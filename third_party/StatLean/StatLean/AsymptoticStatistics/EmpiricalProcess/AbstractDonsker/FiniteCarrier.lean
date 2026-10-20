module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.BracketingDonsker
public import Mathlib

@[expose] public section

/-!
# Finite Gaussian carriers and carrier-agnostic abstract Donsker limits

This file removes the infinite-dimensional-carrier restriction from the
abstract bracketing-Donsker headline. In finite dimension (including rank zero)
the Brownian bridge is the pushforward of the standard Gaussian on `gpH` by the
bounded linear path map. The predicate records an arbitrary bridge law, treating
finite- and infinite-dimensional carriers uniformly.

Reference: van der Vaart, *Asymptotic Statistics*, Theorem 19.5 (book p.270).
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter Topology ProbabilityTheory BoundedContinuousFunction
open scoped ENNReal NNReal RealInnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Carrier-agnostic literal Donsker property.** There is a tight
`P`-Brownian-bridge law `ν` on `ℓ∞(F)`, and for every iid `P` sample the full
bounded empirical-process path exists and converges weakly in outer expectation
to that same law.

The existential witness `hmem` records the boundedness needed to regard the
empirical process as an element of `LinfF F`. There is no finite- or
infinite-dimensional carrier clause in this definition. -/
def IsPDonskerWithBridge (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  ∃ ν : Measure (LinfF F), IsPBrownianBridge F P ν ∧
    ∀ {Ξ : Type} [_inst : MeasurableSpace Ξ] (μ : Measure Ξ)
      [_inst2 : IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω),
      (∀ i, Measurable (X i)) →
      ProbabilityTheory.iIndepFun X μ →
      (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
      μ.map (X 0) = P →
      ∃ hmem : ∀ n ξ, Memℓp
          (fun f : ↥F => empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (f : Ω → ℝ)) ∞,
        WeakConvergesOuter (fun _ => μ)
          (fun n ξ => empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ)) ν

/-! ## Finite-carrier Gaussian construction -/

/-- **Uniform bound for the centred embedding.** A square-integrable envelope
bounds `gpEmbed f` uniformly over `f ∈ F`. This is the norm bound that makes
the finite-dimensional Gaussian path an element of `LinfF F`. -/
theorem gpEmbed_uniform_bound
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ↥F,
      ‖gpEmbed ⟨G, hG_env, hG⟩ hF_meas f‖ ≤ C := by
  refine ⟨2 * ‖hG.toLp G‖, by positivity, fun f => ?_⟩
  have hf : MemLp (f : Ω → ℝ) 2 P :=
    memLp_of_mem_F hG_env hG hF_meas f.2
  have hf_norm : ‖hf.toLp (f : Ω → ℝ)‖ ≤ ‖hG.toLp G‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hf.coeFn_toLp, hG.coeFn_toLp] with x hfx hGx
    rw [hfx, hGx, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hG_env (f : Ω → ℝ) f.2 x).trans (le_abs_self _)
  have hf_int : Integrable (f : Ω → ℝ) P := hf.integrable (by norm_num)
  have hmean : ‖∫ x, (f : Ω → ℝ) x ∂P‖ ≤ ‖hG.toLp G‖ := by
    calc
      ‖∫ x, (f : Ω → ℝ) x ∂P‖
          ≤ ∫ x, ‖(f : Ω → ℝ) x‖ ∂P := norm_integral_le_integral_norm _
      _ = (eLpNorm (f : Ω → ℝ) 1 P).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm,
          integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]
      _ ≤ (eLpNorm (f : Ω → ℝ) 2 P).toReal :=
        ENNReal.toReal_mono hf.eLpNorm_ne_top
          (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hf.aestronglyMeasurable)
      _ = ‖hf.toLp (f : Ω → ℝ)‖ := (Lp.norm_toLp _ _).symm
      _ ≤ ‖hG.toLp G‖ := hf_norm
  rw [Submodule.coe_norm, coe_gpEmbed, centredLp]
  have hc : MemLp (fun _ : Ω => ∫ x, (f : Ω → ℝ) x ∂P) 2 P := memLp_const _
  have hc_norm : ‖hc.toLp (fun _ : Ω => ∫ x, (f : Ω → ℝ) x ∂P)‖
      = ‖∫ x, (f : Ω → ℝ) x ∂P‖ := by
    rw [Lp.norm_toLp,
      eLpNorm_const' (∫ x, (f : Ω → ℝ) x ∂P) (by norm_num) (by norm_num)]
    simp
  rw [show (memLp_centred ⟨G, hG_env, hG⟩ hF_meas f.2).toLp
      (fun x => (f : Ω → ℝ) x - ∫ y, (f : Ω → ℝ) y ∂P)
      = hf.toLp (f : Ω → ℝ) - hc.toLp _ from by
        exact MemLp.toLp_sub hf hc]
  calc
    ‖hf.toLp (f : Ω → ℝ) - hc.toLp _‖
        ≤ ‖hf.toLp (f : Ω → ℝ)‖ + ‖hc.toLp _‖ := norm_sub_le _ _
    _ ≤ ‖hG.toLp G‖ + ‖∫ x, (f : Ω → ℝ) x ∂P‖ := by
      exact add_le_add hf_norm hc_norm.le
    _ ≤ 2 * ‖hG.toLp G‖ := by linarith

/-- The finite-carrier path map sends `h ∈ gpH` to the bounded function
`f ↦ ⟨gpEmbed f, h⟩`. Its construction uses `gpEmbed_uniform_bound`.

This definition is valid at rank zero: the unique input is sent to the zero
path. -/
noncomputable def finiteGpPathCLM
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f) :
    ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) →L[ℝ] LinfF F := by
  let hex := gpEmbed_uniform_bound hG_env hG hF_meas
  let C := hex.choose
  have hC : 0 ≤ C := hex.choose_spec.1
  have hbound : ∀ f : ↥F, ‖gpEmbed ⟨G, hG_env, hG⟩ hF_meas f‖ ≤ C :=
    hex.choose_spec.2
  let L : ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) →ₗ[ℝ] LinfF F :=
    { toFun := fun h => ⟨fun f => ⟪gpEmbed ⟨G, hG_env, hG⟩ hF_meas f, h⟫,
          memℓp_infty ⟨C * ‖h‖, by
            rintro _ ⟨f, rfl⟩
            change |⟪gpEmbed ⟨G, hG_env, hG⟩ hF_meas f, h⟫| ≤ C * ‖h‖
            exact (abs_real_inner_le_norm _ _).trans
              (mul_le_mul_of_nonneg_right (hbound f) (norm_nonneg h))⟩⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext f
        change ⟪gpEmbed ⟨G, hG_env, hG⟩ hF_meas f, x + y⟫ =
          ⟪gpEmbed ⟨G, hG_env, hG⟩ hF_meas f, x⟫ +
            ⟪gpEmbed ⟨G, hG_env, hG⟩ hF_meas f, y⟫
        exact inner_add_right _ _ _
      map_smul' := by
        intro c x
        apply lp.ext
        funext f
        change ⟪gpEmbed ⟨G, hG_env, hG⟩ hF_meas f, c • x⟫ =
          c • ⟪gpEmbed ⟨G, hG_env, hG⟩ hF_meas f, x⟫
        simpa [smul_eq_mul] using
          (real_inner_smul_right (gpEmbed ⟨G, hG_env, hG⟩ hF_meas f) x c) }
  exact LinearMap.mkContinuous L C (fun h => by
    apply lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg h))
    intro f
    change ‖⟪gpEmbed ⟨G, hG_env, hG⟩ hF_meas f, h⟫‖ ≤ C * ‖h‖
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hbound f) (norm_nonneg h)))

/-- Coordinate formula for `finiteGpPathCLM`, used to identify covariance and
Gaussian marginals of finite projections. -/
theorem finiteGpPathCLM_apply
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (h : ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)) (f : ↥F) :
    finiteGpPathCLM hG_env hG hF_meas h f =
      ⟪gpEmbed ⟨G, hG_env, hG⟩ hF_meas f, h⟫ := by
  rw [finiteGpPathCLM]
  rfl

/-- The finite-dimensional `P`-Brownian-bridge candidate: push the standard
Gaussian on the centred carrier `gpH` through `finiteGpPathCLM`.

At rank zero `stdGaussian` is the point mass at zero, hence this is the point
mass at the zero path. -/
noncomputable def finiteGaussianPBridge
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    [FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)] :
    Measure (LinfF F) := by
  letI : MeasurableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) := borel _
  letI : BorelSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) := ⟨rfl⟩
  exact (stdGaussian ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)).map
    (finiteGpPathCLM hG_env hG hF_meas)

/-- The finite-carrier Gaussian candidate is a `P`-Brownian bridge. The
statement deliberately includes the rank-zero case through the ordinary
`FiniteDimensional` instance, with no positive-rank premise. -/
theorem isPBrownianBridge_finiteGaussianPBridge
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    [FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)] :
    IsPBrownianBridge F P (finiteGaussianPBridge hG_env hG hF_meas) := by
  classical
  have hclosed : IsClosed
      (gpH ⟨G, hG_env, hG⟩ hF_meas : Set (Lp ℝ 2 P)) := by
    rw [gpH]
    exact Submodule.isClosed_topologicalClosure _
  letI hcomplete : CompleteSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) :=
    hclosed.completeSpace_coe
  letI hsecond : SecondCountableTopology ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) :=
    inferInstance
  letI hmeas : MeasurableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) := borel _
  letI hborel : BorelSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) := ⟨rfl⟩
  letI hstdprob : IsProbabilityMeasure
      (stdGaussian ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)) :=
    @ProbabilityTheory.isProbabilityMeasure_stdGaussian _ _ _ _ hmeas hborel
  letI hstdgauss : ProbabilityTheory.IsGaussian
      (stdGaussian ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)) :=
    @ProbabilityTheory.isGaussian_stdGaussian _ _ _ _ hmeas hborel
  have hT_meas : Measurable (finiteGpPathCLM hG_env hG hF_meas) :=
    (finiteGpPathCLM hG_env hG hF_meas).continuous.measurable
  have hprob : IsProbabilityMeasure (finiteGaussianPBridge hG_env hG hF_meas) := by
    rw [finiteGaussianPBridge]
    exact Measure.isProbabilityMeasure_map hT_meas.aemeasurable
  have hmean : ∀ f : ↥F,
      ∫ z : LinfF F, z f ∂(finiteGaussianPBridge hG_env hG hF_meas) = 0 := by
    intro f
    rw [finiteGaussianPBridge, integral_map hT_meas.aemeasurable
      (continuous_linfF_eval f).aestronglyMeasurable]
    change ∫ h : ↥(gpH ⟨G, hG_env, hG⟩ hF_meas),
      (innerSL ℝ (gpEmbed ⟨G, hG_env, hG⟩ hF_meas f)) h
      ∂(stdGaussian ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)) = 0
    exact @integral_strongDual_stdGaussian _ _ _ _ hmeas hborel _
  have hcov : ∀ f g : ↥F,
      ∫ z : LinfF F, (z f) * (z g) ∂(finiteGaussianPBridge hG_env hG hF_meas)
        = (∫ x, (f : Ω → ℝ) x * (g : Ω → ℝ) x ∂P)
          - (∫ x, (f : Ω → ℝ) x ∂P) * (∫ x, (g : Ω → ℝ) x ∂P) := by
    intro f g
    rw [finiteGaussianPBridge]
    change ∫ z : LinfF F, ((fun w : LinfF F => w f) * (fun w : LinfF F => w g)) z
      ∂((stdGaussian ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)).map
        (finiteGpPathCLM hG_env hG hF_meas)) = _
    rw [integral_map hT_meas.aemeasurable
      (((continuous_linfF_eval f).mul (continuous_linfF_eval g)).aestronglyMeasurable)]
    change ∫ h : ↥(gpH ⟨G, hG_env, hG⟩ hF_meas),
      ⟪gpEmbed ⟨G, hG_env, hG⟩ hF_meas f, h⟫ *
        ⟪gpEmbed ⟨G, hG_env, hG⟩ hF_meas g, h⟫
          ∂(stdGaussian ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)) = _
    have hmem : MemLp id 2
        (stdGaussian ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)) :=
      @ProbabilityTheory.IsGaussian.memLp_two_id _ _ _ hmeas hborel _ hstdgauss
        hcomplete hsecond
    have hstd := @covarianceBilin_apply
      ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) _ _ hmeas hborel
      (stdGaussian ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)) hcomplete _ hmem
      (gpEmbed ⟨G, hG_env, hG⟩ hF_meas f)
      (gpEmbed ⟨G, hG_env, hG⟩ hF_meas g)
    have hcovstd := @covarianceBilin_stdGaussian
      ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) _ _ _ hmeas hborel
    have hid : ∫ x : ↥(gpH ⟨G, hG_env, hG⟩ hF_meas), id x
        ∂(stdGaussian ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)) = 0 := by
      simpa using (@integral_id_stdGaussian
        ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) _ _ _ hmeas hborel)
    rw [hcovstd, hid] at hstd
    simp only [sub_zero] at hstd
    change ⟪gpEmbed ⟨G, hG_env, hG⟩ hF_meas f,
        gpEmbed ⟨G, hG_env, hG⟩ hF_meas g⟫ = _ at hstd
    rw [← hstd, Submodule.coe_inner, coe_gpEmbed, coe_gpEmbed,
      inner_centredLp ⟨G, hG_env, hG⟩ hF_meas]
  have hfdd : ∀ (m : ℕ) (φ : Fin m → ↥F),
      ProbabilityTheory.HasGaussianLaw
        (fun z : LinfF F => (fun k => z (φ k)))
        (finiteGaussianPBridge hG_env hG hF_meas) := by
    intro m φ
    let Q : ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) →L[ℝ] (Fin m → ℝ) :=
      ContinuousLinearMap.pi (fun k => innerSL ℝ (gpEmbed ⟨G, hG_env, hG⟩ hF_meas (φ k)))
    have hR_meas : Measurable (fun z : LinfF F => (fun k => z (φ k))) :=
      measurable_pi_iff.mpr (fun k => (continuous_linfF_eval (φ k)).measurable)
    refine ⟨?_⟩
    rw [finiteGaussianPBridge,
      Measure.map_map hR_meas hT_meas]
    have hcomp : (fun z : LinfF F => (fun k => z (φ k))) ∘
        (finiteGpPathCLM hG_env hG hF_meas) = Q := by
      funext h k
      exact finiteGpPathCLM_apply hG_env hG hF_meas h (φ k)
    rw [hcomp]
    exact ProbabilityTheory.isGaussian_map_of_measurable Q.continuous.measurable
  have htight : MeasureTheory.IsTightMeasureSet
      ({finiteGaussianPBridge hG_env hG hF_meas} : Set (Measure (LinfF F))) := by
    have hsrc : MeasureTheory.IsTightMeasureSet
        ({stdGaussian ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)} :
          Set (Measure ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))) :=
      MeasureTheory.isTightMeasureSet_singleton
    have himg := hsrc.map (finiteGpPathCLM hG_env hG hF_meas).continuous
    simpa [finiteGaussianPBridge] using himg
  have huc : ∀ᵐ z ∂(finiteGaussianPBridge hG_env hG hF_meas),
      ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f g : ↥F,
        distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ → |z f - z g| < ε := by
    rw [finiteGaussianPBridge, ae_map_iff hT_meas.aemeasurable
      pBridge_ucPaths_measurableSet]
    filter_upwards [] with h
    intro ε hε
    refine ⟨ε / (‖h‖ + 1), by positivity, fun f g hfg => ?_⟩
    rw [finiteGpPathCLM_apply, finiteGpPathCLM_apply, ← inner_sub_left]
    calc
      |⟪gpEmbed ⟨G, hG_env, hG⟩ hF_meas f -
          gpEmbed ⟨G, hG_env, hG⟩ hF_meas g, h⟫|
          ≤ ‖gpEmbed ⟨G, hG_env, hG⟩ hF_meas f -
              gpEmbed ⟨G, hG_env, hG⟩ hF_meas g‖ * ‖h‖ :=
            abs_real_inner_le_norm _ _
      _ ≤ distL2 P (f : Ω → ℝ) (g : Ω → ℝ) * ‖h‖ :=
        mul_le_mul_of_nonneg_right
          (norm_gpEmbed_sub_le ⟨G, hG_env, hG⟩ hF_meas f g) (norm_nonneg h)
      _ ≤ (ε / (‖h‖ + 1)) * ‖h‖ :=
        mul_le_mul_of_nonneg_right hfg.le (norm_nonneg h)
      _ < ε := by
        calc
          (ε / (‖h‖ + 1)) * ‖h‖ < (ε / (‖h‖ + 1)) * (‖h‖ + 1) := by
            exact mul_lt_mul_of_pos_left (by linarith) (by positivity)
          _ = ε := by field_simp
  exact ⟨hprob, hcov, hmean, hfdd, htight, huc⟩

/-- Explicit rank-zero check: the same standard-Gaussian pushforward is a
Brownian bridge when the centred carrier has no nonzero coordinates. -/
private theorem exists_pBrownianBridge_finrank_zero
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    [FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)]
    (_hzero : Module.finrank ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) = 0) :
    ∃ ν : Measure (LinfF F), IsPBrownianBridge F P ν :=
  ⟨finiteGaussianPBridge hG_env hG hF_meas,
    isPBrownianBridge_finiteGaussianPBridge hG_env hG hF_meas⟩

/-- The point mass at the zero path is the `P`-Brownian bridge indexed by the
empty class. -/
theorem emptyClass_pBrownianBridge (P : Measure Ω) [IsProbabilityMeasure P] :
    IsPBrownianBridge (∅ : Set (Ω → ℝ)) P (Measure.dirac 0) := by
  refine
    { isProbabilityMeasure := inferInstance
      cov := ?_
      mean := ?_
      isGaussian_fdd := ?_
      tight := ?_
      ucPaths := ?_ }
  · intro f
    exact (Set.notMem_empty (f : Ω → ℝ) f.2).elim
  · intro f
    exact (Set.notMem_empty (f : Ω → ℝ) f.2).elim
  · intro m φ
    refine ⟨?_⟩
    simp only [Measure.map_dirac]
    infer_instance
  · rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε _
    refine ⟨{0}, isCompact_singleton, ?_⟩
    intro μ hμ
    rw [Set.mem_singleton_iff.mp hμ]
    simp
  · filter_upwards [ae_eq_dirac (fun z : LinfF (∅ : Set (Ω → ℝ)) => z)] with z hz
    change z = 0 at hz
    subst z
    intro ε hε
    exact ⟨1, zero_lt_one, fun f => (Set.notMem_empty (f : Ω → ℝ) f.2).elim⟩

/-- A `P`-Brownian-bridge law exists for every function class. The empty class
has the degenerate zero bridge. Otherwise the proof branches on
`FiniteDimensional ℝ gpH`: the finite branch uses `finiteGaussianPBridge`,
including rank zero, while the infinite branch uses the separable
`gpBridgeMeasure` construction. -/
theorem exists_pBrownianBridge_all
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) :
    ∃ ν : Measure (LinfF F), IsPBrownianBridge F P ν := by
  classical
  by_cases hF_ne : F.Nonempty
  swap
  · have hF_empty : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hF_ne
    subst F
    exact ⟨Measure.dirac 0, emptyClass_pBrownianBridge P⟩
  by_cases hfin : FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas)
  · letI : FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas) := hfin
    exact ⟨finiteGaussianPBridge hG_env hG hF_meas,
      isPBrownianBridge_finiteGaussianPBridge hG_env hG hF_meas⟩
  · exact exists_pBrownianBridge hG_env hG hF_meas hfin
      (separableSpace_gpH_of_entropyIntegral hF_ent ⟨G, hG_env, hG⟩ hF_meas)
      hF_ent hF_ne

/-! ## Finite projections of arbitrary bridge laws -/

private theorem pBrownianBridge_readout_isGaussian_aux
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (ν : Measure (LinfF F)) (hν : IsPBrownianBridge F P ν) (m : ℕ) :
    ProbabilityTheory.IsGaussian
      (ν.map (fun z : LinfF F => (WithLp.toLp 2
        (fun i => z ((netEnum hG_env hG hF_meas hF_ent m).symm i).1) :
        EuclideanSpace ℝ (Fin (Fintype.card
          ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))))))) := by
  classical
  set k := Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))
  set ψ : Fin k → ↥F := fun i => ((netEnum hG_env hG hF_meas hF_ent m).symm i).1
  have hpi : ProbabilityTheory.HasGaussianLaw
      (fun z : LinfF F => (fun j => z (ψ j))) ν := hν.isGaussian_fdd k ψ
  set L := (EuclideanSpace.equiv (Fin k) ℝ).symm
  have hcomp :
      (fun z : LinfF F => (WithLp.toLp 2 (fun j => z (ψ j)) :
        EuclideanSpace ℝ (Fin k))) =
        L ∘ (fun z : LinfF F => (fun j => z (ψ j))) := rfl
  haveI : ProbabilityTheory.IsGaussian
      (ν.map (fun z : LinfF F => (fun j => z (ψ j)))) := hpi.isGaussian_map
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable
    (L.continuous.measurable.aemeasurable) hpi.aemeasurable]
  exact ProbabilityTheory.isGaussian_map_equiv L

private theorem pBrownianBridge_readout_mean_aux
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (ν : Measure (LinfF F)) (hν : IsPBrownianBridge F P ν) (m : ℕ) :
    ∫ x, id x
        ∂(ν.map (fun z : LinfF F => (WithLp.toLp 2
          (fun i => z ((netEnum hG_env hG hF_meas hF_ent m).symm i).1) :
          EuclideanSpace ℝ (Fin (Fintype.card
            ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)))))))
      = ∫ x, id x
        ∂(ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ
          (Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)))))
          (marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m))) := by
  classical
  set k := Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))
  set ψ : Fin k → ↥F := fun i => ((netEnum hG_env hG hF_meas hF_ent m).symm i).1
  set R : LinfF F → EuclideanSpace ℝ (Fin k) :=
    fun z => (WithLp.toLp 2 (fun i => z (ψ i)) : EuclideanSpace ℝ (Fin k))
  rw [ProbabilityTheory.integral_id_multivariateGaussian']
  haveI : ProbabilityTheory.IsGaussian (ν.map R) :=
    pBrownianBridge_readout_isGaussian_aux hG_env hG hF_meas hF_ent ν hν m
  have hcont_eval : ∀ i : ↥F, Continuous (fun z : LinfF F => z i) := by
    intro i
    apply (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
    intro z w
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have hsub : (z : ↥F → ℝ) i - (w : ↥F → ℝ) i = (z - w) i := by
      rw [lp.coeFn_sub z w]
      rfl
    rw [show ‖(z : ↥F → ℝ) i - (w : ↥F → ℝ) i‖ = ‖(z - w) i‖ by rw [hsub]]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w) i
  have hR_meas : Measurable R :=
    ((PiLp.continuous_toLp 2 _).comp
      (continuous_pi (fun i => hcont_eval (ψ i)))).measurable
  have hR_int : Integrable R ν :=
    (integrable_map_measure aestronglyMeasurable_id hR_meas.aemeasurable).mp
      ProbabilityTheory.IsGaussian.integrable_id
  rw [integral_map hR_meas.aemeasurable aestronglyMeasurable_id]
  simp only [id_eq]
  refine PiLp.ext (fun i => ?_)
  have hproj : (∫ z, R z ∂ν).ofLp i = ∫ z, (R z).ofLp i ∂ν := by
    have h := ContinuousLinearMap.integral_comp_comm
      (EuclideanSpace.proj (𝕜 := ℝ) i) hR_int
    simpa only [EuclideanSpace.coe_proj] using h.symm
  rw [show (0 : EuclideanSpace ℝ (Fin k)).ofLp i = 0 from rfl, hproj]
  change (∫ z : LinfF F, z (ψ i) ∂ν) = 0
  exact hν.mean (ψ i)

private theorem pBrownianBridge_readout_covarianceBilin_aux
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (ν : Measure (LinfF F)) (hν : IsPBrownianBridge F P ν) (m : ℕ)
    (hS_psd : (marginalCovMatrix P
      (netPhi hG_env hG hF_meas hF_ent m)).PosSemidef) :
    ProbabilityTheory.covarianceBilin
        (ν.map (fun z : LinfF F => (WithLp.toLp 2
          (fun i => z ((netEnum hG_env hG hF_meas hF_ent m).symm i).1) :
          EuclideanSpace ℝ (Fin (Fintype.card
            ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)))))))
      = ProbabilityTheory.covarianceBilin
          (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ
            (Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)))))
            (marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m))) := by
  classical
  set k := Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))
  set ψ : Fin k → ↥F := fun i => ((netEnum hG_env hG hF_meas hF_ent m).symm i).1
  set S := marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m)
  set R : LinfF F → EuclideanSpace ℝ (Fin k) :=
    fun z => (WithLp.toLp 2 (fun i => z (ψ i)) : EuclideanSpace ℝ (Fin k))
  letI : IsProbabilityMeasure ν := hν.isProbabilityMeasure
  have hcont_eval : ∀ i : ↥F, Continuous (fun z : LinfF F => z i) := by
    intro i
    apply (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
    intro z w
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have hsub : (z : ↥F → ℝ) i - (w : ↥F → ℝ) i = (z - w) i := by
      rw [lp.coeFn_sub z w]
      rfl
    rw [show ‖(z : ↥F → ℝ) i - (w : ↥F → ℝ) i‖ = ‖(z - w) i‖ by rw [hsub]]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w) i
  have hR_meas : Measurable R :=
    ((PiLp.continuous_toLp 2 _).comp
      (continuous_pi (fun i => hcont_eval (ψ i)))).measurable
  haveI : ProbabilityTheory.IsGaussian (ν.map R) :=
    pBrownianBridge_readout_isGaussian_aux hG_env hG hF_meas hF_ent ν hν m
  have hMemLp_map : MemLp id 2 (ν.map R) :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  have hMemLp_R : MemLp R 2 ν :=
    (memLp_map_measure_iff aestronglyMeasurable_id hR_meas.aemeasurable).mp hMemLp_map
  have hMemLp_coord : ∀ i : Fin k, MemLp (fun z : LinfF F => z (ψ i)) 2 ν := by
    intro i
    have heq : (fun z : LinfF F => z (ψ i)) =
        (EuclideanSpace.proj (𝕜 := ℝ) i) ∘ R := by
      funext z
      rw [EuclideanSpace.coe_proj]
      rfl
    rw [heq]
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitz.comp_memLp (map_zero _) hMemLp_R
  have hbasis : ∀ a : Fin k,
      (fun u : EuclideanSpace ℝ (Fin k) =>
        (inner ℝ ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis a) u : ℝ))
        = fun u => u.ofLp a := by
    intro a
    funext u
    rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, PiLp.inner_apply]
    have hpt : ∀ x : Fin k,
        (inner ℝ ((EuclideanSpace.single a (1 : ℝ)).ofLp x) (u.ofLp x) : ℝ)
          = u.ofLp x * (if x = a then (1 : ℝ) else 0) := by
      intro x
      rw [PiLp.single_apply]
      rfl
    simp_rw [hpt]
    simp [Finset.sum_ite_eq']
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply]
  rw [ProbabilityTheory.covarianceBilin_apply_eq_cov
        (μ := ProbabilityTheory.multivariateGaussian 0 S)
        ProbabilityTheory.IsGaussian.memLp_two_id,
    ProbabilityTheory.covarianceBilin_apply_eq_cov (μ := ν.map R) hMemLp_map]
  rw [hbasis i, hbasis j]
  rw [ProbabilityTheory.covariance_eval_multivariateGaussian hS_psd]
  have hcoord_meas : ∀ a : Fin k,
      AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin k) => u.ofLp a) (ν.map R) := by
    intro a
    have h : (fun u : EuclideanSpace ℝ (Fin k) => u.ofLp a) =
        ⇑(EuclideanSpace.proj (𝕜 := ℝ) a) := by
      funext u
      rw [EuclideanSpace.coe_proj]
    rw [h]
    exact (EuclideanSpace.proj (𝕜 := ℝ) a).continuous.measurable.aestronglyMeasurable
  rw [ProbabilityTheory.covariance_map (hcoord_meas i) (hcoord_meas j)
    hR_meas.aemeasurable]
  change cov[fun z : LinfF F => z (ψ i), fun z : LinfF F => z (ψ j); ν] = S i j
  rw [ProbabilityTheory.covariance_eq_sub (hMemLp_coord i) (hMemLp_coord j)]
  simp only [Pi.mul_apply]
  rw [hν.mean (ψ i), hν.mean (ψ j), hν.cov (ψ i) (ψ j)]
  simp only [mul_zero, sub_zero]
  simp only [S, marginalCovMatrix, marginalCovEntry, netPhi, ψ]

/-- The finite net-coordinate readout of any `P`-Brownian bridge is the
corresponding centred marginal Gaussian. -/
theorem pBrownianBridge_readout_eq_multivariateGaussian
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (ν : Measure (LinfF F)) (hν : IsPBrownianBridge F P ν) (m : ℕ) :
    ν.map (fun z : LinfF F => (WithLp.toLp 2
          (fun i => z ((netEnum hG_env hG hF_meas hF_ent m).symm i).1) :
          EuclideanSpace ℝ (Fin (Fintype.card
            ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))))))
      = ProbabilityTheory.multivariateGaussian 0
          (marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m)) := by
  classical
  set k := Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))
  set ψ : Fin k → ↥F := fun i => ((netEnum hG_env hG hF_meas hF_ent m).symm i).1
  set S := marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m)
  set Rpi : LinfF F → (Fin k → ℝ) := fun z j => z (ψ j)
  have hS_psd : S.PosSemidef :=
    marginalCovMatrix_netPhi_posSemidef hG_env hG hF_meas hF_ent m
  haveI : ProbabilityTheory.IsGaussian
      (ProbabilityTheory.multivariateGaussian 0 S) := inferInstance
  haveI : ProbabilityTheory.IsGaussian
      (ν.map (fun z : LinfF F =>
        (WithLp.toLp 2 (Rpi z) : EuclideanSpace ℝ (Fin k)))) :=
    pBrownianBridge_readout_isGaussian_aux hG_env hG hF_meas hF_ent ν hν m
  refine ProbabilityTheory.IsGaussian.ext ?_ ?_
  · exact pBrownianBridge_readout_mean_aux hG_env hG hF_meas hF_ent ν hν m
  · exact pBrownianBridge_readout_covarianceBilin_aux hG_env hG hF_meas hF_ent
      ν hν m hS_psd

/-- The `netTuple` pushforward of an arbitrary `P`-Brownian bridge agrees with
the reindexed marginal Gaussian. -/
theorem pBrownianBridge_map_netTuple_eq
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (ν : Measure (LinfF F)) (hν : IsPBrownianBridge F P ν) (m : ℕ) :
    ν.map (netTuple hG_env hG hF_meas hF_ent m)
      = (ProbabilityTheory.multivariateGaussian 0
          (marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m))).map
        (netReindex hG_env hG hF_meas hF_ent m) := by
  set mvg := ProbabilityTheory.multivariateGaussian 0
    (marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m))
  have hrecover : ∀ ρ : Measure
      (↥(Set.range (netRep hG_env hG hF_meas hF_ent m)) → ℝ),
      (ρ.map (netReindexInv hG_env hG hF_meas hF_ent m)).map
        (netReindex hG_env hG hF_meas hF_ent m) = ρ := by
    intro ρ
    rw [Measure.map_map (measurable_netReindex hG_env hG hF_meas hF_ent m)
      (measurable_netReindexInv hG_env hG hF_meas hF_ent m),
      netReindex_netReindexInv, Measure.map_id]
  rw [← hrecover (ν.map (netTuple hG_env hG hF_meas hF_ent m)),
    ← hrecover (mvg.map (netReindex hG_env hG hF_meas hF_ent m))]
  congr 1
  rw [Measure.map_map (measurable_netReindexInv hG_env hG hF_meas hF_ent m)
      (measurable_netTuple hG_env hG hF_meas hF_ent m),
    Measure.map_map (measurable_netReindexInv hG_env hG hF_meas hF_ent m)
      (measurable_netReindex hG_env hG hF_meas hF_ent m),
    netReindexInv_netReindex, Measure.map_id]
  have hcomp : (netReindexInv hG_env hG hF_meas hF_ent m) ∘
      (netTuple hG_env hG hF_meas hF_ent m) =
      fun z : LinfF F => (WithLp.toLp 2
        (fun i => z ((netEnum hG_env hG hF_meas hF_ent m).symm i).1) :
        EuclideanSpace ℝ (Fin (Fintype.card
          ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))))) := by
    funext z
    rfl
  rw [hcomp]
  exact pBrownianBridge_readout_eq_multivariateGaussian
    hG_env hG hF_meas hF_ent ν hν m

private theorem weakConverges_netTuple_withBridge_aux
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (ν : Measure (LinfF F)) (hν : IsPBrownianBridge F P ν)
    (h_clt : IsMarginalCLT F P) (m : ℕ)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    WeakConverges
      (fun n => μ.map (fun ξ => netTuple hG_env hG hF_meas hF_ent m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ)))))
      (ν.map (netTuple hG_env hG hF_meas hF_ent m)) := by
  classical
  set φ := netPhi hG_env hG hF_meas hF_ent m
  have hφ_mem : ∀ i, φ i ∈ F := netPhi_mem hG_env hG hF_meas hF_ent m
  set stdVec : ℕ → Ξ → EuclideanSpace ℝ (Fin _) := fun n ξ =>
    (Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n, tupleVec φ (X i ξ)
      - n • ∫ ζ, tupleVec φ (X 0 ζ) ∂μ)
  obtain ⟨Y, hY, hTID⟩ :=
    h_clt.2 μ X hX_meas hX_indep hX_id hX_law φ hφ_mem
  have hWC_euclid : WeakConverges (fun n => μ.map (stdVec n))
      (ProbabilityTheory.multivariateGaussian 0 (marginalCovMatrix P φ)) := by
    have hlim_eq :
        (⟨(ProbabilityTheory.multivariateGaussian 0
              (marginalCovMatrix P φ)).map Y,
            Measure.isProbabilityMeasure_map hTID.aemeasurable_limit⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin _))) =
        ⟨ProbabilityTheory.multivariateGaussian 0 (marginalCovMatrix P φ),
          inferInstance⟩ := Subtype.ext hY.map_eq
    intro g
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (hlim_eq ▸ hTID.tendsto)) g
  have hWC_net := hWC_euclid.map
    (continuous_netReindex hG_env hG hF_meas hF_ent m)
    (measurable_netReindex hG_env hG hF_meas hF_ent m)
  rw [← pBrownianBridge_map_netTuple_eq hG_env hG hF_meas hF_ent ν hν m] at hWC_net
  have hseq : ∀ n : ℕ,
      (μ.map (stdVec n)).map (netReindex hG_env hG hF_meas hF_ent m) =
        μ.map (fun ξ => netTuple hG_env hG hF_meas hF_ent m
          (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
            (memℓp_empiricalProcess
              ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
              (fun i : Fin n => X i.val ξ)))) := by
    intro n
    rw [Measure.map_map (measurable_netReindex hG_env hG hF_meas hF_ent m)
      (by
        have htv : Measurable (tupleVec φ) := by
          have hpi : Measurable (fun ω => (fun i => φ i ω) : Ω → (Fin _ → ℝ)) :=
            measurable_pi_iff.mpr (fun i => hF_meas (φ i) (hφ_mem i))
          exact (EuclideanSpace.equiv _ ℝ).symm.continuous.measurable.comp hpi
        exact Measurable.const_smul
          ((Finset.measurable_sum _ (fun i _ => htv.comp (hX_meas i))).sub
            measurable_const) ((Real.sqrt (n : ℝ))⁻¹))]
    refine Measure.map_congr (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Function.comp_apply]
    exact (netTuple_empirical_eq_reindex_std hG_env hG hF_meas hF_ent h_clt m μ X
      hX_meas hX_id hX_law n ξ).symm
  rw [funext hseq] at hWC_net
  exact hWC_net

private theorem weakConverges_findim_proj_withBridge_aux
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (ν : Measure (LinfF F)) (hν : IsPBrownianBridge F P ν)
    (h_clt : IsMarginalCLT F P) (m : ℕ)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    WeakConverges
      (fun n => μ.map (fun ξ => finiteNetProj hG_env hG hF_meas hF_ent m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ)))))
      (ν.map (finiteNetProj hG_env hG hF_meas hF_ent m)) := by
  have hμmap : ∀ n : ℕ,
      μ.map (fun ξ => finiteNetProj hG_env hG hF_meas hF_ent m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ)))) =
        (μ.map (fun ξ => netTuple hG_env hG hF_meas hF_ent m
          (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
            (memℓp_empiricalProcess
              ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
              (fun i : Fin n => X i.val ξ))))).map
          (netRecon hG_env hG hF_meas hF_ent m) := by
    intro n
    have hcomp : (fun ξ => finiteNetProj hG_env hG hF_meas hF_ent m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ)))) =
        (netRecon hG_env hG hF_meas hF_ent m) ∘
          (fun ξ => netTuple hG_env hG hF_meas hF_ent m
            (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
              (memℓp_empiricalProcess
                ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
                (fun i : Fin n => X i.val ξ)))) := by
      funext ξ
      rw [Function.comp_apply, finiteNetProj_eq_comp, Function.comp_apply]
    rw [hcomp, ← Measure.map_map
      (continuous_netRecon hG_env hG hF_meas hF_ent m).measurable
      (measurable_projectedEmpirical' hG_env hG hF_meas hF_ent m X hX_meas n)]
  have hνmap : ν.map (finiteNetProj hG_env hG hF_meas hF_ent m) =
      (ν.map (netTuple hG_env hG hF_meas hF_ent m)).map
        (netRecon hG_env hG hF_meas hF_ent m) := by
    rw [Measure.map_map
      (continuous_netRecon hG_env hG hF_meas hF_ent m).measurable
      (measurable_netTuple hG_env hG hF_meas hF_ent m), finiteNetProj_eq_comp]
  rw [funext hμmap, hνmap]
  exact (weakConverges_netTuple_withBridge_aux hG_env hG hF_meas hF_ent ν hν
    h_clt m μ X hX_meas hX_indep hX_id hX_law).map
    (continuous_netRecon hG_env hG hF_meas hF_ent m)
    (continuous_netRecon hG_env hG hF_meas hF_ent m).measurable

private theorem weakConvergesOuter_findim_proj_withBridge_aux
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (ν : Measure (LinfF F)) (hν : IsPBrownianBridge F P ν)
    (h_clt : IsMarginalCLT F P) (m : ℕ)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    WeakConvergesOuter (fun _ => μ)
      (fun n ξ => finiteNetProj hG_env hG hF_meas hF_ent m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ))))
      (ν.map (finiteNetProj hG_env hG hF_meas hF_ent m)) := by
  rw [weakConvergesOuter_of_measurable
    (fun n => measurable_projectedEmpirical hG_env hG hF_meas hF_ent m X hX_meas n)]
  exact weakConverges_findim_proj_withBridge_aux hG_env hG hF_meas hF_ent ν hν
    h_clt m μ X hX_meas hX_indep hX_id hX_law

private theorem limit_proj_error_withBridge_aux
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (ν : Measure (LinfF F)) (hν : IsPBrownianBridge F P ν)
    (f : LinfF F →ᵇ ℝ) :
    Tendsto
      (fun m => ∫ z, |f (finiteNetProj hG_env hG hF_meas hF_ent m z) - f z| ∂ν)
      atTop (𝓝 0) := by
  letI : IsProbabilityMeasure ν := hν.isProbabilityMeasure
  set Φ : ℕ → LinfF F → ℝ :=
    fun m z => |f (finiteNetProj hG_env hG hF_meas hF_ent m z) - f z|
  have hzero : (0 : ℝ) = ∫ _ : LinfF F, (0 : ℝ) ∂ν := by simp
  rw [hzero]
  apply tendsto_integral_of_dominated_convergence (fun _ => 2 * ‖f‖)
  · intro m
    have h1 : Measurable
        (fun z : LinfF F => f (finiteNetProj hG_env hG hF_meas hF_ent m z)) :=
      f.continuous.measurable.comp
        (measurable_finiteNetProj hG_env hG hF_meas hF_ent m)
    exact ((h1.sub f.continuous.measurable).abs).aestronglyMeasurable
  · exact integrable_const _
  · intro m
    refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    calc
      |f (finiteNetProj hG_env hG hF_meas hF_ent m z) - f z|
          ≤ |f (finiteNetProj hG_env hG hF_meas hF_ent m z)| + |f z| := abs_sub _ _
      _ ≤ ‖f‖ + ‖f‖ := by
        apply add_le_add <;> rw [← Real.norm_eq_abs] <;> exact f.norm_coe_le_norm _
      _ = 2 * ‖f‖ := by ring
  · filter_upwards [hν.ucPaths] with z hz
    have htproj : Tendsto
        (fun m => finiteNetProj hG_env hG hF_meas hF_ent m z) atTop (𝓝 z) :=
      tendsto_finiteNetProj_of_ucPath hG_env hG hF_meas hF_ent z hz
    have hf_tendsto : Tendsto
        (fun m => f (finiteNetProj hG_env hG hF_meas hF_ent m z)) atTop (𝓝 (f z)) :=
      (f.continuous.tendsto z).comp htproj
    have hsub : Tendsto
        (fun m => f (finiteNetProj hG_env hG hF_meas hF_ent m z) - f z)
        atTop (𝓝 (0 : ℝ)) := by
      simpa using hf_tendsto.sub (tendsto_const_nhds (x := f z))
    simpa [Φ] using! (continuous_abs.tendsto (0 : ℝ)).comp hsub

private theorem weakConvergesOuter_withBridge_readout_aux
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (ν : Measure (LinfF F)) (hν : IsPBrownianBridge F P ν)
    (h_clt : IsMarginalCLT F P) (h_eq : IsAsymptoticallyEquicontinuous F P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) (f : LinfF F →ᵇ ℝ)
    (hf_lip : ∃ K, LipschitzWith K f) :
    Tendsto (fun n =>
        (outerExpectation μ (fun ξ => ENNReal.ofReal
          (f (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
              (memℓp_empiricalProcess
                ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
                (fun i : Fin n => X i.val ξ))) + ‖f‖))).toReal
          - ‖f‖ * (μ Set.univ).toReal) atTop (𝓝 (∫ y, f y ∂ν)) := by
  set 𝔾 : ℕ → Ξ → LinfF F := fun n ξ =>
    empiricalProcessLinf (fun i : Fin n => X i.val ξ)
      (memℓp_empiricalProcess
        ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
        (fun i : Fin n => X i.val ξ))
  set R : ℕ → ℝ := fun n =>
    (outerExpectation μ (fun ξ => ENNReal.ofReal (f (𝔾 n ξ) + ‖f‖))).toReal
      - ‖f‖ * (μ Set.univ).toReal
  set Rproj : ℕ → ℕ → ℝ := fun m n =>
    (outerExpectation μ (fun ξ =>
      ENNReal.ofReal (f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)) + ‖f‖))).toReal
      - ‖f‖ * (μ Set.univ).toReal
  set Lproj : ℕ → ℝ := fun m =>
    ∫ z, f (finiteNetProj hG_env hG hF_meas hF_ent m z) ∂ν
  set L : ℝ := ∫ y, f y ∂ν
  set Dtail : ℕ → ℕ → ℝ := fun m n =>
    (outerExpectation μ (fun ξ => ENNReal.ofReal
      |f (𝔾 n ξ) - f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))|)).toReal
  refine tendsto_outerReadout_of_pieces R Rproj Lproj L Dtail
    ?_middle ?_limtail ?_hdiff ?_Dtail ?_hDbdd
  case _middle =>
    intro m
    have hS2 := weakConvergesOuter_findim_proj_withBridge_aux hG_env hG hF_meas
      hF_ent ν hν h_clt m μ X hX_meas hX_indep hX_id hX_law f
    have hmap : ∫ y, f y ∂(ν.map (finiteNetProj hG_env hG hF_meas hF_ent m)) =
        Lproj m := by
      rw [integral_map
        (measurable_finiteNetProj hG_env hG hF_meas hF_ent m).aemeasurable
        f.continuous.aestronglyMeasurable]
    rw [show Rproj m = fun n =>
      (outerExpectation μ (fun ξ => ENNReal.ofReal
        (f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)) + ‖f‖))).toReal
        - ‖f‖ * (μ Set.univ).toReal from rfl, ← hmap]
    convert hS2 using 2
  case _limtail =>
    have hS4 := limit_proj_error_withBridge_aux hG_env hG hF_meas hF_ent ν hν f
    letI : IsProbabilityMeasure ν := hν.isProbabilityMeasure
    rw [tendsto_iff_dist_tendsto_zero]
    have hbound : ∀ m, dist (Lproj m) L ≤
        ∫ z, |f (finiteNetProj hG_env hG hF_meas hF_ent m z) - f z| ∂ν := by
      intro m
      change dist
        (∫ z, f (finiteNetProj hG_env hG hF_meas hF_ent m z) ∂ν)
        (∫ y, f y ∂ν) ≤ _
      rw [Real.dist_eq]
      have hf_int : Integrable f ν := f.integrable _
      have hfπ_int : Integrable
          (fun z => f (finiteNetProj hG_env hG hF_meas hF_ent m z)) ν :=
        Integrable.of_bound
          (f.continuous.measurable.comp
            (measurable_finiteNetProj hG_env hG hF_meas hF_ent m)).aestronglyMeasurable
          ‖f‖ (Eventually.of_forall (fun z => f.norm_coe_le_norm _))
      rw [← integral_sub hfπ_int hf_int]
      exact abs_integral_le_integral_abs
    exact squeeze_zero (fun m => dist_nonneg) hbound hS4
  case _hdiff =>
    intro m n
    have hbnd := abs_outerReadout_diff_le_readout_abs μ f (𝔾 n)
      (fun ξ => finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))
    change |((outerExpectation μ (fun ξ => ENNReal.ofReal (f (𝔾 n ξ) + ‖f‖))).toReal
      - ‖f‖ * (μ Set.univ).toReal) -
      ((outerExpectation μ (fun ξ => ENNReal.ofReal
        (f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)) + ‖f‖))).toReal
      - ‖f‖ * (μ Set.univ).toReal)| ≤ _
    have hcancel :
        ((outerExpectation μ (fun ξ => ENNReal.ofReal (f (𝔾 n ξ) + ‖f‖))).toReal
          - ‖f‖ * (μ Set.univ).toReal) -
        ((outerExpectation μ (fun ξ => ENNReal.ofReal
          (f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)) + ‖f‖))).toReal
          - ‖f‖ * (μ Set.univ).toReal) =
        (outerExpectation μ (fun ξ => ENNReal.ofReal (f (𝔾 n ξ) + ‖f‖))).toReal -
        (outerExpectation μ (fun ξ => ENNReal.ofReal
          (f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)) + ‖f‖))).toReal := by
      ring
    rw [hcancel]
    exact hbnd
  case _Dtail =>
    have hHP4 := empirical_readout_tail_outer hG_env hG hF_meas hF_ent
      h_eq μ X hX_meas hX_indep hX_id hX_law f hf_lip
    simpa only [Dtail, 𝔾] using hHP4
  case _hDbdd =>
    intro m
    refine Filter.isBoundedUnder_of ⟨2 * ‖f‖, fun n => ?_⟩
    change (outerExpectation μ (fun ξ => ENNReal.ofReal
      |f (𝔾 n ξ) - f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))|)).toReal
      ≤ 2 * ‖f‖
    have hE_le : outerExpectation μ (fun ξ => ENNReal.ofReal
        |f (𝔾 n ξ) - f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))|)
        ≤ ENNReal.ofReal (2 * ‖f‖) := by
      calc
        outerExpectation μ (fun ξ => ENNReal.ofReal
          |f (𝔾 n ξ) - f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))|)
            ≤ outerExpectation μ (fun _ => ENNReal.ofReal (2 * ‖f‖)) := by
              refine outerExpectation_mono (fun ξ => ENNReal.ofReal_le_ofReal ?_)
              have hfX := abs_le.1 (f.norm_coe_le_norm (𝔾 n ξ))
              have hfY := abs_le.1 (f.norm_coe_le_norm
                (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)))
              rw [abs_le]
              constructor <;> [linarith [hfX.1, hfY.2]; linarith [hfX.2, hfY.1]]
        _ = ENNReal.ofReal (2 * ‖f‖) := by
          rw [outerExpectation_const, measure_univ, mul_one]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hE_le).trans_eq
      (ENNReal.toReal_ofReal (by positivity))

/-- **Generic arbitrary-bridge sufficiency.** Marginal CLT plus asymptotic
equicontinuity implies full outer weak convergence to any explicitly supplied
`P`-Brownian bridge law. No carrier-dimensionality or separability premise is
present. -/
theorem weakConvergesOuter_of_marginalCLT_and_asymptoticallyEquicontinuous_withBridge
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (ν : Measure (LinfF F)) (hν : IsPBrownianBridge F P ν)
    (h_clt : IsMarginalCLT F P) (h_eq : IsAsymptoticallyEquicontinuous F P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    WeakConvergesOuter (fun _ => μ)
      (fun n ξ => empiricalProcessLinf (fun i : Fin n => X i.val ξ)
        (memℓp_empiricalProcess
          ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
          (fun i : Fin n => X i.val ξ))) ν := by
  let 𝔾 : ℕ → Ξ → LinfF F := fun n ξ =>
    empiricalProcessLinf (fun i : Fin n => X i.val ξ)
      (memℓp_empiricalProcess
        ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
        (fun i : Fin n => X i.val ξ))
  letI : IsProbabilityMeasure ν := hν.isProbabilityMeasure
  exact weakConvergesOuter_of_lipschitz_readout
    (μ := fun _ => μ) (Xn := 𝔾) (νD := ν)
    (fun f hf_lip => weakConvergesOuter_withBridge_readout_aux
      hG_env hG hF_meas hF_ent ν hν h_clt h_eq μ X hX_meas hX_indep hX_id hX_law
      f hf_lip)

/-- **Theorem 19.5, carrier-agnostic form.** A measurable class with finite
bracketing-entropy integral has a derived square-integrable envelope and is
Donsker in the literal carrier-agnostic sense, with an existential
`P`-Brownian-bridge limit law.

There is no `hH_inf`: `finiteGaussianPBridge` handles finite carriers, including
rank zero, while the isonormal construction handles infinite carriers. -/
theorem donskerWithBridge_of_finite_bracketing_entropy
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    -- USER-INPUT: every member of the function class is measurable;
    -- vdV Theorem 19.5.
    (hF_meas : ∀ f ∈ F, Measurable f)
    -- USER-INPUT: finite bracketing-entropy integral; vdV Theorem 19.5.
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    : ∃ (G : Ω → ℝ) (_hG_env : IsEnvelope F G) (_hG : MemLp G 2 P),
        IsPDonskerWithBridge F P := by
  obtain ⟨G, hG_env, hG⟩ := exists_l2_envelope_of_entropyIntegral h_int
  have hPD : IsPDonsker F P :=
    isPDonsker_of_finite_bracketing_entropy_integral
      F P hF_meas h_int
  obtain ⟨ν, hν⟩ :=
    exists_pBrownianBridge_all hG_env hG hF_meas h_int
  refine ⟨G, hG_env, hG, ν, hν, ?_⟩
  intro Ξ _ μ _ X hX_meas hX_indep hX_id hX_law
  refine ⟨fun n ξ => memℓp_empiricalProcess
    ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
    (fun i : Fin n => X i.val ξ), ?_⟩
  exact weakConvergesOuter_of_marginalCLT_and_asymptoticallyEquicontinuous_withBridge
    hG_env hG hF_meas h_int ν hν hPD.marginalCLT
      hPD.asymptoticallyEquicontinuous μ X hX_meas hX_indep hX_id hX_law

end AsymptoticStatistics.EmpiricalProcess
