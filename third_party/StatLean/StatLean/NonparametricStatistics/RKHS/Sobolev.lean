module
public import StatLean.NonparametricStatistics.RKHS.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section

/-!
# The Sobolev space `H₀¹[0,1]` as a reproducing kernel Hilbert space

The classical Sobolev space of absolutely continuous `f : [0,1] → ℝ` with
square-integrable derivative and `f(0) = f(1) = 0`, under the Dirichlet inner product
`⟪f, g⟫ = ∫₀¹ f' g'`, is an RKHS whose kernel is the Green's function of `−d²/dt²` with
Dirichlet boundary conditions:
`K(x, y) = min x y − x y = (1 − max x y) · min x y`.

**Model.** Since `f(x) = ∫₀ˣ f'` characterizes absolutely continuous functions, we take
the *integral representation as the definition*: the carrier is the closed subspace
`{g ∈ L²[0,1] : ∫₀¹ g = 0}` (the orthogonal complement of the constants), an element `g`
acting as the function `x ↦ ∫₀ˣ g = ⟪𝟙_{[0,x]}, g⟫`.  The Dirichlet inner product on the
functions is then the `L²` inner product of the representatives, evaluation is bounded
with `‖E_x‖² = x(1−x)`, and the kernel function of `x` is the representative
`𝟙_{[0,x]} − x·𝟙` (whose primitive is the Green's function above).  Completeness is
inherited from `L²` — this replaces the classical pointwise-Cauchy argument.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 1, §1.3.1 (Sobolev spaces on $[0,1]$: the Dirichlet space of absolutely continuous
functions with $f(0)=f(1)=0$, its kernel, and the sharp evaluation bound); the
integral-representation view is the book's §11.2.1.

**Proof formalization notes.** The book defines the space via absolute continuity and proves $f(x)
= \int_0^x f'$; we take the integral representation as the *definition*: the carrier is the
mean-zero subspace $(\mathbb{R}\cdot\mathbf{1})^{\perp} \subseteq L^2[0,1]$ of derivative
representatives, an element $g$ acting as $x \mapsto \langle \mathbf{1}_{[0,x]}, g\rangle$.
Completeness is then inherited from $L^2$ (replacing the book's pointwise-Cauchy argument), the
boundary conditions become the mean-zero constraint, and the kernel function of $x$ is the
representative $\mathbf{1}_{[0,x]} - x\cdot\mathbf{1}$, giving $K(x,y) = \min(x,y) - xy$ and
$\|E_x\|^2 = x(1-x)$ by four indicator inner products. Injectivity of the action (the only
nontrivial point of the RKHS structure) is a π-system argument promoted from the rays $[0,x]$.

**Bibliographic comments.** The Green's-function kernel of the Dirichlet Sobolev space
is classical; see N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950), §II.5, and
S. Bergman's earlier work on kernels of differential operators.  This space is the
Cameron–Martin space of the Brownian bridge (R. H. Cameron and W. T. Martin, 1947).
-/

open RKHS MeasureTheory
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

/-- The base interval `[0,1]` of the Sobolev space, as the domain of its functions. -/
abbrev unitInterval01 : Set ℝ := Set.Icc 0 1

/-- Lebesgue measure restricted to `[0,1]`. -/
noncomputable abbrev sobolevMeasure : Measure ℝ := volume.restrict unitInterval01

instance : Fact ((volume : Measure ℝ) unitInterval01 < ⊤) :=
  ⟨by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩

/-- The constant function `1` as an element of `L²[0,1]`. -/
noncomputable def sobolevOne : Lp ℝ 2 sobolevMeasure :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) (1 : ℝ)

/-- The indicator `𝟙_{[0,x]}` as an element of `L²[0,1]`; the "derivative" of the ramp
`t ↦ min t x`. -/
noncomputable def sobolevInd (x : ℝ) : Lp ℝ 2 sobolevMeasure :=
  indicatorConstLp 2 (measurableSet_Icc (a := (0 : ℝ)) (b := x)) (measure_ne_top _ _) (1 : ℝ)

instance : IsClosed (((ℝ ∙ sobolevOne)ᗮ : Submodule ℝ (Lp ℝ 2 sobolevMeasure)) :
    Set (Lp ℝ 2 sobolevMeasure)) :=
  Submodule.isClosed_orthogonal _

section Aux

/-- The measure of `[0,m]` inside `[0,1]`, as a real number. -/
private theorem sobolevMeasure_real_Icc {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    sobolevMeasure.real (Set.Icc 0 m) = m := by
  change ((volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Icc 0 m)).toReal = m
  rw [Measure.restrict_apply measurableSet_Icc, Set.Icc_inter_Icc, max_self, min_eq_left hm1,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hm0]

/-- The total mass of `sobolevMeasure` is one. -/
private theorem sobolevMeasure_real_univ : sobolevMeasure.real Set.univ = 1 := by
  change ((volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ).toReal = 1
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  norm_num

/-- Restricting `sobolevMeasure` to `[0,1]` changes nothing. -/
private theorem sobolevMeasure_restrict_Icc :
    sobolevMeasure.restrict (Set.Icc (0 : ℝ) 1) = sobolevMeasure := by
  change (volume.restrict (Set.Icc (0 : ℝ) 1)).restrict (Set.Icc (0 : ℝ) 1) = _
  rw [Measure.restrict_restrict measurableSet_Icc, Set.inter_self]

private theorem inner_sobolevInd_sobolevInd {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) :
    ⟪sobolevInd x, sobolevInd y⟫_ℝ = min x y := by
  rw [sobolevInd, sobolevInd,
    MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (μ := sobolevMeasure) (measurableSet_Icc (a := (0 : ℝ)) (b := x))
      (measurableSet_Icc (a := (0 : ℝ)) (b := y)) (measure_ne_top _ _) (measure_ne_top _ _),
    Set.Icc_inter_Icc, max_self,
    sobolevMeasure_real_Icc (le_min hx0 hy0) ((min_le_left x y).trans hx1)]

private theorem inner_sobolevOne_sobolevInd {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ⟪sobolevOne, sobolevInd y⟫_ℝ = y := by
  rw [sobolevOne, sobolevInd,
    MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (μ := sobolevMeasure) MeasurableSet.univ (measurableSet_Icc (a := (0 : ℝ)) (b := y))
      (measure_ne_top _ _) (measure_ne_top _ _),
    Set.univ_inter, sobolevMeasure_real_Icc hy0 hy1]

private theorem inner_sobolevInd_sobolevOne {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ⟪sobolevInd y, sobolevOne⟫_ℝ = y := by
  rw [real_inner_comm, inner_sobolevOne_sobolevInd hy0 hy1]

private theorem inner_sobolevOne_sobolevOne : ⟪sobolevOne, sobolevOne⟫_ℝ = 1 := by
  rw [sobolevOne,
    MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (μ := sobolevMeasure) MeasurableSet.univ MeasurableSet.univ
      (measure_ne_top _ _) (measure_ne_top _ _),
    Set.univ_inter, sobolevMeasure_real_univ]

private theorem inner_sobolevInd_eq_setIntegral (x : ℝ) (g : Lp ℝ 2 sobolevMeasure) :
    ⟪sobolevInd x, g⟫_ℝ = ∫ t in Set.Icc 0 x, (g : ℝ → ℝ) t ∂sobolevMeasure :=
  MeasureTheory.L2.inner_indicatorConstLp_one (𝕜 := ℝ) (μ := sobolevMeasure)
    (measurableSet_Icc (a := (0 : ℝ)) (b := x)) (measure_ne_top _ _) g

private theorem inner_sobolevOne_eq_integral (g : Lp ℝ 2 sobolevMeasure) :
    ⟪sobolevOne, g⟫_ℝ = ∫ t, (g : ℝ → ℝ) t ∂sobolevMeasure := by
  rw [← MeasureTheory.setIntegral_univ]
  exact MeasureTheory.L2.inner_indicatorConstLp_one (𝕜 := ℝ) (μ := sobolevMeasure)
    MeasurableSet.univ (measure_ne_top _ _) g

/-- The `[0,1]`-indicator and the constant `1` have the same action on `L²[0,1]`. -/
private theorem inner_sobolevInd_one_eq (g : Lp ℝ 2 sobolevMeasure) :
    ⟪sobolevInd (1 : ℝ), g⟫_ℝ = ⟪sobolevOne, g⟫_ℝ := by
  rw [inner_sobolevInd_eq_setIntegral, inner_sobolevOne_eq_integral, sobolevMeasure_restrict_Icc]

end Aux

/-- **The Dirichlet–Sobolev space `H₀¹[0,1]`**, modeled as the mean-zero subspace of
`L²[0,1]` carrying the derivative representative of each function; the boundary
conditions `f(0) = f(1) = 0` correspond to the mean-zero constraint. -/
noncomputable abbrev SobolevH01 : Type _ := ↥((ℝ ∙ sobolevOne)ᗮ)

section Injectivity

/-- The left-infinite rational rays form a π-system generating the Borel σ-algebra of `ℝ`. -/
private theorem isPiSystem_Iic_rat : IsPiSystem (⋃ a : ℚ, {Set.Iic (a : ℝ)}) := by
  rintro s hs t ht -
  simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hs ht
  obtain ⟨p, rfl⟩ := hs
  obtain ⟨q, rfl⟩ := ht
  refine Set.mem_iUnion.mpr ⟨min p q, ?_⟩
  rw [Set.mem_singleton_iff, Set.Iic_inter_Iic]
  norm_cast

/-- **Uniqueness of the primitive**: an `L²[0,1]` function whose integral over every initial
segment `[0,x]`, `x ∈ [0,1]`, vanishes is the zero element.  Proved by promoting the
hypothesis from the π-system of left-infinite rays to all Borel sets. -/
private theorem lp_eq_zero_of_setIntegral_Icc_eq_zero (g : Lp ℝ 2 sobolevMeasure)
    (h : ∀ x ∈ unitInterval01,
      ∫ t in Set.Icc 0 x, (g : ℝ → ℝ) t ∂sobolevMeasure = 0) : g = 0 := by
  have hint : Integrable (g : ℝ → ℝ) sobolevMeasure := by
    rw [← integrableOn_univ]
    exact integrableOn_Lp_of_measure_ne_top g fact_one_le_two_ennreal.elim (measure_ne_top _ _)
  have hUniv : ∫ t, (g : ℝ → ℝ) t ∂sobolevMeasure = 0 := by
    have h1 := h 1 (Set.mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩)
    rwa [sobolevMeasure_restrict_Icc] at h1
  have hIic : ∀ a : ℝ, ∫ t in Set.Iic a, (g : ℝ → ℝ) t ∂sobolevMeasure = 0 := by
    intro a
    rcases lt_or_ge a 0 with ha | ha
    · refine setIntegral_measure_zero _ ?_
      change (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic a) = 0
      rw [Measure.restrict_apply measurableSet_Iic,
        show Set.Iic a ∩ Set.Icc (0 : ℝ) 1 = ∅ by
          refine Set.eq_empty_iff_forall_notMem.mpr ?_
          rintro t ⟨hta, h0, -⟩
          exact absurd (le_trans h0 hta) (not_le.mpr ha)]
      exact measure_empty
    · have hres : sobolevMeasure.restrict (Set.Iic a)
          = sobolevMeasure.restrict (Set.Icc 0 (min a 1)) := by
        change (volume.restrict (Set.Icc (0 : ℝ) 1)).restrict (Set.Iic a)
          = (volume.restrict (Set.Icc (0 : ℝ) 1)).restrict (Set.Icc 0 (min a 1))
        rw [Measure.restrict_restrict measurableSet_Iic,
          Measure.restrict_restrict measurableSet_Icc]
        congr 1
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]
        tauto
      rw [hres]
      exact h (min a 1) (Set.mem_Icc.mpr ⟨le_min ha zero_le_one, min_le_right _ _⟩)
  have key : ∀ u : Set ℝ, MeasurableSet u →
      ∫ t in u, (g : ℝ → ℝ) t ∂sobolevMeasure = 0 := by
    refine MeasurableSpace.induction_on_inter
      (C := fun u _ => ∫ t in u, (g : ℝ → ℝ) t ∂sobolevMeasure = 0)
      (s := ⋃ a : ℚ, {Set.Iic (a : ℝ)})
      (BorelSpace.measurable_eq.trans Real.borel_eq_generateFrom_Iic_rat)
      isPiSystem_Iic_rat (by simp) ?_ ?_ ?_
    · rintro u hu
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hu
      obtain ⟨q, rfl⟩ := hu
      exact hIic _
    · intro u hu hu0
      have hadd := integral_add_compl hu hint
      rw [hu0, zero_add] at hadd
      rw [hadd]
      exact hUniv
    · intro fseq hdisj hmeas hf0
      rw [integral_iUnion hmeas hdisj hint.integrableOn]
      simp [hf0]
  exact Lp.eq_zero_iff_ae_eq_zero.mpr
    (MeasureTheory.Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero hint
      fun s hs _ => key s hs)

/-- Injectivity of the action of `H₀¹[0,1]` on `[0,1]`. -/
private theorem sobolevCoe_injective :
    Function.Injective
      (⇑((ContinuousLinearMap.pi fun x : unitInterval01 => innerSL ℝ (sobolevInd x.1)).comp
        (Submodule.subtypeL ((ℝ ∙ sobolevOne)ᗮ))) : SobolevH01 → unitInterval01 → ℝ) := by
  intro f₁ f₂ hf
  have hzero : (f₁ : Lp ℝ 2 sobolevMeasure) - (f₂ : Lp ℝ 2 sobolevMeasure) = 0 := by
    refine lp_eq_zero_of_setIntegral_Icc_eq_zero _ ?_
    intro x hx
    rw [← inner_sobolevInd_eq_setIntegral, inner_sub_right]
    have hval : ⟪sobolevInd x, (f₁ : Lp ℝ 2 sobolevMeasure)⟫_ℝ
        = ⟪sobolevInd x, (f₂ : Lp ℝ 2 sobolevMeasure)⟫_ℝ := congrFun hf ⟨x, hx⟩
    rw [hval, sub_self]
  exact Subtype.ext (sub_eq_zero.mp hzero)

end Injectivity

/-- The Sobolev space is an RKHS on `[0,1]`: the element with derivative representative
`g` acts as the function `x ↦ ∫₀ˣ g = ⟪𝟙_{[0,x]}, g⟫`. -/
noncomputable instance : RKHS ℝ SobolevH01 unitInterval01 ℝ where
  coeCLM :=
    (ContinuousLinearMap.pi fun x : unitInterval01 => innerSL ℝ (sobolevInd x.1)).comp
      (Submodule.subtypeL _)
  coeCLM_injective := by
    exact sobolevCoe_injective

/-- Unfolding of the RKHS action of the Sobolev space. -/
private theorem sobolevH01_coe_apply (f : SobolevH01) (x : unitInterval01) :
    f x = ⟪sobolevInd (x : ℝ), (f : Lp ℝ 2 sobolevMeasure)⟫_ℝ := rfl


/-- Interpretation of the action: `f x = ∫_{[0,x]} g` where `g` is the derivative
representative of `f`. -/
theorem sobolevH01_apply (f : SobolevH01) (x : unitInterval01) :
    f x = ∫ t in Set.Icc 0 (x : ℝ), ((f : Lp ℝ 2 sobolevMeasure) : ℝ → ℝ) t
      ∂sobolevMeasure := by
  rw [sobolevH01_coe_apply, inner_sobolevInd_eq_setIntegral]

/-- Left boundary condition: every function of the Sobolev space vanishes at `0`. -/
theorem sobolevH01_apply_zero (f : SobolevH01) :
    f (⟨0, by norm_num⟩ : unitInterval01) = 0 := by
  rw [sobolevH01_apply]
  refine setIntegral_measure_zero _ ?_
  change (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Icc 0 (0 : ℝ)) = 0
  rw [Set.Icc_self, Measure.restrict_apply (measurableSet_singleton _)]
  exact measure_mono_null Set.inter_subset_left (by simp)

/-- Right boundary condition: every function of the Sobolev space vanishes at `1`
(this is where the mean-zero constraint enters). -/
theorem sobolevH01_apply_one (f : SobolevH01) :
    f (⟨1, by norm_num⟩ : unitInterval01) = 0 := by
  rw [sobolevH01_coe_apply]
  change ⟪sobolevInd (1 : ℝ), (f : Lp ℝ 2 sobolevMeasure)⟫_ℝ = 0
  rw [inner_sobolevInd_one_eq]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp f.2

/-- Completeness of the Sobolev carrier, as an explicit term (the orthogonal complement
of a subspace of the complete space `L²` is complete). -/
@[reducible]
noncomputable def sobolevH01CompleteSpace : CompleteSpace SobolevH01 :=
  Submodule.instOrthogonalCompleteSpace (ℝ ∙ sobolevOne)

/-- The kernel function of the Sobolev space at `x` (the completeness instance is passed
explicitly; definitionally `kernelFun SobolevH01 x`). -/
noncomputable def sobolevKernelFun (x : unitInterval01) : SobolevH01 :=
  @kernelFun ℝ _ unitInterval01 SobolevH01 _ _ sobolevH01CompleteSpace _ x

/-- The reproducing kernel of the Sobolev space (definitionally
`scalarKernel SobolevH01`). -/
noncomputable def sobolevScalarKernel (x y : unitInterval01) : ℝ :=
  @scalarKernel ℝ _ unitInterval01 SobolevH01 _ _ sobolevH01CompleteSpace _ x y

/-- The reproducing identity for the Sobolev kernel functions, obtained directly from
Mathlib's `RKHS.kerFun_inner` (so it does not depend on `RKHS/Basic.lean`). -/
private theorem inner_sobolevKernelFun (x : unitInterval01) (f : SobolevH01) :
    ⟪sobolevKernelFun x, f⟫_ℝ = f x := by
  have h := @RKHS.kerFun_inner ℝ _ unitInterval01 ℝ _ _ SobolevH01 _ _ _
    sobolevH01CompleteSpace _ x (1 : ℝ) f
  have hone : ⟪(1 : ℝ), (1 : ℝ)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq]; norm_num
  rw [show ⟪(1 : ℝ), f x⟫_ℝ = f x from by
    calc ⟪(1 : ℝ), f x⟫_ℝ = ⟪(1 : ℝ), (f x) • (1 : ℝ)⟫_ℝ := by rw [smul_eq_mul, mul_one]
      _ = f x * ⟪(1 : ℝ), (1 : ℝ)⟫_ℝ := real_inner_smul_right _ _ _
      _ = f x := by rw [hone, mul_one]] at h
  exact h

/-- The candidate kernel representative `𝟙_{[0,x]} − x·𝟙` is mean zero. -/
private theorem sobolevCandidate_mem (x : unitInterval01) :
    sobolevInd (x : ℝ) - (x : ℝ) • sobolevOne ∈ (ℝ ∙ sobolevOne)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
    real_inner_smul_right, inner_sobolevOne_sobolevInd x.2.1 x.2.2, inner_sobolevOne_sobolevOne]
  ring

/-- The kernel function of the point `x` has derivative representative
`𝟙_{[0,x]} − x·𝟙` (the formal solution of the Dirichlet boundary-value problem
`−k'' = δₓ`). -/
theorem sobolevH01_kernelFun (x : unitInterval01) :
    (sobolevKernelFun x : Lp ℝ 2 sobolevMeasure)
      = sobolevInd x.1 - (x : ℝ) • sobolevOne := by
  set k : SobolevH01 :=
    ⟨sobolevInd (x : ℝ) - (x : ℝ) • sobolevOne, sobolevCandidate_mem x⟩ with hk
  have hrep : ∀ f : SobolevH01, ⟪k, f⟫_ℝ = f x := by
    intro f
    have hexp : ⟪k, f⟫_ℝ
        = ⟪sobolevInd (x : ℝ), (f : Lp ℝ 2 sobolevMeasure)⟫_ℝ
          - (x : ℝ) * ⟪sobolevOne, (f : Lp ℝ 2 sobolevMeasure)⟫_ℝ := by
      rw [hk]
      change ⟪sobolevInd (x : ℝ) - (x : ℝ) • sobolevOne,
        (f : Lp ℝ 2 sobolevMeasure)⟫_ℝ = _
      rw [inner_sub_left, real_inner_smul_left]
    rw [hexp, Submodule.mem_orthogonal_singleton_iff_inner_right.mp f.2, sobolevH01_coe_apply]
    ring
  have hzero : ∀ f : SobolevH01, ⟪k - sobolevKernelFun x, f⟫_ℝ = 0 := by
    intro f
    rw [inner_sub_left, hrep, inner_sobolevKernelFun, sub_self]
  have hkeq : k = sobolevKernelFun x := sub_eq_zero.mp (inner_self_eq_zero.mp
    (hzero (k - sobolevKernelFun x)))
  rw [← hkeq, hk]

/-- **The reproducing kernel of `H₀¹[0,1]` is the Dirichlet Green's function**:
`K(x, y) = min x y − x y`. -/
theorem sobolevH01_scalarKernel (x y : unitInterval01) :
    sobolevScalarKernel x y = min (x : ℝ) y - (x : ℝ) * y := by
  have hgram : sobolevScalarKernel x y = ⟪sobolevKernelFun x, sobolevKernelFun y⟫_ℝ :=
    (inner_sobolevKernelFun x (sobolevKernelFun y)).symm
  rw [hgram]
  change ⟪(sobolevKernelFun x : Lp ℝ 2 sobolevMeasure),
    (sobolevKernelFun y : Lp ℝ 2 sobolevMeasure)⟫_ℝ = _
  rw [sobolevH01_kernelFun, sobolevH01_kernelFun, inner_sub_left, inner_sub_right,
    inner_sub_right, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_right, inner_sobolevInd_sobolevInd x.2.1 x.2.2 y.2.1,
    inner_sobolevInd_sobolevOne x.2.1 x.2.2, inner_sobolevOne_sobolevInd y.2.1 y.2.2,
    inner_sobolevOne_sobolevOne]
  ring

/-- The Green's function in case-split form: `(1−y)x` for `x ≤ y`, `(1−x)y` otherwise. -/
theorem min_sub_mul_eq_ite (x y : ℝ) :
    min x y - x * y = if x ≤ y then (1 - y) * x else (1 - x) * y := by
  rcases le_or_gt x y with h | h
  · rw [if_pos h, min_eq_left h]; ring
  · rw [if_neg (not_le.mpr h), min_eq_right h.le]; ring

/-- The exact norm of evaluation on the Sobolev space: `‖E_x‖² = ‖k_x‖² = x(1−x)`. -/
theorem sobolevH01_norm_kernelFun_sq (x : unitInterval01) :
    ‖sobolevKernelFun x‖ ^ 2 = (x : ℝ) * (1 - (x : ℝ)) := by
  have hgram : sobolevScalarKernel x x = ⟪sobolevKernelFun x, sobolevKernelFun x⟫_ℝ :=
    (inner_sobolevKernelFun x (sobolevKernelFun x)).symm
  have hd := sobolevH01_scalarKernel x x
  rw [min_self, hgram, real_inner_self_eq_norm_sq] at hd
  rw [hd]; ring

/-- The sharp evaluation bound on the Sobolev space:
`|f(x)| ≤ √(x(1−x)) · ‖f‖` — improving the naive Cauchy–Schwarz bound `√x · ‖f‖`. -/
theorem sobolevH01_norm_apply_le (f : SobolevH01) (x : unitInterval01) :
    ‖f x‖ ≤ Real.sqrt ((x : ℝ) * (1 - (x : ℝ))) * ‖f‖ := by
  have hnorm : Real.sqrt ((x : ℝ) * (1 - (x : ℝ))) = ‖sobolevKernelFun x‖ := by
    rw [← sobolevH01_norm_kernelFun_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm, ← inner_sobolevKernelFun x f]
  exact norm_inner_le_norm _ _

end StatLean.NonparametricStatistics
