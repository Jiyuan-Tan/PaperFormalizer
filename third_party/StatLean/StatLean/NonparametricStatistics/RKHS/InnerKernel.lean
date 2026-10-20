module
public import StatLean.NonparametricStatistics.RKHS.KernelFunction

@[expose] public section

/-!
# The RKHS induced by the inner product of a Hilbert space

For a Hilbert space `L`, the inner product `K(x, y) = ⟪x, y⟫` is a kernel function on the
set `L`, and the corresponding RKHS is the space of bounded linear functionals of the
form `v ↦ ⟪v, w⟫` — i.e. `L` itself, acting on `L` through the (anti-)duality.  We
realize this concretely: `L` carries an RKHS structure over the set `X = L` with
`coeCLM w = fun v => ⟪v, w⟫_𝕜`, under which the kernel function of the point `x` is `x`
itself and the reproducing kernel is the inner product.

The structure is provided as a `def` (`dualRKHS`), not a global instance: making every
Hilbert space coerce to functions on itself would pollute downstream elaboration.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 2, §2.3.4, Proposition 2.24 (the RKHS induced by the inner product) and Exercise
2.10.

**Proof formalization notes.** With Mathlib's convention (inner conjugate-linear in the first
slot), `coeCLM` must put the representing element in the *second* slot, so the members of the dual
RKHS are the functions $v \mapsto \langle v, w\rangle$ — continuous *conjugate-linear*
functionals. The book's Proposition 2.24 (linear functionals) and Exercise 2.10 (conjugate-linear
functionals) therefore swap roles: the ℂ-linear range statement is FALSE here (machine-checked
witness `dualRKHS_range_coe_false`, kept in-file: on `L = ℂ` the element `1` acts as `conj`), and
the correct statement — proved — is Riesz–Fréchet for conjugate-linear functionals, `range = {⇑T :
T ∈ L →L⋆[𝕜] 𝕜}`.

**Bibliographic comments.** This is the Riesz–Fréchet representation theorem (F. Riesz
1907, M. Fréchet 1907) read as a statement about reproducing kernels; see also
N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950), §I.3.
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable (𝕜 : Type*) [RCLike 𝕜]
variable (L : Type*) [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]

/-- The RKHS structure on a Hilbert space `L` over the set `L` itself, where the element
`w` acts as the bounded functional `v ↦ ⟪v, w⟫_𝕜`.  Not an instance by design. -/
@[reducible]
noncomputable def dualRKHS : RKHS 𝕜 L L 𝕜 where
  coeCLM := ContinuousLinearMap.pi fun v => innerSL 𝕜 v
  coeCLM_injective := by
    intro w₁ w₂ h
    refine ext_inner_left 𝕜 fun v => ?_
    simpa using congrFun h v

/-- Under `dualRKHS`, the kernel function of the point `x ∈ L` is `x` itself. -/
theorem dualRKHS_kernelFun (x : L) :
    letI := dualRKHS 𝕜 L
    kernelFun L x = x := by
  letI := dualRKHS 𝕜 L
  refine ext_inner_right 𝕜 fun f => ?_
  rw [inner_kernelFun]
  rfl

/-- **The inner product is the reproducing kernel of the dual RKHS**:
`K(x, y) = ⟪x, y⟫_𝕜`. -/
theorem dualRKHS_scalarKernel (x y : L) :
    letI := dualRKHS 𝕜 L
    scalarKernel L x y = ⟪x, y⟫_𝕜 := by
  letI := dualRKHS 𝕜 L
  change (kernelFun L y) x = ⟪x, y⟫_𝕜
  rw [dualRKHS_kernelFun]
  rfl

/-- The inner product of a Hilbert space is a kernel function on the underlying set. -/
theorem isKernelFun_inner :
    IsKernelFun fun x y : L => ⟪x, y⟫_𝕜 :=
  isKernelFun_featureKernel (𝕜 := 𝕜) (E := L) (X := L) id

/-- Machine-checked witness that `dualRKHS_range_coe` is FALSE over `𝕜 = ℂ`.

`coeCLM` must be `𝕜`-*linear* in the RKHS element, and Mathlib's inner product is linear in
its *second* slot; hence the element `w` is forced into the second slot and the function it
represents is `v ↦ ⟪v, w⟫_𝕜`, which is *conjugate*-linear in `v`.  So the range of the
coercion is the set of continuous conjugate-linear functionals, not the linear ones.

Witness: `L = 𝕜 = ℂ`, `w = 1`, whose function is `conj`.  If `conj = ⇑T` for some
`T : ℂ →L[ℂ] ℂ` then `T 1 = 1`, so `T I = I • T 1 = I`, while `conj I = -I`. -/
private theorem dualRKHS_range_coe_false :
    letI := dualRKHS ℂ ℂ
    Set.range (fun w : ℂ => (w : ℂ → ℂ)) ≠ {g : ℂ → ℂ | ∃ T : ℂ →L[ℂ] ℂ, g = T} := by
  letI := dualRKHS ℂ ℂ
  intro h
  have hmem : (fun v : ℂ => conj v) ∈ Set.range (fun w : ℂ => (w : ℂ → ℂ)) := by
    refine ⟨1, ?_⟩
    funext v
    change ⟪v, (1 : ℂ)⟫_ℂ = conj v
    rw [RCLike.inner_apply, one_mul]
  rw [h] at hmem
  obtain ⟨T, hT⟩ := hmem
  have h1 : T 1 = (1 : ℂ) := by
    have := congrFun hT 1
    simpa using this.symm
  have hI : T Complex.I = -Complex.I := by
    have := congrFun hT Complex.I
    simpa using this.symm
  have h2 : T Complex.I = Complex.I := by
    have hs : Complex.I • (1 : ℂ) = Complex.I := by simp
    rw [← hs, map_smul, h1, smul_eq_mul, mul_one]
  rw [hI] at h2
  exact Complex.I_ne_zero (by linear_combination -h2 / 2)

/-- Under `dualRKHS`, the functions of the RKHS are exactly the bounded *conjugate-linear*
functionals on `L` (Riesz–Fréchet).  With Mathlib's inner product (conjugate-linear in the
first slot), the element `w` acts as `v ↦ ⟪v, w⟫_𝕜`, which is conjugate-linear in `v`; over
`ℝ` these are just the bounded linear functionals, recovering the classical statement.
(The `𝕜`-linear version is false over `ℂ` — see `dualRKHS_range_coe_false` above; this is
the classical duality-of-conventions between the inner-product kernel and its conjugate.) -/
theorem dualRKHS_range_coe :
    letI := dualRKHS 𝕜 L
    Set.range (fun w : L => (w : L → 𝕜))
      = {g : L → 𝕜 | ∃ T : L →L⋆[𝕜] 𝕜, g = T} := by
  letI := dualRKHS 𝕜 L
  ext g
  constructor
  · rintro ⟨w, rfl⟩
    -- the functional `v ↦ ⟪v, w⟫` is conjugate-linear and bounded by `‖w‖`
    refine ⟨LinearMap.mkContinuous
      { toFun := fun v => ⟪v, w⟫_𝕜
        map_add' := fun v₁ v₂ => inner_add_left _ _ _
        map_smul' := fun c v => by
          simpa [smul_eq_mul] using inner_smul_left (𝕜 := 𝕜) v w c }
      ‖w‖ (fun v => by
        change ‖⟪v, w⟫_𝕜‖ ≤ ‖w‖ * ‖v‖
        rw [mul_comm]
        exact norm_inner_le_norm _ _), ?_⟩
    rfl
  · rintro ⟨T, rfl⟩
    -- `v ↦ conj (T v)` is a bounded `𝕜`-linear functional; represent it by Riesz
    set S : L →L[𝕜] 𝕜 := LinearMap.mkContinuous
      { toFun := fun v => conj (T v)
        map_add' := fun v₁ v₂ => by simp
        map_smul' := fun c v => by
          simp [ContinuousLinearMap.map_smulₛₗ, smul_eq_mul] }
      ‖T‖ (fun v => by
        change ‖conj (T v)‖ ≤ ‖T‖ * ‖v‖
        rw [RCLike.norm_conj]
        exact T.le_opNorm v) with hS
    refine ⟨(InnerProductSpace.toDual 𝕜 L).symm S, ?_⟩
    funext v
    change ⟪v, (InnerProductSpace.toDual 𝕜 L).symm S⟫_𝕜 = T v
    rw [← inner_conj_symm, InnerProductSpace.toDual_symm_apply, hS]
    change conj (conj (T v)) = T v
    rw [RCLike.conj_conj]

end StatLean.NonparametricStatistics
