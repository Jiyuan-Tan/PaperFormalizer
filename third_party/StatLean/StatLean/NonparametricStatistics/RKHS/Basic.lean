module
public import Mathlib.Analysis.InnerProductSpace.Reproducing

@[expose] public section

/-!
# Scalar reproducing kernel Hilbert spaces: kernel functions and the reproducing identity

Mathlib's `RKHS 𝕜 H X V` class packages a Hilbert space `H` with a continuous injection
into functions `X → V` (pointwise-continuous evaluation).  This file develops the *scalar*
theory (`V = 𝕜`) in the classical form: the kernel function `k_x ∈ H` of a point,
the scalar reproducing kernel `K(x, y) = k_y(x)`, the reproducing identity
`f x = ⟪k_x, f⟫`, Hermitian symmetry, the evaluation functional and its exact norm
`‖E_x‖ = ‖k_x‖ = √(K(x,x))`, and the fact that norm convergence implies pointwise
convergence.

Mathlib's inner product `⟪·,·⟫_𝕜` is conjugate-linear in the *first* slot, so the
classical `f(x) = ⟨f, k_x⟩` (conjugate-linear in the second slot) appears here as
`f x = ⟪kernelFun H x, f⟫_𝕜`, and `K(x,y) = ⟪kernelFun H x, kernelFun H y⟫_𝕜`.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 1, §1.1, Definitions 1.1–1.2 (RKHS, kernel functions, the reproducing kernel) and
the basic identities $K(x,y) = \langle k_y, k_x\rangle$, $\|E_y\|^2 = K(y,y)$ (p. 4); Chapter 2,
§2.1, Lemma 2.2 (norm convergence implies pointwise convergence).

**Proof formalization notes.** The file is a thin scalar layer over Mathlib's vector-valued `RKHS`
class (`Mathlib.Analysis.InnerProductSpace.Reproducing`, itself modeled on this book): `kernelFun
H x` is `RKHS.kerFun H x 1` and `scalarKernel H x y = (kernelFun H y) x`. Mathlib's inner product
is conjugate-linear in the *first* slot, so the book's $f(x) = \langle f, k_x\rangle$ becomes `f x
= ⟪kernelFun H x, f⟫` and $K(x,y) = \langle k_y, k_x\rangle$ becomes `⟪kernelFun H x, kernelFun H
y⟫`; all conjugation orientations downstream follow this flip. The exact evaluation norm
`norm_evalCLM` is the Riesz form `evalCLM = innerSL (kernelFun H x)` plus `innerSL_apply_norm`.

**Bibliographic comments.** The abstract theory of reproducing kernels was systematized
by N. Aronszajn, *Theory of reproducing kernels*, Trans. Amer. Math. Soc. **68** (1950),
337–404; the reproducing identity via the Riesz representation theorem goes back to
Aronszajn and, in special cases, S. Bergman (1922).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

variable (H) in
/-- The **kernel function of the point** `x`: the unique element `k_x ∈ H` representing the
evaluation functional at `x`, i.e. `f x = ⟪k_x, f⟫_𝕜` for every `f ∈ H`.  This is the
scalar (`V = 𝕜`) specialization of `RKHS.kerFun` applied to `1 : 𝕜`. -/
noncomputable def kernelFun (x : X) : H := RKHS.kerFun H x 1

variable (H) in
/-- The **scalar reproducing kernel** of the RKHS `H`: `K(x, y) = k_y(x)`, the value of the
kernel function of `y` at the point `x`.  Beware the argument order: `scalarKernel H x y`
evaluates `kernelFun H y` at `x`. -/
noncomputable def scalarKernel (x y : X) : 𝕜 := (kernelFun H y : H) x

/-- The reproducing identity: evaluation at `x` is the inner product against the kernel
function of `x` (conjugate-linear slot first, per Mathlib's convention). -/
@[simp]
theorem inner_kernelFun (x : X) (f : H) : ⟪kernelFun H x, f⟫_𝕜 = f x := by
  rw [kernelFun, RKHS.kerFun_inner, RCLike.inner_apply', map_one, one_mul]

/-- The reproducing identity, conjugated version. -/
theorem inner_kernelFun_right (x : X) (f : H) : ⟪f, kernelFun H x⟫_𝕜 = conj (f x) := by
  rw [← inner_conj_symm, inner_kernelFun]

variable (H) in
/-- The scalar kernel is the Gram function of the kernel functions:
`K(x, y) = ⟪k_x, k_y⟫_𝕜`. -/
theorem scalarKernel_eq_inner (x y : X) :
    scalarKernel H x y = ⟪kernelFun H x, kernelFun H y⟫_𝕜 := by
  rw [scalarKernel, inner_kernelFun]

variable (H) in
/-- The scalar kernel agrees with Mathlib's operator-valued `RKHS.kernel` evaluated at `1`. -/
theorem scalarKernel_eq_kernel_one (x y : X) :
    scalarKernel H x y = RKHS.kernel H x y 1 := by
  rw [scalarKernel, kernelFun, RKHS.kerFun_apply]

variable (H) in
/-- Hermitian symmetry of the reproducing kernel: `conj (K(x, y)) = K(y, x)`. -/
theorem scalarKernel_conj_symm (x y : X) :
    conj (scalarKernel H x y) = scalarKernel H y x := by
  rw [scalarKernel_eq_inner, scalarKernel_eq_inner, inner_conj_symm]

variable (H) in
/-- The diagonal of the kernel is the squared norm of the kernel function:
`K(x, x) = ‖k_x‖²`. -/
theorem scalarKernel_self (x : X) :
    scalarKernel H x x = ((‖kernelFun H x‖ : 𝕜)) ^ 2 := by
  rw [scalarKernel_eq_inner, inner_self_eq_norm_sq_to_K]

variable (H) in
/-- The diagonal of the kernel is real and nonnegative. -/
theorem re_scalarKernel_self_nonneg (x : X) : 0 ≤ RCLike.re (scalarKernel H x x) := by
  rw [scalarKernel_eq_inner]
  exact inner_self_nonneg

variable (𝕜 H) in
/-- The **evaluation functional** `E_x : H →L[𝕜] 𝕜`, `E_x f = f x`.  Bounded by definition
of an RKHS. -/
noncomputable def evalCLM (x : X) : H →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.proj x).comp (coeCLM 𝕜)

@[simp]
theorem evalCLM_apply (x : X) (f : H) : evalCLM 𝕜 H x f = f x := rfl

/-- Riesz representation of the evaluation functional: `E_x = ⟪k_x, ·⟫_𝕜`. -/
theorem evalCLM_eq_innerSL_kernelFun (x : X) :
    evalCLM 𝕜 H x = innerSL 𝕜 (kernelFun H x) := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [evalCLM_apply, innerSL_apply_apply, inner_kernelFun]

/-- The exact norm of the evaluation functional: `‖E_x‖ = ‖k_x‖ = √(K(x,x))`. -/
theorem norm_evalCLM (x : X) : ‖evalCLM 𝕜 H x‖ = ‖kernelFun H x‖ := by
  rw [evalCLM_eq_innerSL_kernelFun, innerSL_apply_norm]

/-- Pointwise evaluation is controlled by the kernel diagonal:
`‖f x‖ ≤ ‖k_x‖ · ‖f‖`. -/
theorem norm_apply_le (f : H) (x : X) : ‖f x‖ ≤ ‖kernelFun H x‖ * ‖f‖ := by
  rw [← inner_kernelFun x f]
  exact norm_inner_le_norm _ _

/-- Norm convergence in an RKHS implies pointwise convergence: if `f_n → f` in `H`,
then `f_n x → f x` for every `x`. -/
theorem tendsto_apply_of_tendsto {ι : Type*} {l : Filter ι} {f : ι → H} {g : H}
    (h : Filter.Tendsto f l (nhds g)) (x : X) :
    Filter.Tendsto (fun n => f n x) l (nhds (g x)) :=
  ((RKHS.continuous_eval x).tendsto g).comp h

end StatLean.NonparametricStatistics
