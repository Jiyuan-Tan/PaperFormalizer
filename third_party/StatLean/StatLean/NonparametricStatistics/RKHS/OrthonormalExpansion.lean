module
public import StatLean.NonparametricStatistics.RKHS.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section

/-!
# Pointwise orthonormal expansion of a reproducing kernel

If `{e_i}` is a Hilbert basis of a scalar RKHS `H` on `X`, then the reproducing kernel
expands pointwise as the unordered sum
`K(x, y) = ∑ᵢ conj (e_i y) · e_i x`,
because `k_y = ∑ᵢ conj (e_i y) · e_i` converges in norm and norm convergence implies
pointwise convergence.  On the diagonal this is the Parseval identity
`K(x, x) = ∑ᵢ ‖e_i x‖²`.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 2, §2.1, Theorem 2.4 (pointwise expansion of the kernel along an orthonormal basis).

**Proof formalization notes.** Sums are unordered (`HasSum` over the basis index), matching the
book's net convergence. The proof maps the norm-convergent expansion $k_y = \sum_i
\overline{e_i(y)}\, e_i$ (from `HilbertBasis.hasSum_repr` and the reproducing identity) through
the *continuous* evaluation functional `evalCLM`, which is exactly the book's "norm convergence
implies pointwise convergence" step; the Parseval diagonal form is the same sum pushed through
`RCLike.reCLM`.

**Bibliographic comments.** The expansion of a reproducing kernel along an orthonormal
basis appears in N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950), 337–404, §I.4;
for the Szegő and Bergman kernels it goes back to G. Szegő (1921) and S. Bergman (1922).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} {ι : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

/-- The kernel function of a point expands along a Hilbert basis with coefficients the
conjugated point values: `k_y = ∑ᵢ conj (e_i y) • e_i` (norm convergence, unordered). -/
theorem hasSum_kernelFun (e : HilbertBasis ι 𝕜 H) (y : X) :
    HasSum (fun i => conj ((e i : H) y) • (e i : H)) (kernelFun H y) := by
  have h := e.hasSum_repr (kernelFun H y)
  refine h.congr_fun fun i => ?_
  rw [HilbertBasis.repr_apply_apply, inner_kernelFun_right]

/-- **Pointwise expansion of the kernel along a Hilbert basis**:
`K(x, y) = ∑ᵢ conj (e_i y) · e_i x` as an unordered pointwise sum. -/
theorem hasSum_scalarKernel (e : HilbertBasis ι 𝕜 H) (x y : X) :
    HasSum (fun i => conj ((e i : H) y) * (e i : H) x) (scalarKernel H x y) := by
  have h := (hasSum_kernelFun e y).mapL (evalCLM 𝕜 H x)
  refine h.congr_fun ?_
  intro i
  rw [evalCLM_apply, RKHS.coe_smul]
  rfl

/-- Diagonal (Parseval) form of the kernel expansion: `K(x, x) = ∑ᵢ ‖e_i x‖²`. -/
theorem hasSum_scalarKernel_self (e : HilbertBasis ι 𝕜 H) (x : X) :
    HasSum (fun i => ‖(e i : H) x‖ ^ 2) (RCLike.re (scalarKernel H x x)) := by
  have h := (hasSum_scalarKernel e x x).mapL (RCLike.reCLM (K := 𝕜))
  refine h.congr_fun fun i => ?_
  rw [RCLike.reCLM_apply, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- The point values of a Hilbert basis of an RKHS are square-summable, with sum bounded
by the kernel diagonal. -/
theorem summable_normSq_apply (e : HilbertBasis ι 𝕜 H) (x : X) :
    Summable fun i => ‖(e i : H) x‖ ^ 2 :=
  (hasSum_scalarKernel_self e x).summable

end StatLean.NonparametricStatistics
