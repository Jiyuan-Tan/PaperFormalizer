module
public import StatLean.NonparametricStatistics.RKHS.KernelFunction
public import StatLean.NonparametricStatistics.RKHS.Moore

@[expose] public section

/-!
# Feature maps and the kernel method

A **feature map** is an embedding `φ : X → L` of the data domain into an auxiliary
Hilbert space; it induces the kernel `K(x, y) = ⟪φ x, φ y⟫` on `X` (`featureKernel`,
defined in `KernelFunction.lean`, where it is shown to be a kernel function).  This file
records the two directions of the "kernel trick":

* every RKHS kernel arises from a feature map — namely its own kernel functions
  (`scalarKernel_eq_featureKernel`, restated here);
* every kernel induced by a feature map is the reproducing kernel of an RKHS
  (via Moore's theorem), so optimizing over the induced function class is optimizing
  over an RKHS.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 8, §8.2 (the kernel method: feature maps, induced kernels, and predictors).

**Proof formalization notes.** The two directions of the kernel trick: `featureKernel` positivity
lives in `KernelFunction.lean`, and the converse — every kernel function is a feature-map kernel —
instantiates Moore's theorem with $\varphi = x \mapsto k_x$. As in `Moore.lean`, the feature-space
universe must be pinned to `Type (max uK uX)` (auto-bound `Type _` would quantify over an
independent universe and fail).

**Bibliographic comments.** The kernel trick in statistical learning goes back to
M. Aizerman, E. Braverman and L. Rozonoer, *Theoretical foundations of the potential
function method*, Autom. Remote Control **25** (1964), 821–837, and was popularized by
B. E. Boser, I. M. Guyon and V. N. Vapnik, *A training algorithm for optimal margin
classifiers*, COLT (1992).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace 𝕜 L]

/-- A feature-map kernel is Hermitian-diagonal-normalized: `K(x,x) = ‖φ x‖²`. -/
theorem featureKernel_self (φ : X → L) (x : X) :
    featureKernel 𝕜 φ x x = ((‖φ x‖ : 𝕜)) ^ 2 := by
  simp [featureKernel, inner_self_eq_norm_sq_to_K]

universe uK uX in
/-- **Every kernel function is a feature-map kernel**: by Moore's theorem, a kernel
function `K` is the Gram function of the kernel-function embedding of its RKHS (the
feature space lives in `Type (max uK uX)`, the universe of the Moore completion). -/
theorem IsKernelFun.exists_featureMap {k : Type uK} [RCLike k] {Y : Type uX}
    {K : Y → Y → k} (hK : IsKernelFun K) :
    ∃ (L' : Type (max uK uX)) (_ : NormedAddCommGroup L') (_ : InnerProductSpace k L')
      (φ : Y → L'), K = featureKernel k φ := by
  obtain ⟨H, _, _, _, _, hHK⟩ := hK.exists_rkhs
  exact ⟨H, ‹_›, ‹_›, kernelFun (X := Y) H, by
    rw [← hHK, scalarKernel_eq_featureKernel]⟩

variable (𝕜) in
/-- The predictor class of a feature map: functions of the form `x ↦ ⟪φ x, w⟫` for
`w ∈ L` — the "linear functionals in feature space". -/
def featurePredictor (φ : X → L) (w : L) : X → 𝕜 := fun x => ⟪φ x, w⟫_𝕜

/-- Predictors are pointwise-bounded by the kernel diagonal:
`‖(featurePredictor φ w) x‖ ≤ √(re K(x,x)) · ‖w‖`. -/
theorem norm_featurePredictor_le (φ : X → L) (w : L) (x : X) :
    ‖featurePredictor 𝕜 φ w x‖
      ≤ Real.sqrt (RCLike.re (featureKernel 𝕜 φ x x)) * ‖w‖ := by
  have hre : RCLike.re (featureKernel 𝕜 φ x x) = ‖φ x‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := 𝕜) (φ x)
  rw [hre, Real.sqrt_sq (norm_nonneg _)]
  exact norm_inner_le_norm (𝕜 := 𝕜) (φ x) w

end StatLean.NonparametricStatistics
