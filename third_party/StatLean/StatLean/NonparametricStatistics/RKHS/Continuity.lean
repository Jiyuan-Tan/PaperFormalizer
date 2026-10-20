module
public import StatLean.NonparametricStatistics.RKHS.Basic

@[expose] public section

/-!
# Continuity of the functions in an RKHS with continuous kernel

If `X` is a topological space and the reproducing kernel `K : X × X → 𝕜` is (jointly)
continuous, then:
* the kernel-function map `x ↦ k_x ∈ H` is continuous, via the identity
  `‖k_y − k_{y₀}‖² = K(y,y) − K(y,y₀) − K(y₀,y) + K(y₀,y₀)`; and
* every `f ∈ H` is a continuous function on `X`, since
  `|f(y) − f(y₀)| ≤ ‖f‖·‖k_y − k_{y₀}‖`.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 2, §2.3, Theorem 2.17 (continuous kernels have continuous functions), via the norm
identity $\|k_y - k_{y_0}\|^2 = K(y,y) - K(y,y_0) - K(y_0,y) + K(y_0,y_0)$.

**Proof formalization notes.** The proof of `continuous_kernelFun` first makes `scalarKernel H`
opaque (`obtain ⟨K, hKd⟩ : ∃ K, scalarKernel H = K`): otherwise the elaborator whnf-unfolds the
kernel through `RKHS.kerFun`'s adjoint during `Continuous.comp` unification and exhausts the
heartbeat budget. Membership continuity then follows from $|f(y) - f(y_0)| \le \|f\|\,\|k_y -
k_{y_0}\|$ exactly as in the book.

**Bibliographic comments.** N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950), §I.5.
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [TopologicalSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

variable (H) in
/-- Norm identity for differences of kernel functions:
`‖k_y − k_{y₀}‖² = re (K(y,y) − K(y,y₀) − K(y₀,y) + K(y₀,y₀))`. -/
theorem norm_kernelFun_sub_sq (y y₀ : X) :
    ‖kernelFun H y - kernelFun H y₀‖ ^ 2
      = RCLike.re (scalarKernel H y y - scalarKernel H y y₀
          - scalarKernel H y₀ y + scalarKernel H y₀ y₀) := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), inner_sub_sub_self]
  simp only [scalarKernel_eq_inner]

variable (H) in
/-- If the kernel is jointly continuous then the kernel-function map `x ↦ k_x` is
continuous from `X` to `H`. -/
theorem continuous_kernelFun
    -- USER-INPUT: joint continuity of the reproducing kernel
    (hK : Continuous fun p : X × X => scalarKernel H p.1 p.2) :
    Continuous fun x : X => kernelFun H x := by
  -- `scalarKernel H` must be made opaque before any `Continuous.comp`: otherwise the
  -- unifier tries to whnf it through `RKHS.kerFun`'s adjoint and blows the heartbeat budget.
  obtain ⟨K, hKd⟩ : ∃ K : X → X → 𝕜, scalarKernel H = K := ⟨_, rfl⟩
  rw [hKd] at hK
  rw [continuous_iff_continuousAt]
  intro y₀
  have hd : Continuous fun y : X => (y, y) := continuous_id.prodMk continuous_id
  have hr : Continuous fun y : X => (y, y₀) := continuous_id.prodMk continuous_const
  have hl : Continuous fun y : X => (y₀, y) := continuous_const.prodMk continuous_id
  have h1 : Continuous fun y : X => K y y := hK.comp' hd
  have h2 : Continuous fun y : X => K y y₀ := hK.comp' hr
  have h3 : Continuous fun y : X => K y₀ y := hK.comp' hl
  have hg : Continuous fun y : X => RCLike.re (K y y - K y y₀ - K y₀ y + K y₀ y₀) :=
    RCLike.continuous_re.comp' (((h1.sub h2).sub h3).add continuous_const)
  have heq : (fun y : X => ‖kernelFun H y - kernelFun H y₀‖)
      = fun y : X => Real.sqrt (RCLike.re (K y y - K y y₀ - K y₀ y + K y₀ y₀)) := by
    funext y
    rw [← hKd, ← norm_kernelFun_sub_sq, Real.sqrt_sq (norm_nonneg _)]
  have key : Filter.Tendsto (fun y : X => kernelFun H y) (nhds y₀)
      (nhds (kernelFun H y₀)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero, heq]
    have hct : Filter.Tendsto
        (fun y : X => Real.sqrt (RCLike.re (K y y - K y y₀ - K y₀ y + K y₀ y₀))) (nhds y₀)
        (nhds (Real.sqrt (RCLike.re (K y₀ y₀ - K y₀ y₀ - K y₀ y₀ + K y₀ y₀)))) :=
      (Real.continuous_sqrt.comp' hg).continuousAt
    simpa using hct
  exact key

/-- **Continuous kernels have continuous functions**: if the reproducing kernel of `H` is
jointly continuous on `X × X`, every member of `H` is a continuous function. -/
theorem continuous_coe_of_continuous_scalarKernel
    -- USER-INPUT: joint continuity of the reproducing kernel
    (hK : Continuous fun p : X × X => scalarKernel H p.1 p.2) (f : H) :
    Continuous (f : X → 𝕜) := by
  have heq : (f : X → 𝕜) = fun y => ⟪kernelFun H y, f⟫_𝕜 := by
    funext y
    rw [inner_kernelFun]
  rw [heq]
  exact continuous_inner.comp ((continuous_kernelFun H hK).prodMk continuous_const)

end StatLean.NonparametricStatistics
