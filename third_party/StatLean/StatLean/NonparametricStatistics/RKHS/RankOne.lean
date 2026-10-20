module
public import StatLean.NonparametricStatistics.RKHS.KernelFunction

@[expose] public section

/-!
# The rank-one RKHS induced by a single function

For a function `f₀ : X → 𝕜`, the product `K(x, y) = f₀(x) · conj (f₀ y)` is a kernel
function, and any RKHS with this kernel is the one-dimensional space spanned by `f₀`,
on which `f₀` itself has norm `1` (when `f₀ ≠ 0`).

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 2, §2.3.1, Proposition 2.19 (the one-dimensional RKHS induced by a single function).

**Proof formalization notes.** Elements of an RKHS are determined by their values (`RKHS.ext`), so
the unit representative of $f_0$ is pinned down pointwise; spanning follows because every kernel
function is a scalar multiple of it and the line `𝕜 ∙ g` is closed (finite-dimensional), so the
closed span of the kernel functions (`kerFun_dense`) collapses to the line.

**Bibliographic comments.** N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950), Part I
§2 (elementary examples of reproducing kernels).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}

/-- The rank-one product `K(x, y) = f₀(x) · conj (f₀ y)` of any function with itself is a
kernel function. -/
theorem isKernelFun_rankOne (f₀ : X → 𝕜) :
    IsKernelFun fun x y => f₀ x * conj (f₀ y) := by
  have key : (fun x y => f₀ x * conj (f₀ y)) = featureKernel 𝕜 fun x => conj (f₀ x) := by
    funext x y
    simp only [featureKernel, RCLike.inner_apply, RCLike.conj_conj]
    ring
  rw [key]
  exact isKernelFun_featureKernel _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

-- The kernel functions of a rank-one RKHS are the scalar multiples of any member
-- realizing the generating function `f₀`.  Shared by the two headline results below;
-- the norm hypothesis of `kernelFun_of_scalarKernel_rankOne` is not needed for this.
private theorem kernelFun_rankOne_aux (f₀ : X → 𝕜)
    (hK : scalarKernel H = fun x y => f₀ x * conj (f₀ y))
    {g : H} (hg : (g : X → 𝕜) = f₀) (y : X) :
    kernelFun H y = conj (f₀ y) • g := by
  refine RKHS.ext fun x => ?_
  have h1 : scalarKernel H x y = f₀ x * conj (f₀ y) := by rw [hK]
  calc (kernelFun H y : H) x = f₀ x * conj (f₀ y) := h1
    _ = conj (f₀ y) * f₀ x := mul_comm _ _
    _ = (conj (f₀ y) • g : H) x := by simp [congrFun hg x]

/-- **The RKHS of a rank-one kernel is one-dimensional**: if the kernel of `H` is
`f₀(x) · conj (f₀ y)` with `f₀ ≠ 0`, then `H` is spanned by a single unit vector whose
underlying function is `f₀`. -/
theorem exists_unit_spanning_of_scalarKernel_rankOne (f₀ : X → 𝕜)
    -- USER-INPUT: the generating function is not identically zero
    (hf₀ : f₀ ≠ 0)
    -- USER-INPUT: the kernel of `H` is the rank-one product of `f₀`
    (hK : scalarKernel H = fun x y => f₀ x * conj (f₀ y)) :
    ∃ g : H, (g : X → 𝕜) = f₀ ∧ ‖g‖ = 1 ∧ ∀ h : H, ∃ c : 𝕜, h = c • g := by
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.mp hf₀
  have hy₀' : f₀ y₀ ≠ 0 := hy₀
  have hc₀ : conj (f₀ y₀) ≠ 0 := by
    simpa using hy₀'
  -- the candidate unit vector
  refine ⟨(conj (f₀ y₀))⁻¹ • kernelFun H y₀, ?_, ?_, ?_⟩
  · funext x
    have h1 : scalarKernel H x y₀ = f₀ x * conj (f₀ y₀) := by rw [hK]
    calc (((conj (f₀ y₀))⁻¹ • kernelFun H y₀ : H) : X → 𝕜) x
        = (conj (f₀ y₀))⁻¹ * (f₀ x * conj (f₀ y₀)) := by
          simp only [RKHS.coe_smul, Pi.smul_apply, smul_eq_mul]
          rw [show (kernelFun H y₀ : H) x = scalarKernel H x y₀ from rfl, h1]
      _ = f₀ x := by field_simp
  · -- the norm of the kernel function at `y₀` is `‖f₀ y₀‖`
    have hnk : ‖kernelFun H y₀‖ = ‖f₀ y₀‖ := by
      have h1 : scalarKernel H y₀ y₀ = ((‖kernelFun H y₀‖ : 𝕜)) ^ 2 := scalarKernel_self H y₀
      have h2 : scalarKernel H y₀ y₀ = f₀ y₀ * conj (f₀ y₀) := by rw [hK]
      rw [RCLike.mul_conj, h1] at h2
      have h3 : ((‖kernelFun H y₀‖ ^ 2 : ℝ) : 𝕜) = ((‖f₀ y₀‖ ^ 2 : ℝ) : 𝕜) := by
        push_cast
        exact h2
      have h4 : ‖kernelFun H y₀‖ ^ 2 = ‖f₀ y₀‖ ^ 2 := RCLike.ofReal_inj.mp h3
      nlinarith [norm_nonneg (kernelFun H y₀), norm_nonneg (f₀ y₀)]
    rw [norm_smul, hnk, norm_inv, RCLike.norm_conj]
    field_simp
  · -- spanning: the closed line through `g` contains all kernel functions
    intro h
    have hker : ∀ (x : X) (w : 𝕜),
        RKHS.kerFun H x w ∈ (𝕜 ∙ ((conj (f₀ y₀))⁻¹ • kernelFun H y₀ : H)) := by
      intro x w
      have hg : (((conj (f₀ y₀))⁻¹ • kernelFun H y₀ : H) : X → 𝕜) = f₀ := by
        funext z
        have h1 : scalarKernel H z y₀ = f₀ z * conj (f₀ y₀) := by rw [hK]
        calc (((conj (f₀ y₀))⁻¹ • kernelFun H y₀ : H) : X → 𝕜) z
            = (conj (f₀ y₀))⁻¹ * (f₀ z * conj (f₀ y₀)) := by
              simp only [RKHS.coe_smul, Pi.smul_apply, smul_eq_mul]
              rw [show (kernelFun H y₀ : H) z = scalarKernel H z y₀ from rfl, h1]
          _ = f₀ z := by field_simp
      have hsm : RKHS.kerFun H x w = w • kernelFun H x := by
        rw [kernelFun, ← ContinuousLinearMap.map_smul]
        congr 1
        simp
      rw [hsm, kernelFun_rankOne_aux f₀ hK hg x, smul_smul]
      exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
    have hsub : (Submodule.span 𝕜 {v : H | ∃ (x : X) (w : 𝕜), RKHS.kerFun H x w = v})
        ≤ (𝕜 ∙ ((conj (f₀ y₀))⁻¹ • kernelFun H y₀ : H)) := by
      rw [Submodule.span_le]
      rintro v ⟨x, w, rfl⟩
      exact hker x w
    have htop : (⊤ : Submodule 𝕜 H) ≤ (𝕜 ∙ ((conj (f₀ y₀))⁻¹ • kernelFun H y₀ : H)) := by
      rw [← RKHS.kerFun_dense (𝕜 := 𝕜) (H := H) (X := X) (V := 𝕜)]
      exact Submodule.topologicalClosure_minimal _ hsub
        (Submodule.closed_of_finiteDimensional _)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (htop Submodule.mem_top)
    exact ⟨c, hc.symm⟩

/-- The kernel functions of a rank-one RKHS: `k_y = conj (f₀ y) • g` where `g` is the
unit vector representing `f₀`. -/
theorem kernelFun_of_scalarKernel_rankOne (f₀ : X → 𝕜)
    -- USER-INPUT: the kernel of `H` is the rank-one product of `f₀`
    (hK : scalarKernel H = fun x y => f₀ x * conj (f₀ y))
    {g : H} (hg : (g : X → 𝕜) = f₀) (hgnorm : ‖g‖ = 1) (y : X) :
    kernelFun H y = conj (f₀ y) • g :=
  kernelFun_rankOne_aux f₀ hK hg y

end StatLean.NonparametricStatistics
