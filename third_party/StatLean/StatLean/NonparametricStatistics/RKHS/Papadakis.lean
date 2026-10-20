module
public import StatLean.NonparametricStatistics.RKHS.Basic
public import StatLean.NonparametricStatistics.RKHS.ParsevalFrame

@[expose] public section

/-!
# Parseval frames of an RKHS and pointwise kernel expansions

A family `{f_i} ⊆ H` in a scalar RKHS is a Parseval frame **iff** the reproducing kernel
expands pointwise through it: `K(x, y) = ∑ᵢ f_i(x) · conj (f_i y)`.  This generalizes the
orthonormal-basis expansion (`OrthonormalExpansion.lean`) — frames need not be linearly
independent — and is the practical tool for *recognizing* an RKHS from a series
representation of its kernel.

Forward direction: `K(x,y) = ⟪k_x, k_y⟫` and the polarized Parseval identity.  Converse:
the analysis operator is isometric on the dense span of the kernel functions, hence
extends to an isometry, which characterizes Parseval frames.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 2, §2.1, Theorem 2.10 (Papadakis' criterion: Parseval frames are exactly the
families expanding the kernel pointwise) and Remark 2.11.

**Proof formalization notes.** The forward direction is the polarized Parseval identity evaluated
at kernel functions. For the converse, the analysis operator is shown norm-nonincreasing
everywhere (partial sums are dominated on the *dense span* of the kernel functions and the
domination is a closed condition), then isometric on that dense span, hence isometric everywhere
by continuity (`Continuous.ext_on`) — the book's "isometric on a dense subspace extends" device
made explicit.

**Bibliographic comments.** Attributed to M. Papadakis; see M. Papadakis,
*On the dimension function of orthonormal wavelets*, Proc. Amer. Math. Soc. **128**
(2000), 2043–2049, and V. I. Paulsen's course notes on reproducing kernels for this
formulation.
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace ENNReal

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} {ι : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

/-- A Parseval frame of an RKHS expands the kernel pointwise:
`K(x, y) = ∑ᵢ f_i(x) · conj (f_i y)`. -/
theorem IsParsevalFrame.hasSum_scalarKernel {f : ι → H} (hf : IsParsevalFrame 𝕜 f)
    (x y : X) :
    HasSum (fun i => (f i : H) x * conj ((f i : H) y)) (scalarKernel H x y) := by
  have H0 := hf.hasSum_inner (kernelFun H x) (kernelFun H y)
  rw [← scalarKernel_eq_inner] at H0
  simpa [inner_kernelFun, inner_kernelFun_right] using H0

/-! ### Auxiliary material for the converse -/

omit [CompleteSpace H] in
/-- `⟪h, f i⟫ · ⟪f i, h⟫` is the real scalar `‖⟪f i, h⟫‖²`. -/
private theorem inner_mul_inner_self' (f : ι → H) (h : H) (i : ι) :
    ⟪h, f i⟫_𝕜 * ⟪f i, h⟫_𝕜 = ((‖⟪f i, h⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← inner_conj_symm (𝕜 := 𝕜) (f i) h, RCLike.mul_conj, RCLike.norm_conj]
  norm_cast

omit [CompleteSpace H] in
/-- `⟪h, h⟫` is the real scalar `‖h‖²`. -/
private theorem inner_self_ofReal' (h : H) : ⟪h, h⟫_𝕜 = ((‖h‖ ^ 2 : ℝ) : 𝕜) := by
  rw [inner_self_eq_norm_sq_to_K]; push_cast; ring

omit [CompleteSpace H] in
/-- The `𝕜`-valued Parseval identity at `h` implies its real form. -/
private theorem hasSum_sq_of_hasSum_inner {f : ι → H} {h : H}
    (H0 : HasSum (fun i => ⟪h, f i⟫_𝕜 * ⟪f i, h⟫_𝕜) ⟪h, h⟫_𝕜) :
    HasSum (fun i => ‖⟪f i, h⟫_𝕜‖ ^ 2) (‖h‖ ^ 2) := by
  have := H0.mapL (RCLike.reCLM (K := 𝕜))
  simpa only [Function.comp_def, RCLike.reCLM_apply, inner_mul_inner_self', inner_self_ofReal',
    RCLike.ofReal_re] using this

/-- The defining `HasSum` of the `ℓ²` norm, specialized to `p = 2`. -/
private theorem lp2_hasSum_sq' (x : lp (fun _ : ι => 𝕜) 2) :
    HasSum (fun i => ‖x i‖ ^ 2) (‖x‖ ^ 2) := by
  have h2 : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  simpa using lp.hasSum_norm h2 x

/-- The span of the kernel functions `k_x` is dense in a scalar RKHS. -/
private theorem dense_span_kernelFun :
    Dense ((Submodule.span 𝕜 (Set.range (kernelFun (𝕜 := 𝕜) (X := X) H)) : Submodule 𝕜 H) :
      Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  have hle : Submodule.span 𝕜 {y : H | ∃ (x : X) (v : 𝕜), RKHS.kerFun H x v = y}
      ≤ Submodule.span 𝕜 (Set.range (kernelFun (𝕜 := 𝕜) (X := X) H)) := by
    rw [Submodule.span_le]
    rintro y ⟨x, v, rfl⟩
    have hv : RKHS.kerFun H x v = v • kernelFun (𝕜 := 𝕜) H x := by
      change RKHS.kerFun H x v = v • RKHS.kerFun H x 1
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hmono := Submodule.topologicalClosure_mono hle
  rw [RKHS.kerFun_dense] at hmono
  exact top_le_iff.1 hmono

/-- The polarized Parseval identity is sesquilinear, hence propagates from the kernel functions
to their linear span. -/
private theorem hasSum_inner_of_mem_span {f : ι → H}
    (hker : ∀ x y : X,
      HasSum (fun i => ⟪kernelFun (𝕜 := 𝕜) H x, f i⟫_𝕜 * ⟪f i, kernelFun (𝕜 := 𝕜) H y⟫_𝕜)
        ⟪kernelFun (𝕜 := 𝕜) H x, kernelFun (𝕜 := 𝕜) H y⟫_𝕜)
    {a b : H}
    (ha : a ∈ Submodule.span 𝕜 (Set.range (kernelFun (𝕜 := 𝕜) (X := X) H)))
    (hb : b ∈ Submodule.span 𝕜 (Set.range (kernelFun (𝕜 := 𝕜) (X := X) H))) :
    HasSum (fun i => ⟪a, f i⟫_𝕜 * ⟪f i, b⟫_𝕜) ⟪a, b⟫_𝕜 := by
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem u v hu hv =>
      obtain ⟨x, rfl⟩ := hu
      obtain ⟨y, rfl⟩ := hv
      exact hker x y
  | zero_left v hv => simp
  | zero_right u hu => simp
  | add_left u v w hu hv hw h1 h2 => simpa [inner_add_left, add_mul] using h1.add h2
  | add_right u v w hu hv hw h1 h2 => simpa [inner_add_right, mul_add] using h1.add h2
  | smul_left c u v hu hv h1 =>
      simpa [inner_smul_left, mul_assoc] using h1.mul_left (conj c)
  | smul_right c u v hu hv h1 =>
      simpa [inner_smul_right, mul_left_comm] using h1.mul_left c

/-- **Papadakis' criterion**, converse direction: if a family of members of `H` expands
the kernel pointwise, it is a Parseval frame for `H`. -/
theorem isParsevalFrame_of_hasSum_scalarKernel {f : ι → H}
    -- USER-INPUT: pointwise expansion of the kernel through the family
    (hexp : ∀ x y, HasSum (fun i => (f i : H) x * conj ((f i : H) y)) (scalarKernel H x y)) :
    IsParsevalFrame 𝕜 f := by
  -- Step 1: the hypothesis is the polarized Parseval identity on the kernel functions.
  have hker : ∀ x y : X,
      HasSum (fun i => ⟪kernelFun (𝕜 := 𝕜) H x, f i⟫_𝕜 * ⟪f i, kernelFun (𝕜 := 𝕜) H y⟫_𝕜)
        ⟪kernelFun (𝕜 := 𝕜) H x, kernelFun (𝕜 := 𝕜) H y⟫_𝕜 := by
    intro x y
    rw [← scalarKernel_eq_inner]
    simpa [inner_kernelFun, inner_kernelFun_right] using hexp x y
  -- Step 2: hence the (real) Parseval identity holds on the span of the kernel functions.
  have hspan : ∀ h ∈ Submodule.span 𝕜 (Set.range (kernelFun (𝕜 := 𝕜) (X := X) H)),
      HasSum (fun i => ‖⟪f i, h⟫_𝕜‖ ^ 2) (‖h‖ ^ 2) :=
    fun h hh => hasSum_sq_of_hasSum_inner (hasSum_inner_of_mem_span hker hh hh)
  -- Step 3: each partial sum is dominated by `‖·‖²` on the span, hence — being continuous —
  -- everywhere.
  have hbdd : ∀ (h : H) (s : Finset ι), ∑ i ∈ s, ‖⟪f i, h⟫_𝕜‖ ^ 2 ≤ ‖h‖ ^ 2 := by
    intro h s
    have hc : IsClosed {z : H | ∑ i ∈ s, ‖⟪f i, z⟫_𝕜‖ ^ 2 ≤ ‖z‖ ^ 2} := by
      refine isClosed_le (continuous_finset_sum s fun i _ => ?_) (continuous_norm.pow 2)
      exact ((innerSL 𝕜 (f i)).continuous.norm).pow 2
    have hsub : ((Submodule.span 𝕜 (Set.range (kernelFun (𝕜 := 𝕜) (X := X) H)) :
        Submodule 𝕜 H) : Set H) ⊆ {z : H | ∑ i ∈ s, ‖⟪f i, z⟫_𝕜‖ ^ 2 ≤ ‖z‖ ^ 2} :=
      fun z hz => sum_le_hasSum s (fun i _ => by positivity) (hspan z hz)
    have hall := hc.closure_subset_iff.2 hsub
    rw [(dense_span_kernelFun (𝕜 := 𝕜) (X := X) (H := H)).closure_eq] at hall
    exact hall (Set.mem_univ h)
  -- Step 4: the analysis operator is therefore a norm-nonincreasing linear map into `ℓ²(ι)`.
  have hmem : ∀ h : H, Memℓp (fun i => ⟪f i, h⟫_𝕜) 2 := fun h =>
    memℓp_gen' (C := ‖h‖ ^ 2) (fun s => by simpa using hbdd h s)
  let A : H →ₗ[𝕜] lp (fun _ : ι => 𝕜) 2 :=
    { toFun := fun h => ⟨fun i => ⟪f i, h⟫_𝕜, hmem h⟩
      map_add' := by intro x y; ext i; simp only [inner_add_right]; rfl
      map_smul' := by intro c x; ext i; simp [inner_smul_right, Pi.smul_apply] }
  have hA : ∀ (h : H) (i : ι), (A h) i = ⟪f i, h⟫_𝕜 := fun _ _ => rfl
  have hAle : ∀ h : H, ‖A h‖ ≤ 1 * ‖h‖ := by
    intro h
    rw [one_mul]
    have h1 := lp2_hasSum_sq' (A h)
    simp only [hA] at h1
    have h2 : ‖A h‖ ^ 2 ≤ ‖h‖ ^ 2 := hasSum_le_of_sum_le h1 (hbdd h)
    have h3 := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3
  -- Step 5: it is isometric on the (dense) span, hence isometric everywhere by continuity.
  have hcont : Continuous fun h : H => ‖A h‖ :=
    continuous_norm.comp (A.mkContinuous 1 hAle).continuous
  have heq : (fun h : H => ‖A h‖) = fun h : H => ‖h‖ := by
    refine Continuous.ext_on (dense_span_kernelFun (𝕜 := 𝕜) (X := X) (H := H)) hcont
      continuous_norm ?_
    intro z hz
    have h1 := lp2_hasSum_sq' (A z)
    simp only [hA] at h1
    have h2 := h1.unique (hspan z hz)
    change ‖A z‖ = ‖z‖
    rw [← Real.sqrt_sq (norm_nonneg (A z)), h2, Real.sqrt_sq (norm_nonneg z)]
  -- Step 6: read the Parseval identity back off the `ℓ²` norm.
  intro h
  have h1 := lp2_hasSum_sq' (A h)
  simp only [hA] at h1
  have h2 : ‖A h‖ = ‖h‖ := congrFun heq h
  rwa [h2] at h1

/-- **Papadakis' criterion**: a family in an RKHS is a Parseval frame iff it expands the
reproducing kernel pointwise. -/
theorem isParsevalFrame_iff_hasSum_scalarKernel {f : ι → H} :
    IsParsevalFrame 𝕜 f
      ↔ ∀ x y, HasSum (fun i => (f i : H) x * conj ((f i : H) y)) (scalarKernel H x y) :=
  ⟨fun hf => hf.hasSum_scalarKernel, isParsevalFrame_of_hasSum_scalarKernel⟩

end StatLean.NonparametricStatistics
