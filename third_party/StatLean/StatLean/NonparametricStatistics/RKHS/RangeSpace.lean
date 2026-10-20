module
public import StatLean.NonparametricStatistics.RKHS.IntegralOperator
public import StatLean.NonparametricStatistics.RKHS.Basic

@[expose] public section

/-!
# The range of an integral operator is an RKHS

For a symbol `S : X → Y → 𝕜` with square-integrable sections, the range
`{T_S g : g ∈ L²(Y,μ)}` is a reproducing kernel Hilbert space on `X` with kernel
`K = S □ S*`, and its norm is the range (Sarason) norm
`‖f‖ = inf {‖g‖_{L²} : T_S g = f}`.

**Model.** The kernel of `T_S` is the orthogonal complement of the conjugated sections
`{conj S(x,·)}`, so `T_S` is injective and isometric (for the range norm) on the closed
span of those sections.  We therefore *define* the range space as that closed span
`rangeSpaceCarrier ⊆ L²(Y,μ)`, acting on `X` through `g ↦ T_S g`; the kernel function of
the point `x` is then the section `conj S(x,·)` itself, and the reproducing kernel is
`(S □ S*)`.  The classical statements (range description and infimum formula) are
derived from this model.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 11, §11.2, Theorem 11.3 (the range of an integral operator is an RKHS with kernel $S
\square S^*$ and the Sarason range norm) and Corollary 11.4; §11.2.1 identifies the Volterra
example.

**Proof formalization notes.** The range space is *modeled* as the closed span of the conjugated
sections — i.e. $(\ker T_S)^{\perp}$ — acting through $T_S$, so the Sarason norm is simply the
subspace norm and the infimum formula and its attainment become theorems about the orthogonal
decomposition of a preimage. The kernel function at $x$ is the conjugated section itself. As in
`Subspace.lean`, `rangeSpaceKernelFun`/`rangeSpaceScalarKernel` pass the carrier's `CompleteSpace`
instance explicitly (bare synthesis records an instance-transparency-incompatible uniformity).

**Bibliographic comments.** Range spaces with the lifted norm are due to D. Sarason,
*Sub-Hardy Hilbert Spaces in the Unit Disk* (Wiley, 1994); the identification of the
range of an integral operator as an RKHS goes back to N. Aronszajn, Trans. Amer. Math.
Soc. **68** (1950), §I.8.
-/

open RKHS ComplexConjugate MeasureTheory
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [MeasurableSpace Y]
variable {μ : Measure Y}

variable (μ) in
/-- The carrier of the range space of `T_S`: the closed span of the conjugated sections
`conj S(x,·)`, i.e. `(ker T_S)ᗮ ⊆ L²(Y, μ)`. -/
noncomputable def rangeSpaceCarrier (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) :
    Submodule 𝕜 (Lp 𝕜 2 μ) :=
  (Submodule.span 𝕜 (Set.range (symbolConjLp μ S hS))).topologicalClosure

instance (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) :
    IsClosed ((rangeSpaceCarrier μ S hS : Submodule 𝕜 (Lp 𝕜 2 μ)) : Set (Lp 𝕜 2 μ)) :=
  Submodule.isClosed_topologicalClosure _

variable (μ) in
/-- The RKHS structure of the range of an integral operator: an element `g` of the
closed span of the conjugated sections acts as the function `T_S g` on `X`.  Provided as
a `def` (used via `letI`), since it depends on the symbol data. -/
@[reducible]
noncomputable def rangeSpaceRKHS (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) :
    RKHS 𝕜 (rangeSpaceCarrier μ S hS) X 𝕜 where
  coeCLM :=
    (ContinuousLinearMap.pi fun x => innerSL 𝕜 (symbolConjLp μ S hS x)).comp
      (Submodule.subtypeL _)
  coeCLM_injective := by
    intro f g hfg
    have h0 : ∀ x, ⟪symbolConjLp μ S hS x,
        ((f : Lp 𝕜 2 μ) - (g : Lp 𝕜 2 μ))⟫_𝕜 = 0 := by
      intro x
      have hx := congrFun hfg x
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
        innerSL_apply_apply] at hx
      rw [inner_sub_right]
      exact sub_eq_zero.mpr hx
    have hmem : ((f : Lp 𝕜 2 μ) - (g : Lp 𝕜 2 μ)) ∈ rangeSpaceCarrier μ S hS :=
      Submodule.sub_mem _ f.2 g.2
    have hsub : rangeSpaceCarrier μ S hS ≤ (𝕜 ∙ ((f : Lp 𝕜 2 μ) - (g : Lp 𝕜 2 μ)))ᗮ := by
      refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (h0 x)
    have hz := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hsub hmem)
    have hfg0 : (f : Lp 𝕜 2 μ) - (g : Lp 𝕜 2 μ) = 0 := inner_self_eq_zero.mp hz
    exact Subtype.ext (by linear_combination (norm := module) hfg0)

/-- In the range-space model, members act by the integral operator:
`f x = T_S f (x)`. -/
theorem rangeSpace_apply (S : X → Y → 𝕜) (hS : IsL2Symbol μ S)
    (f : rangeSpaceCarrier μ S hS) (x : X) :
    letI := rangeSpaceRKHS μ S hS
    f x = integralOp μ S (f : Lp 𝕜 2 μ) x := by
  letI := rangeSpaceRKHS μ S hS
  rw [integralOp_eq_inner S hS]
  rfl

variable (μ) in
/-- Completeness of the range-space carrier, as an explicit term (closed subspace of the
complete space `L²`). -/
@[reducible]
noncomputable def rangeSpaceCompleteSpace (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) :
    CompleteSpace (rangeSpaceCarrier μ S hS) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

variable (μ) in
/-- The kernel function of the range space (definitionally
`kernelFun (rangeSpaceCarrier μ S hS)`; the instances are passed explicitly). -/
noncomputable def rangeSpaceKernelFun (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) (x : X) :
    rangeSpaceCarrier μ S hS :=
  @kernelFun 𝕜 _ X (rangeSpaceCarrier μ S hS) _ _ (rangeSpaceCompleteSpace μ S hS)
    (rangeSpaceRKHS μ S hS) x

variable (μ) in
/-- The reproducing kernel of the range space (definitionally
`scalarKernel (rangeSpaceCarrier μ S hS)`). -/
noncomputable def rangeSpaceScalarKernel (S : X → Y → 𝕜) (hS : IsL2Symbol μ S)
    (x z : X) : 𝕜 :=
  @scalarKernel 𝕜 _ X (rangeSpaceCarrier μ S hS) _ _ (rangeSpaceCompleteSpace μ S hS)
    (rangeSpaceRKHS μ S hS) x z

/-- The conjugated section at `x` belongs to the carrier (it generates it). -/
private theorem mem_rangeSpaceCarrier_symbolConjLp (S : X → Y → 𝕜) (hS : IsL2Symbol μ S)
    (x : X) : symbolConjLp μ S hS x ∈ rangeSpaceCarrier μ S hS :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x, rfl⟩)

/-- Orthogonality to every conjugated section propagates to the whole carrier: the
orthogonal complement of a singleton is closed, so it swallows the topological closure of
the span of the sections. -/
private theorem rangeSpaceCarrier_le_orthogonal (S : X → Y → 𝕜) (hS : IsL2Symbol μ S)
    (v : Lp 𝕜 2 μ) (hv : ∀ x, ⟪symbolConjLp μ S hS x, v⟫_𝕜 = 0) :
    rangeSpaceCarrier μ S hS ≤ (𝕜 ∙ v)ᗮ := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (hv x)

/-- The representative of a carrier element is a preimage of it under `T_S`. -/
private theorem integralOp_coe_eq_coe (S : X → Y → 𝕜) (hS : IsL2Symbol μ S)
    (f : rangeSpaceCarrier μ S hS) :
    letI := rangeSpaceRKHS μ S hS
    integralOp μ S (f : Lp 𝕜 2 μ) = (f : X → 𝕜) := by
  letI := rangeSpaceRKHS μ S hS
  funext x
  exact (rangeSpace_apply S hS f x).symm

/-- The kernel function of the range space at `x` is the conjugated section
`conj S(x,·)`. -/
theorem rangeSpace_kernelFun (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) (x : X) :
    (rangeSpaceKernelFun μ S hS x : Lp 𝕜 2 μ) = symbolConjLp μ S hS x := by
  have key := @inner_kernelFun 𝕜 _ X (rangeSpaceCarrier μ S hS) _ _
    (rangeSpaceCompleteSpace μ S hS) (rangeSpaceRKHS μ S hS) x
  have h : (@kernelFun 𝕜 _ X (rangeSpaceCarrier μ S hS) _ _
      (rangeSpaceCompleteSpace μ S hS) (rangeSpaceRKHS μ S hS) x)
      = ⟨symbolConjLp μ S hS x, mem_rangeSpaceCarrier_symbolConjLp S hS x⟩ :=
    ext_inner_right 𝕜 fun v => by rw [key v]; rfl
  exact congrArg Subtype.val h

/-- **The kernel of the range space is the box product** `S □ S*`. -/
theorem rangeSpace_scalarKernel (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) (x z : X) :
    rangeSpaceScalarKernel μ S hS x z = boxProd μ S (symbolAdjoint S) x z := by
  rw [boxProd_symbolAdjoint_eq_featureKernel S hS]
  change ⟪symbolConjLp μ S hS x, (rangeSpaceKernelFun μ S hS z : Lp 𝕜 2 μ)⟫_𝕜 = _
  rw [rangeSpace_kernelFun S hS z]
  rfl

/-- **The range of the integral operator equals the range space**: every `T_S g` is
realized by a member of the carrier, and conversely. -/
theorem range_integralOp_eq_range_coe (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) :
    letI := rangeSpaceRKHS μ S hS
    Set.range (integralOp μ S)
      = Set.range fun f : rangeSpaceCarrier μ S hS => (f : X → 𝕜) := by
  letI := rangeSpaceRKHS μ S hS
  haveI : CompleteSpace (rangeSpaceCarrier μ S hS) := rangeSpaceCompleteSpace μ S hS
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨g, rfl⟩
    refine ⟨⟨(rangeSpaceCarrier μ S hS).starProjection g,
      Submodule.starProjection_apply_mem _ g⟩, ?_⟩
    funext x
    have hz : ⟪symbolConjLp μ S hS x,
        g - (rangeSpaceCarrier μ S hS).starProjection g⟫_𝕜 = 0 :=
      Submodule.sub_starProjection_mem_orthogonal (K := rangeSpaceCarrier μ S hS) g
        _ (mem_rangeSpaceCarrier_symbolConjLp S hS x)
    rw [integralOp_eq_inner S hS]
    change ⟪symbolConjLp μ S hS x, (rangeSpaceCarrier μ S hS).starProjection g⟫_𝕜
        = ⟪symbolConjLp μ S hS x, g⟫_𝕜
    rw [inner_sub_right] at hz
    exact (sub_eq_zero.mp hz).symm
  · rintro _ ⟨f, rfl⟩
    exact ⟨(f : Lp 𝕜 2 μ), integralOp_coe_eq_coe S hS f⟩

/-- **The range norm is the Sarason infimum**:
`‖f‖ = inf {‖g‖_{L²} : T_S g = f}` for `f` in the range space. -/
theorem rangeSpace_norm_eq_sInf (S : X → Y → 𝕜) (hS : IsL2Symbol μ S)
    (f : rangeSpaceCarrier μ S hS) :
    letI := rangeSpaceRKHS μ S hS
    ‖f‖ = sInf (norm '' {g : Lp 𝕜 2 μ | integralOp μ S g = (f : X → 𝕜)}) := by
  letI := rangeSpaceRKHS μ S hS
  set A := {g : Lp 𝕜 2 μ | integralOp μ S g = (f : X → 𝕜)} with hA
  have hfA : (f : Lp 𝕜 2 μ) ∈ A := integralOp_coe_eq_coe S hS f
  have hlb : ∀ g ∈ A, ‖(f : Lp 𝕜 2 μ)‖ ≤ ‖g‖ := by
    intro g hg
    have h0 : ∀ x, ⟪symbolConjLp μ S hS x, g - (f : Lp 𝕜 2 μ)⟫_𝕜 = 0 := by
      intro x
      have e1 : integralOp μ S g x = ⟪symbolConjLp μ S hS x, g⟫_𝕜 :=
        integralOp_eq_inner S hS g x
      have e2 : integralOp μ S (f : Lp 𝕜 2 μ) x
          = ⟪symbolConjLp μ S hS x, (f : Lp 𝕜 2 μ)⟫_𝕜 :=
        integralOp_eq_inner S hS _ x
      rw [inner_sub_right, ← e1, ← e2, congrFun hg x,
        congrFun (integralOp_coe_eq_coe S hS f) x, sub_self]
    have horth : rangeSpaceCarrier μ S hS ≤ (𝕜 ∙ (g - (f : Lp 𝕜 2 μ)))ᗮ :=
      rangeSpaceCarrier_le_orthogonal S hS _ h0
    have hff : ⟪(f : Lp 𝕜 2 μ), g - (f : Lp 𝕜 2 μ)⟫_𝕜 = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp (horth f.2)
    have hpy : ‖g‖ ^ 2 = ‖(f : Lp 𝕜 2 μ)‖ ^ 2 + ‖g - (f : Lp 𝕜 2 μ)‖ ^ 2 := by
      conv_lhs => rw [show g = (f : Lp 𝕜 2 μ) + (g - (f : Lp 𝕜 2 μ)) by abel]
      rw [norm_add_sq (𝕜 := 𝕜), hff]
      simp
    nlinarith [norm_nonneg g, norm_nonneg (f : Lp 𝕜 2 μ),
      norm_nonneg (g - (f : Lp 𝕜 2 μ))]
  have hbdd : BddBelow (norm '' A) := ⟨0, by rintro _ ⟨g, _, rfl⟩; exact norm_nonneg _⟩
  have h1 : sInf (norm '' A) ≤ ‖(f : Lp 𝕜 2 μ)‖ := csInf_le hbdd ⟨_, hfA, rfl⟩
  have h2 : ‖(f : Lp 𝕜 2 μ)‖ ≤ sInf (norm '' A) :=
    le_csInf ⟨_, ⟨_, hfA, rfl⟩⟩ (by rintro _ ⟨g, hg, rfl⟩; exact hlb g hg)
  have hnf : ‖f‖ = ‖(f : Lp 𝕜 2 μ)‖ := rfl
  rw [hnf]
  linarith

/-- The infimum in the Sarason norm is attained, by the representative itself. -/
theorem rangeSpace_norm_attained (S : X → Y → 𝕜) (hS : IsL2Symbol μ S)
    (f : rangeSpaceCarrier μ S hS) :
    letI := rangeSpaceRKHS μ S hS
    integralOp μ S (f : Lp 𝕜 2 μ) = (f : X → 𝕜) :=
  integralOp_coe_eq_coe S hS f

end StatLean.NonparametricStatistics
