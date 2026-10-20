module
public import StatLean.NonparametricStatistics.RKHS.IntegralOperator
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

/-!
# Mercer kernels and their integral operators

A **Mercer kernel** on a compact metric space `X` is a continuous kernel function
`K : X → X → 𝕜`.  Against a finite Borel measure `μ` on `X`, such a kernel induces the
integral operator `T_K g (x) = ∫ K(x,y) g(y) dμ(y)`, which we package as a continuous
linear endomorphism `mercerCLM` of `L²(X, μ)` (continuity of `K` on the compact square
gives boundedness of the sections uniformly in `x`).

The `L²`-endomorphism only needs continuity of `K`, not positivity, so `mercerCLM` is
defined from a `Continuous` hypothesis alone — the converse direction of Mercer theory
(positivity of `T_K` implies positivity of `K`) then makes sense.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 11, §11.3, Definition 11.5 (Mercer kernels) and the associated integral operator on
$L^2(X,\mu)$ (the boundedness computation of Proposition 11.9).

**Proof formalization notes.** `mercerCLM` is defined from joint continuity alone — positivity is
*not* assumed — so the converse direction of Mercer theory (Proposition 11.11) is well-posed. The
`L²`-valued operator is assembled by `LinearMap.mkContinuousOfExistsBound` with a
dominated-convergence proof that images are continuous, a uniform bound from compactness of $X
\times X$, and linearity read off the inner-product form `integralOp_eq_inner`.

**Bibliographic comments.** J. Mercer, *Functions of positive and negative type and
their connection with the theory of integral equations*, Philos. Trans. Roy. Soc. A
**209** (1909), 415–446.
-/

open ComplexConjugate MeasureTheory
open scoped InnerProductSpace ENNReal NNReal

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]

variable (𝕜) in
/-- **Mercer kernel**: a jointly continuous kernel function on a compact metric space. -/
structure IsMercerKernel (K : X → X → 𝕜) : Prop where
  /-- Joint continuity on `X × X`.  Constitutive: continuity is what upgrades the
  spectral expansion to uniform convergence. -/
  continuous : Continuous fun p : X × X => K p.1 p.2
  /-- Positive semidefiniteness. -/
  isKernelFun : IsKernelFun K

omit [MeasurableSpace X] [BorelSpace X] in
/-- A continuous kernel on a compact square is uniformly bounded. -/
private theorem exists_bound_of_continuous {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x y : X, ‖K x y‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun p : X × X => K p.1 p.2) hKc.continuousOn
  exact ⟨max M 0, le_max_right _ _,
    fun x y => le_trans (hM (x, y) (Set.mem_univ _)) (le_max_left _ _)⟩

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Sections of a jointly continuous kernel are continuous. -/
private theorem continuous_section {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) (x : X) :
    Continuous fun y => K x y :=
  hKc.comp (continuous_const.prodMk continuous_id)

variable {μ : Measure X} [IsFiniteMeasure μ]

/-- Sections of a jointly continuous kernel are square-integrable against a finite Borel
measure. -/
theorem isL2Symbol_of_continuous {K : X → X → 𝕜}
    -- USER-INPUT: joint continuity of the kernel
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    IsL2Symbol μ K := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_continuous hKc
  exact fun x => MemLp.of_bound (continuous_section hKc x).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun y => hM x y)

/-- The integral operator of a continuous kernel is continuous (dominated convergence:
the sections are uniformly bounded and `g ∈ L² ⊆ L¹` for a finite measure). -/
private theorem continuous_integralOp {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) (g : Lp 𝕜 2 μ) :
    Continuous (integralOp μ K g) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_continuous hKc
  have hgi : Integrable (g : X → 𝕜) μ := (Lp.memLp g).integrable (by norm_num)
  refine continuous_of_dominated (bound := fun y => M * ‖(g : X → 𝕜) y‖) ?_ ?_ ?_ ?_
  · exact fun x =>
      ((continuous_section hKc x).aestronglyMeasurable).mul (Lp.aestronglyMeasurable g)
  · intro x
    filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM x y) (norm_nonneg _)
  · exact hgi.norm.const_mul M
  · filter_upwards with y
    exact (hKc.comp (continuous_id.prodMk continuous_const)).mul continuous_const

/-- The uniform pointwise bound on the integral operator of a continuous kernel. -/
private theorem norm_integralOp_le_of_continuous {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x y : X, ‖K x y‖ ≤ M) (g : Lp 𝕜 2 μ) (x : X) :
    ‖integralOp μ K g x‖
      ≤ ((measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * M) * ‖g‖ := by
  refine le_trans (norm_integralOp_le K (isL2Symbol_of_continuous hKc) g x) ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg g)
  refine Lp.norm_le_of_ae_bound hM0 ?_
  filter_upwards [MemLp.coeFn_toLp (μ := μ) (p := 2)
    ((IsL2Symbol.conj K (isL2Symbol_of_continuous hKc)) x)] with y hy
  rw [show ((symbolConjLp μ K (isL2Symbol_of_continuous hKc) x : Lp 𝕜 2 μ) : X → 𝕜) y
      = conj (K x y) from hy, RCLike.norm_conj]
  exact hM x y

/-- The integral operator of a continuous kernel produces square-integrable functions. -/
theorem memLp_integralOp_of_continuous {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) (g : Lp 𝕜 2 μ) :
    MemLp (integralOp μ K g) 2 μ := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_continuous hKc
  exact MemLp.of_bound (continuous_integralOp hKc g).aestronglyMeasurable _
    (Filter.Eventually.of_forall fun x =>
      norm_integralOp_le_of_continuous hKc hM0 hM g x)

variable (μ) in
/-- **The Mercer integral operator** `T_K : L²(X,μ) → L²(X,μ)`,
`T_K g = [x ↦ ∫ K(x,y) g(y) dμ(y)]`.  Defined for any jointly continuous `K`. -/
noncomputable def mercerCLM {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun g => (memLp_integralOp_of_continuous hKc g).toLp _
      map_add' := by
        intro g h
        rw [← MemLp.toLp_add]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 (Filter.Eventually.of_forall fun x => ?_)
        change integralOp μ K (g + h) x = integralOp μ K g x + integralOp μ K h x
        rw [integralOp_eq_inner K (isL2Symbol_of_continuous hKc),
          integralOp_eq_inner K (isL2Symbol_of_continuous hKc),
          integralOp_eq_inner K (isL2Symbol_of_continuous hKc), inner_add_right]
      map_smul' := by
        intro c g
        change (memLp_integralOp_of_continuous hKc (c • g)).toLp _
          = c • (memLp_integralOp_of_continuous hKc g).toLp _
        rw [← MemLp.toLp_const_smul]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 (Filter.Eventually.of_forall fun x => ?_)
        change integralOp μ K (c • g) x = c • integralOp μ K g x
        rw [integralOp_eq_inner K (isL2Symbol_of_continuous hKc),
          integralOp_eq_inner K (isL2Symbol_of_continuous hKc), inner_smul_right,
          smul_eq_mul] }
    (by
      obtain ⟨M, hM0, hM⟩ := exists_bound_of_continuous (K := K) hKc
      refine ⟨(measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ *
        ((measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * M), fun g => ?_⟩
      rw [mul_assoc]
      refine Lp.norm_le_of_ae_bound (by positivity) ?_
      filter_upwards [MemLp.coeFn_toLp (μ := μ) (p := 2)
        (memLp_integralOp_of_continuous hKc g)] with x hx
      change ‖(((memLp_integralOp_of_continuous hKc g).toLp (integralOp μ K g) :
        Lp 𝕜 2 μ) : X → 𝕜) x‖ ≤ _
      rw [hx]
      exact norm_integralOp_le_of_continuous hKc hM0 hM g x)

/-- The defining almost-everywhere description of `mercerCLM`. -/
theorem mercerCLM_coeFn_ae {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) (g : Lp 𝕜 2 μ) :
    (mercerCLM μ hKc g : X → 𝕜) =ᵐ[μ] integralOp μ K g :=
  MemLp.coeFn_toLp (memLp_integralOp_of_continuous hKc g)

/-- Inner products against `T_K g` can be computed through the pointwise formula. -/
theorem inner_mercerCLM {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) (g h : Lp 𝕜 2 μ) :
    ⟪h, mercerCLM μ hKc g⟫_𝕜 = ∫ x, conj (h x) * integralOp μ K g x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mercerCLM_coeFn_ae hKc g] with x hx
  rw [RCLike.inner_apply, hx, mul_comm]

end StatLean.NonparametricStatistics
