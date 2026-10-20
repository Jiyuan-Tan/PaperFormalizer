module
public import StatLean.HighDimensionalStatistics.MEstimator.GoodEvent
public import StatLean.HighDimensionalStatistics.MEstimator.L1Decomposable
public import StatLean.HighDimensionalStatistics.MEstimator.Bound
public import StatLean.HighDimensionalStatistics.MEstimator.DualBound
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# GLM Lasso estimation-error rates (Wainwright Corollaries 9.26, 9.27)

Consider a sparse generalized linear model: the response `yᵢ` follows an exponential family with
natural parameter `⟨xᵢ, θ*⟩`, where the true coefficient vector `θ* ∈ ℝ^d` is supported on a set
`S` of size `s = |S|`. The GLM negative log-likelihood is `Lₙ(θ) = (1/n)∑ᵢ[ψ(⟨xᵢ,θ⟩) − yᵢ⟨xᵢ,θ⟩]`,
where `ψ` is the cumulant (partition) function with `0 ≤ ψ'' ≤ B²`, and `θ̂` is the
`ℓ₁`-regularized (Lasso) estimator minimizing `Lₙ(θ) + λ‖θ‖₁`.

Assume the columns of the design are normalized at level `C`, the loss satisfies a restricted
strong convexity (RSC) condition at `θ*` with curvature `κ`, and the regularization parameter is
tuned at `λ = 4BC(√(log d / n) + δ)`. Then, with probability at least `1 − 2e^{−2nδ²}`:

* **(Corollary 9.26, ℓ₂/ℓ₁ rates)**
  `‖θ̂ − θ*‖₂² ≲ s λ² / κ²` and `‖θ̂ − θ*‖₁ ≲ s λ / κ`; and
* **(Corollary 9.27, ℓ∞ rate)** under an additional `ℓ∞`-curvature condition,
  `‖θ̂ − θ*‖∞ ≤ 3λ / κ`.

The proof instantiates the deterministic decomposable-regularizer bounds (Corollary 9.20 for
`ℓ₂`/`ℓ₁`, Theorem 9.24 for `ℓ∞`) at the `ℓ₁/ℓ∞` decomposable regularizer `l1DecomposableReg S`,
whose subspace Lipschitz constant is `Ψ(M(S)) = √s`, and combines them with the high-probability
good event (`good_event_highProb`) controlling `‖∇Lₙ(θ*)‖∞`.

The RSC condition (9.62) and the `ℓ∞`-curvature condition (9.64) enter as `USER-INPUT` hypotheses —
the book establishes them separately (Theorem 9.36, for sub-Gaussian covariates), which is out of
scope for this file.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019, Chapter 9 (Decomposability and restricted strong convexity),
§9.5.1 (Generalized linear models with sparsity), Corollary 9.26 (`ℓ₂`/`ℓ₁` bounds) and
Corollary 9.27 (`ℓ∞` bound, condition Eq (9.64)); RSC condition Eq (9.62); tuning
`λ = 4BC(√(log d / n) + δ)`.

**Proof formalization notes.**
* Constant deviation: the deterministic `ℓ₂`/`ℓ₁` constants are the provable `144`/`48`
  (see `Bound.lean`), vs. the book's `9/4`/`6`; the `s λ² / κ²` and `s λ / κ` rates are unchanged.
* Tuning note (Cor 9.27): the `ℓ∞` corollary reuses the SAME `λ = 4BC(√(log d / n) + δ)` as
  Cor 9.26, because the good-event high-probability bound `good_event_highProb` (which establishes
  `P(‖∇Lₙ(θ*)‖∞ ≤ λ/2) ≥ 1 − 2e^{−2nδ²}`) requires `λ ≥ 4BC(√(log d / n) + δ)`; the smaller `2BC`
  constant sometimes quoted alongside Thm 9.24 only governs the deterministic `ℓ∞` rate, not this
  probability level.

**Bibliographic comments.** These corollaries are the GLM specialization of the unified
decomposable-regularizer M-estimation framework of S. N. Negahban, P. Ravikumar, M. J. Wainwright
& B. Yu, "A unified framework for high-dimensional analysis of M-estimators with decomposable
regularizers", *Statistical Science* **27**(4):538–557, 2012. That paper introduces decomposability
of a regularizer relative to a subspace pair `(M, M̄^⊥)`, the restricted strong convexity
condition, and the master deterministic bound (their Theorem 1), of which the `ℓ₂`/`ℓ₁` rates here
are the `ℓ₁`-regularizer instance (their Corollary 5 specializes Theorem 1 to the Lasso, including
the `√s` subspace constant for `s`-sparse vectors). The `ℓ∞` bound of Corollary 9.27 follows the
later refinement using a primal-dual / curvature argument developed in Wainwright's textbook
treatment rather than the original 2012 paper. Wainwright's Chapter 9 is the textbook synthesis of
this line of work.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

variable {n d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## The `ℓ₁/ℓ∞` subspace Lipschitz constant -/

/-- **Subspace Lipschitz constant of `ℓ₁` over `M(S)` is `√s`** (Wainwright §9.4, p.279):
`Ψ(M(S)) = sup_{u∈M(S), ‖u‖₂≤1} ‖u‖₁ = √|S|`. From `l1Norm_restrict_le_sqrt_card_mul_norm`. -/
theorem subspaceLip_l1_suppSubmodule (S : Finset (Fin d)) :
    subspaceLip (l1Seminorm d) (suppSubmodule S) = Real.sqrt S.card := by
  have hcoe : ∀ v : EuclideanSpace ℝ (Fin d), (l1Seminorm d) v = l1Norm v := fun _ => rfl
  -- Every ratio `Φ(v)/‖v‖` for `v ∈ M(S) \ {0}` is `≤ √s`.
  have hub : ∀ a ∈ ((fun u => (l1Seminorm d) u / ‖u‖) ''
        ((↑(suppSubmodule S) : Set (EuclideanSpace ℝ (Fin d))) \ {0})), a ≤ Real.sqrt S.card := by
    rintro a ⟨v, ⟨hv, hv0⟩, rfl⟩
    have hv0' : v ≠ 0 := by simpa using hv0
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0'
    change l1Norm v / ‖v‖ ≤ Real.sqrt S.card
    rw [div_le_iff₀ hvnorm]
    have hres : restrict S v = v := restrict_eq_self S v (fun i hi => hv i hi)
    calc l1Norm v = l1Norm (restrict S v) := by rw [hres]
      _ ≤ Real.sqrt S.card * ‖v‖ := l1Norm_restrict_le_sqrt_card_mul_norm S v
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · -- `S = ∅`: the subspace is `{0}`, the ratio set is empty, both sides `0`.
    subst hSe
    rw [Finset.card_empty, Nat.cast_zero, Real.sqrt_zero]
    unfold subspaceLip
    rw [show ((fun u => (l1Seminorm d) u / ‖u‖) ''
          ((↑(suppSubmodule (∅ : Finset (Fin d))) :
            Set (EuclideanSpace ℝ (Fin d))) \ {0})) = ∅ from ?_, Real.sSup_empty]
    rw [Set.eq_empty_iff_forall_notMem]
    rintro a ⟨u, ⟨hu, hu0⟩, rfl⟩
    refine hu0 ?_
    rw [Set.mem_singleton_iff]
    apply WithLp.ofLp_injective 2
    funext j
    simpa using hu j (Finset.notMem_empty j)
  · -- `S ≠ ∅`: the indicator vector `∑_{j∈S} eⱼ` achieves the ratio `√s`.
    obtain ⟨j0, hj0⟩ := hSne
    set u : EuclideanSpace ℝ (Fin d) :=
      WithLp.toLp 2 (fun i => if i ∈ S then (1 : ℝ) else 0) with hu_def
    have huof : ∀ i, u.ofLp i = if i ∈ S then (1 : ℝ) else 0 := fun i => by
      rw [hu_def, WithLp.ofLp_toLp]
    have hmem : u ∈ suppSubmodule S := by intro j hj; rw [huof, if_neg hj]
    have hune : u ≠ 0 := by
      intro h
      have h0 : u.ofLp j0 = 0 := by rw [h]; simp
      rw [huof, if_pos hj0] at h0; exact one_ne_zero h0
    have hl1 : l1Norm u = (S.card : ℝ) := by
      unfold l1Norm
      rw [show (∑ i, |u.ofLp i|) = ∑ i, (if i ∈ S then (1 : ℝ) else 0) from
        Finset.sum_congr rfl fun i _ => by rw [huof]; split_ifs <;> norm_num]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hnorm_sq : ∑ i, |u.ofLp i| ^ 2 = (S.card : ℝ) := by
      rw [show (∑ i, |u.ofLp i| ^ 2) = ∑ i, (if i ∈ S then (1 : ℝ) else 0) from
        Finset.sum_congr rfl fun i _ => by rw [huof]; split_ifs <;> norm_num]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hnorm : ‖u‖ = Real.sqrt S.card := by
      rw [EuclideanSpace.norm_eq, ← hnorm_sq]
      congr 1
    have hcard_pos : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨j0, hj0⟩
    have hratio : (l1Seminorm d) u / ‖u‖ = Real.sqrt S.card := by
      rw [hcoe, hl1, hnorm, div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hcard_pos)),
          Real.mul_self_sqrt hcard_pos.le]
    have hmem_set : Real.sqrt S.card ∈ ((fun u => (l1Seminorm d) u / ‖u‖) ''
        ((↑(suppSubmodule S) : Set (EuclideanSpace ℝ (Fin d))) \ {0})) :=
      ⟨u, ⟨hmem, by simpa using hune⟩, hratio⟩
    unfold subspaceLip
    refine le_antisymm (Real.sSup_le hub (Real.sqrt_nonneg _)) ?_
    exact le_csSup ⟨Real.sqrt S.card, hub⟩ hmem_set

/-! ## Calculus of the GLM cost: convexity, differentiability, gradient

The GLM cost `Lₙ(θ) = (1/n)∑ᵢ[ψ(⟨xᵢ,θ⟩) − yᵢ⟨xᵢ,θ⟩]` is built from the per-row affine map
`θ ↦ ⟨xᵢ, θ⟩`, realized here as `θ ↦ ⟪rowVec M i, θ⟫`. -/

/-- The `i`-th row of the design as a vector in `EuclideanSpace ℝ (Fin d)`. -/
private def rowVec (M : GLMExpFamily n d μ) (i : Fin n) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => M.X i j)

private lemma rowVec_ofLp (M : GLMExpFamily n d μ) (i : Fin n) (j : Fin d) :
    (rowVec M i).ofLp j = M.X i j := by
  simp only [rowVec, WithLp.ofLp_toLp]

/-- The linear predictor as an inner product: `⟪rowᵢ, θ⟫ = linPred X θ i`. -/
private lemma inner_rowVec (M : GLMExpFamily n d μ) (i : Fin n) (θ : EuclideanSpace ℝ (Fin d)) :
    ⟪rowVec M i, θ⟫_ℝ = linPred M.X θ i := by
  rw [PiLp.inner_apply]
  unfold linPred
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rowVec_ofLp]
  change θ.ofLp j * M.X i j = M.X i j * θ.ofLp j
  ring

/-- The `i`-th summand of the GLM cost (written via the inner product). -/
private noncomputable def glmSummand (M : GLMExpFamily n d μ) (ω : Ω) (i : Fin n)
    (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  M.ψ (⟪rowVec M i, θ⟫_ℝ) - M.y i ω * ⟪rowVec M i, θ⟫_ℝ

private lemma glmCost_eq_sum (M : GLMExpFamily n d μ) (ω : Ω) :
    glmCost M ω = fun θ => (1 / (n : ℝ)) * ∑ i, glmSummand M ω i θ := by
  funext θ
  simp only [glmCost, glmSummand]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [inner_rowVec]

/-- The partition function `ψ` is convex (`ψ'' ≥ 0`, so `ψ'` is monotone). -/
private lemma psi_convexOn (M : GLMExpFamily n d μ) : ConvexOn ℝ Set.univ M.ψ := by
  have hψ_diff : Differentiable ℝ M.ψ := fun a => (M.hψ' a).differentiableAt
  have hψ'_diff : Differentiable ℝ M.ψ' := fun a => (M.hψ'' a).differentiableAt
  have hderivψ : deriv M.ψ = M.ψ' := funext fun a => (M.hψ' a).deriv
  have hderivψ' : deriv M.ψ' = M.ψ'' := funext fun a => (M.hψ'' a).deriv
  have hψ'_mono : Monotone M.ψ' := by
    apply monotone_of_deriv_nonneg hψ'_diff
    rw [hderivψ']; exact M.hψ''_nonneg
  exact Monotone.convexOn_univ_of_deriv hψ_diff (by rw [hderivψ]; exact hψ'_mono)

private lemma glmSummand_convexOn (M : GLMExpFamily n d μ) (ω : Ω) (i : Fin n) :
    ConvexOn ℝ Set.univ (glmSummand M ω i) := by
  have hcomp : ConvexOn ℝ Set.univ
      (M.ψ ∘ ⇑(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i)).toLinearMap) := by
    have h := (psi_convexOn M).comp_linearMap
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i)).toLinearMap
    rwa [Set.preimage_univ] at h
  have hlin : ConvexOn ℝ Set.univ
      (⇑((-M.y i ω) •
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i)).toLinearMap)) :=
    LinearMap.convexOn _ convex_univ
  have hadd := hcomp.add hlin
  have heq : glmSummand M ω i
      = (M.ψ ∘ ⇑(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i)).toLinearMap)
        + ⇑((-M.y i ω) •
            (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i)).toLinearMap) := by
    funext θ
    simp only [glmSummand, Function.comp_apply, Pi.add_apply, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, InnerProductSpace.toDual_apply_apply, smul_eq_mul]
    ring
  rw [heq]; exact hadd

/-- **The GLM cost `glmCost M ω` is convex** (its Hessian is `(1/n)∑ᵢ ψ''(⟨xᵢ,θ⟩) xᵢxᵢᵀ ⪰ 0` since
`ψ'' ≥ 0`). -/
theorem glmCost_convexOn (M : GLMExpFamily n d μ) (ω : Ω) :
    ConvexOn ℝ Set.univ (glmCost M ω) := by
  have hsum : ∀ s : Finset (Fin n),
      ConvexOn ℝ Set.univ (fun θ => ∑ i ∈ s, glmSummand M ω i θ) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using convexOn_const (0 : ℝ) convex_univ
    · intro a t ha ih
      have hrw : (fun θ => ∑ i ∈ insert a t, glmSummand M ω i θ)
          = (fun θ => glmSummand M ω a θ) + (fun θ => ∑ i ∈ t, glmSummand M ω i θ) := by
        funext θ; rw [Finset.sum_insert ha]; rfl
      rw [hrw]
      exact (glmSummand_convexOn M ω a).add ih
  rw [glmCost_eq_sum]
  have h := (hsum Finset.univ).smul (show (0 : ℝ) ≤ 1 / (n : ℝ) from by positivity)
  simpa only [smul_eq_mul] using h

private lemma glmSummand_differentiable (M : GLMExpFamily n d μ) (ω : Ω) (i : Fin n) :
    Differentiable ℝ (glmSummand M ω i) := by
  have hg : Differentiable ℝ (fun θ : EuclideanSpace ℝ (Fin d) => ⟪rowVec M i, θ⟫_ℝ) :=
    Differentiable.inner ℝ (differentiable_const _) differentiable_id
  have hψ_diff : Differentiable ℝ M.ψ := fun a => (M.hψ' a).differentiableAt
  have h := (hψ_diff.comp hg).sub (hg.const_mul (M.y i ω))
  have heq : glmSummand M ω i
      = (M.ψ ∘ (fun θ : EuclideanSpace ℝ (Fin d) => ⟪rowVec M i, θ⟫_ℝ))
        - (fun θ => M.y i ω * ⟪rowVec M i, θ⟫_ℝ) := by
    funext θ; simp only [glmSummand, Function.comp_apply, Pi.sub_apply]
  rw [heq]; exact h

/-- **The GLM cost `glmCost M ω` is differentiable.** -/
theorem glmCost_differentiable (M : GLMExpFamily n d μ) (ω : Ω) :
    Differentiable ℝ (glmCost M ω) := by
  rw [glmCost_eq_sum]
  exact (Differentiable.fun_sum (fun i _ => glmSummand_differentiable M ω i)).const_mul _

/-- Fréchet derivative of the `i`-th summand at `θ*`: `ψ'(ηᵢ)·rowᵢᵀ − yᵢ·rowᵢᵀ` (chain rule). -/
private lemma glmSummand_hasFDerivAt (M : GLMExpFamily n d μ) (ω : Ω) (i : Fin n) :
    HasFDerivAt (glmSummand M ω i)
      ((M.ψ' (⟪rowVec M i, M.θstar⟫_ℝ) •
          InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i))
        - (M.y i ω • InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i)))
      M.θstar := by
  have hg : HasFDerivAt (fun θ : EuclideanSpace ℝ (Fin d) => ⟪rowVec M i, θ⟫_ℝ)
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i)) M.θstar := by
    have hfun : (fun θ : EuclideanSpace ℝ (Fin d) => ⟪rowVec M i, θ⟫_ℝ)
        = ⇑(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i)) := by
      funext θ; rw [InnerProductSpace.toDual_apply_apply]
    rw [hfun]; exact ContinuousLinearMap.hasFDerivAt _
  have h1 := (M.hψ' (⟪rowVec M i, M.θstar⟫_ℝ)).comp_hasFDerivAt M.θstar hg
  have h2 := hg.const_mul (M.y i ω)
  exact h1.sub h2

/-- Fréchet derivative of the whole GLM cost at `θ*`. -/
private lemma glmCost_hasFDerivAt (M : GLMExpFamily n d μ) (ω : Ω) :
    HasFDerivAt (glmCost M ω)
      ((1 / (n : ℝ)) • ∑ i, ((M.ψ' (⟪rowVec M i, M.θstar⟫_ℝ) •
            InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i))
          - (M.y i ω • InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i))))
      M.θstar := by
  have hsum : HasFDerivAt (fun θ => ∑ i, glmSummand M ω i θ)
      (∑ i, ((M.ψ' (⟪rowVec M i, M.θstar⟫_ℝ) •
            InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i))
          - (M.y i ω • InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i))))
      M.θstar := by
    have h := HasFDerivAt.sum (fun i (_ : i ∈ Finset.univ) => glmSummand_hasFDerivAt M ω i)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun θ => ?_)
    simp only [Finset.sum_apply]
  have h := hsum.const_mul (1 / (n : ℝ))
  rw [glmCost_eq_sum]
  exact h

/-- **The score is the gradient of the GLM cost at `θ*`.** `∇(glmCost M ω)(θ*) = scoreVec M ω`,
i.e. `(1/n)∑ᵢ (ψ'(ηᵢ) − yᵢ)·xᵢ`. (Chain rule on each `ψ(⟨xᵢ,·⟩)` + linearity of `gradient`.) -/
theorem glmCost_gradient_eq_scoreVec (M : GLMExpFamily n d μ) (ω : Ω) :
    gradient (glmCost M ω) M.θstar = scoreVec M ω := by
  -- The score vector as `(1/n)∑ᵢ (ψ'(ηᵢ) − yᵢ)·rowᵢ`.
  have hscore : scoreVec M ω
      = (1 / (n : ℝ)) • ∑ i, (M.ψ' (linPred M.X M.θstar i) - M.y i ω) • rowVec M i := by
    apply WithLp.ofLp_injective 2
    funext j
    rw [scoreVec_ofLp, scoreCoord]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
      rowVec_ofLp, smul_eq_mul]
  -- The Fréchet derivative CLM equals the dual of the score vector.
  have hCLM : (1 / (n : ℝ)) • ∑ i, ((M.ψ' (⟪rowVec M i, M.θstar⟫_ℝ) •
          InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i))
        - (M.y i ω • InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (rowVec M i)))
      = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (scoreVec M ω) := by
    ext y
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, smul_eq_mul,
        InnerProductSpace.toDual_apply_apply, hscore, real_inner_smul_left, sum_inner]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        InnerProductSpace.toDual_apply_apply, smul_eq_mul, real_inner_smul_left, inner_rowVec]
    ring
  have hgrad : HasGradientAt (glmCost M ω) (scoreVec M ω) M.θstar := by
    rw [hasGradientAt_iff_hasFDerivAt, ← hCLM]
    exact glmCost_hasFDerivAt M ω
  exact hgrad.gradient

/-! ## The corollaries -/

/-- **Corollary 9.26 — GLM Lasso `ℓ₂`/`ℓ₁` rates.** Under (G1) column normalization, (G2) the GLM
exp-family with `0 ≤ ψ'' ≤ B²`, the RSC condition (9.62) at `θ*` (USER-INPUT), `θ*` supported on `S`
(`s = |S|`), and `λ = 4BC{√(log d/n) + δ}`, the `ℓ₁`-regularized GLM Lasso satisfies, with probability
`≥ 1 − 2e^{−2nδ²}`,
`‖θ̂ − θ*‖₂² ≤ 144·s·λ²/κ²` and `‖θ̂ − θ*‖₁ ≤ 48·s·λ/κ`. -/
theorem glm_lasso_l2_l1_rate (M : GLMExpFamily n d μ) [IsProbabilityMeasure μ]
    (S : Finset (Fin d)) (C κ R δ lam : ℝ) (θhat : Ω → EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: (G1) column normalization; Wainwright §9.5.
    (hC : IsColumnNormalized M.X C)
    (hn : 0 < n) (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1) (hB : 0 < M.B) (hCpos : 0 < C)
    -- USER-INPUT: target is `s`-sparse, supported on `S`; Wainwright Cor 9.26.
    (hsparse : M.θstar ∈ suppSubmodule S)
    -- USER-INPUT: RSC condition (9.62) for the GLM cost (radius `1`, tolerance `c₁ log d/n`); Wainwright Cor 9.26 (defers to Thm 9.36).
    (τSq : ℝ) (hτSq : 0 ≤ τSq)
    (hRSC : ∀ ω, RSC (glmCost M ω) M.θstar (l1Seminorm d) κ R τSq)
    -- USER-INPUT: slack `τ²·s ≤ κ/128`; Wainwright Cor 9.26 (sample-size condition).
    (hslack : τSq * (S.card : ℝ) ≤ κ / 128)
    -- USER-INPUT: `εₙ² ≤ R²` localization; Wainwright Cor 9.26.
    (hεR : 144 * (lam ^ 2 / κ ^ 2) * (S.card : ℝ) ≤ R ^ 2)
    -- USER-INPUT: tuning `λ = 4BC{√(log d/n) + δ}`; Wainwright Cor 9.26.
    (hlam : lam = 4 * M.B * C * (Real.sqrt (Real.log d / n) + δ))
    -- USER-INPUT: `θ̂ ω` minimizes the GLM Lasso objective `glmCost + λ‖·‖₁`; Wainwright eq 9.61.
    (hopt : ∀ ω θ, glmCost M ω (θhat ω) + lam * l1Norm (θhat ω)
        ≤ glmCost M ω θ + lam * l1Norm θ) :
    ENNReal.ofReal (1 - 2 * Real.exp (-2 * (n : ℝ) * δ ^ 2)) ≤
      μ {ω | ‖θhat ω - M.θstar‖ ^ 2 ≤ 144 * (lam ^ 2 / κ ^ 2) * (S.card : ℝ)
          ∧ l1Norm (θhat ω - M.θstar) ≤ 48 * (lam / κ) * (S.card : ℝ)} := by
  have hsum_pos : 0 < Real.sqrt (Real.log d / n) + δ :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hδ_pos
  have hlam_pos : 0 < lam := by
    rw [hlam]; exact mul_pos (mul_pos (mul_pos (by norm_num) hB) hCpos) hsum_pos
  have hmem : M.θstar ∈ (l1DecomposableReg S).M := hsparse
  have hΨsq : subspaceLip (l1DecomposableReg S).Φ (l1DecomposableReg S).Mbar ^ 2
      = (S.card : ℝ) := by
    change subspaceLip (l1Seminorm d) (suppSubmodule S) ^ 2 = (S.card : ℝ)
    rw [subspaceLip_l1_suppSubmodule S, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hepe : epsilonSq (l1DecomposableReg S) M.θstar lam κ τSq
      = 144 * (lam ^ 2 / κ ^ 2) * (S.card : ℝ) := by
    have hΦ0 : ((l1DecomposableReg S).M)ᗮ.starProjection M.θstar = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff _).mpr
        ((l1DecomposableReg S).M.le_orthogonal_orthogonal hmem)
    simp only [epsilonSq, hΦ0, map_zero]
    rw [hΨsq]; ring
  have hgood := good_event_highProb M C hC hn hd δ hδ_pos hδ_lt hB hCpos lam (le_of_eq hlam.symm)
  refine le_trans hgood (measure_mono ?_)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hG : GoodEvent (l1DecomposableReg S).Φstar (gradient (glmCost M ω) M.θstar) lam := by
    change (l1DecomposableReg S).Φstar (gradient (glmCost M ω) M.θstar) ≤ lam / 2
    rw [glmCost_gradient_eq_scoreVec]; exact hω
  refine ⟨?_, ?_⟩
  · have hb := cor_l2_bound_of_mem (l1DecomposableReg S) (glmCost M ω) (glmCost_convexOn M ω)
      (glmCost_differentiable M ω) M.θstar (θhat ω) lam κ R τSq hlam_pos hκ hR (hRSC ω) (hopt ω)
      hG hτSq (by rw [hΨsq]; exact hslack) (by rw [hepe]; exact hεR) hmem
    rwa [hΨsq] at hb
  · have hb := cor_reg_bound_of_mem (l1DecomposableReg S) (glmCost M ω) (glmCost_convexOn M ω)
      (glmCost_differentiable M ω) M.θstar (θhat ω) lam κ R τSq hlam_pos hκ hR (hRSC ω) (hopt ω)
      hG hτSq (by rw [hΨsq]; exact hslack) (by rw [hepe]; exact hεR) hmem
    rw [hΨsq] at hb
    exact hb

/-- **Corollary 9.27 — GLM Lasso `ℓ∞` rate.** In addition to the Corollary 9.26 hypotheses, under the
`ℓ∞`-curvature condition (9.64) (USER-INPUT) and the localization `Φ*(θ̂−θ*) ≤ R`, the GLM Lasso
satisfies `‖θ̂ − θ*‖∞ ≤ 3λ/κ` with probability `≥ 1 − 2e^{−2nδ²}`. (Tuning `λ = 4BC{√(log d/n)+δ}`,
the same level as Cor 9.26 — see the file header tuning note.) -/
theorem glm_lasso_linf_rate (M : GLMExpFamily n d μ) [IsProbabilityMeasure μ]
    (S : Finset (Fin d)) (C κ τ R δ lam : ℝ) (θhat : Ω → EuclideanSpace ℝ (Fin d))
    (hC : IsColumnNormalized M.X C)
    (hn : 0 < n) (hd : 0 < d) (hκ : 0 < κ)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1) (hB : 0 < M.B) (hCpos : 0 < C)
    (hsparse : M.θstar ∈ suppSubmodule S)
    -- USER-INPUT: `ℓ∞`-curvature condition (9.64) for the GLM cost; Wainwright Cor 9.27.
    (hcurv : ∀ ω, dualCurvature (glmCost M ω) M.θstar (l1Seminorm d) (linfSeminorm d) κ τ R)
    -- USER-INPUT: slack `τ·s < κ/32`; Wainwright Cor 9.27.
    (hslack : τ * (S.card : ℝ) < κ / 32)
    -- USER-INPUT: localization `Φ*(θ̂−θ*) ≤ R`; Wainwright Cor 9.27.
    (hRloc : ∀ ω, linfNorm (θhat ω - M.θstar) ≤ R)
    -- USER-INPUT: tuning `λ = 4BC{√(log d/n) + δ}`; Wainwright Cor 9.27 (good-event level, see header).
    (hlam : lam = 4 * M.B * C * (Real.sqrt (Real.log d / n) + δ))
    (hopt : ∀ ω θ, glmCost M ω (θhat ω) + lam * l1Norm (θhat ω)
        ≤ glmCost M ω θ + lam * l1Norm θ) :
    ENNReal.ofReal (1 - 2 * Real.exp (-2 * (n : ℝ) * δ ^ 2)) ≤
      μ {ω | linfNorm (θhat ω - M.θstar) ≤ 3 * lam / κ} := by
  have hsum_pos : 0 < Real.sqrt (Real.log d / n) + δ :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hδ_pos
  have hlam_pos : 0 < lam := by
    rw [hlam]; exact mul_pos (mul_pos (mul_pos (by norm_num) hB) hCpos) hsum_pos
  have hmem : M.θstar ∈ (l1DecomposableReg S).M := hsparse
  have hΨsq : subspaceLip (l1DecomposableReg S).Φ (l1DecomposableReg S).Mbar ^ 2
      = (S.card : ℝ) := by
    change subspaceLip (l1Seminorm d) (suppSubmodule S) ^ 2 = (S.card : ℝ)
    rw [subspaceLip_l1_suppSubmodule S, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hgood := good_event_highProb M C hC hn hd δ hδ_pos hδ_lt hB hCpos lam (le_of_eq hlam.symm)
  refine le_trans hgood (measure_mono ?_)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hG : GoodEvent (l1DecomposableReg S).Φstar (gradient (glmCost M ω) M.θstar) lam := by
    change (l1DecomposableReg S).Φstar (gradient (glmCost M ω) M.θstar) ≤ lam / 2
    rw [glmCost_gradient_eq_scoreVec]; exact hω
  have hb := mestimator_dual_bound (l1DecomposableReg S) (glmCost M ω) (glmCost_convexOn M ω)
    (glmCost_differentiable M ω) M.θstar (θhat ω) lam κ τ R hlam_pos hκ hmem (hcurv ω) (hopt ω)
    hG (by rw [hΨsq]; exact hslack) (hRloc ω)
  exact hb

end StatLean.HighDimensionalStatistics.MEstimator
