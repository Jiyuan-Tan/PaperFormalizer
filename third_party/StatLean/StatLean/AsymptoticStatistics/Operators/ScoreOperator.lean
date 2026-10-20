module
public import StatLean.AsymptoticStatistics.Core.EIF
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScore

@[expose] public section

/-!
# Score-operator / adjoint calculus

The abstract score operator `A : H →L[ℝ] ↥(L²₀(P))` from a parameter Hilbert
space `H` into mean-zero `L²(P)`, and the calculus for producing efficient
influence functions from it: the adjoint equation, the information-operator
formula, and the semiparametric specialization.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.5
— eq:25.29 (score operator), eq:25.30 (information-operator formula),
thm:25.31 (adjoint equation), eq:25.33 (semiparametric specialization).
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

-- The structure name `ScoreOperator` matches the namespace; intentional.
set_option linter.dupNamespace false

namespace AsymptoticStatistics.Operators.ScoreOperator

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise

variable {Ω : Type*} [MeasurableSpace Ω]

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- *Abstract score operator* `A : H →L[ℝ] ↥(L²₀(P))`.

A continuous linear map from a user-supplied parameter Hilbert space
`H` into the mean-zero `L²(P)` space. For parametric models
`H := EuclideanSpace ℝ (Fin k)`; for semiparametric / nonparametric
models `H` may be any other Hilbert space (e.g. `Lp ℝ 2 ν`).

Reference: vdV §25.5 (eq:25.29).

Edge behavior: when `H = 0`, the only score operator is the zero map,
and the tangent range is `⊥`. -/
structure ScoreOperator (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- vdV §25.5: the score operator as a continuous
  linear map from `H` to mean-zero `L²(P)`. -/
  toCLM : H →L[ℝ] ↥(L2ZeroMean P)

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- *vdV thm:25.31 (inner-product-certified form).* Given a score
operator `A : H →L[ℝ] ↥(L²₀(P))`, a tangent space `T` containing a
candidate `φ`, and the parameter-derivative-as-inner-product
certification `dψ g = ⟪φ, g⟫_ℝ` for every `g ∈ T`, the candidate `φ`
is an efficient influence function for `dψ`.

Reference: vdV §25.5, thm:25.31. The book states the conclusion as
"`φ` solves the adjoint equation `A* φ = χ`"; for `g ∈ range A`, the
adjoint identity `⟪A v, φ⟫ = ⟪v, A* φ⟫ = ⟪v, χ⟫ = dψ (A v)` recovers
the inner-product hypothesis `h_dψ_eq_inner` from `A* φ = χ` and the
parameter derivative shape on the score range. Extending to the full
`T` (when `T = closure(range A)`) requires a density / continuity
argument, omitted here.

The hypothesis `h_dψ_eq_inner` is the inner-product form of the adjoint
equation on the chosen tangent space.
-/
theorem eif_via_adjoint_equation
    {T : Submodule ℝ ↥(L2ZeroMean P)}
    {dψ : T →L[ℝ] ℝ} {φ : ↥(L2ZeroMean P)}
    (hφ_T : φ ∈ T)
    (h_dψ_eq_inner :
      ∀ g : T, dψ g = ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ) :
    IsEfficientInfluenceFunction P T dψ φ := by
  refine ⟨?_, hφ_T⟩
  intro g
  exact (h_dψ_eq_inner g).symm

/-- *vdV eq:25.30 in inner-product form, derived from the information
equation.* Suppose `κ : H`
solves the *information equation* `(A*A) κ = χ`, encoded without an
explicit adjoint as

  `h_information : ∀ v, ⟪A κ, A v⟫_{L²₀} = ⟪χ, v⟫_H`

(the defining property of the information operator `A*A`: testing
`(A*A) κ = χ` against every `v` is the same as `⟪A κ, A v⟫ = ⟪χ, v⟫`).
Suppose further that the parameter derivative `dψ` is the Riesz form of
`χ` on the score range,

  `h_dψ_on_range : ∀ v, dψ ⟨A v, _⟩ = ⟪χ, v⟫_H`

(this is the book's definition of `χ̃` as the influence function of
`η ↦ χ(η)`: `χ_η b = ⟪χ̃, b⟫_H`), and that the tangent space is covered
by the score range, `h_range : ∀ g ∈ T, ∃ v, A v = g`. Then `A κ` is an
efficient influence function for `dψ`.

Reference: vdV §25.5, eq:25.30. The book writes the conclusion as
`ψ̃ = A((A*A)⁻¹ χ) = A κ`. The proof is the adjoint chain

  `⟪A κ, A v⟫ = ⟪v, (A*A) κ⟫ = ⟪v, χ⟫ = dψ (A v)`,

run here purely in inner-product vocabulary (no
`ContinuousLinearMap.adjoint`, which would need `CompleteSpace
↥(L2ZeroMean P)` synthesizable through the Submodule sort-coercion):
the first equality is the inner-product *definition* of `A*A`, supplied
as `h_information`; the last is `h_dψ_on_range`. The information
equation turns the
candidate `A κ` into a representer of `dψ` on `range A = T`.

The conclusion establishes `⟪A κ, g⟫ = dψ g` for every `g ∈ T` and
`A κ ∈ T`. It does not assert uniqueness of the solution
`κ = (A*A)⁻¹ χ` modulo `N(A)`; existence of a solution to the information
equation suffices. -/
theorem eif_via_information_operator
    (A : ScoreOperator H P) (χ : H) (κ : H)
    (h_information :
      ∀ v : H, ⟪A.toCLM κ, A.toCLM v⟫_ℝ = ⟪χ, v⟫_ℝ)
    {T : Submodule ℝ ↥(L2ZeroMean P)}
    (hφ_T : A.toCLM κ ∈ T)
    (h_range : ∀ g ∈ T, ∃ v : H, A.toCLM v = g)
    {dψ : T →L[ℝ] ℝ}
    (h_dψ_on_range :
      ∀ (v : H) (hv : A.toCLM v ∈ T), dψ ⟨A.toCLM v, hv⟩ = ⟪χ, v⟫_ℝ) :
    IsEfficientInfluenceFunction P T dψ (A.toCLM κ) := by
  refine ⟨?_, hφ_T⟩
  intro g
  -- `g ∈ T` is in the score range: `g = A v` for some `v`.
  obtain ⟨v, hv⟩ := h_range (g : ↥(L2ZeroMean P)) g.2
  have hAv_mem : A.toCLM v ∈ T := by rw [hv]; exact g.2
  -- Rewrite `g` as the subtype element `⟨A v, _⟩`.
  have hg_subtype : g = ⟨A.toCLM v, hAv_mem⟩ := Subtype.ext hv.symm
  -- `IsInfluenceFunction` goal: `⟪A κ, g⟫ = dψ g`. Rewrite both sides
  -- to the `A v` form, then run the adjoint chain
  -- `⟪A κ, A v⟫ = ⟪χ, v⟫ = dψ ⟨A v, _⟩`.
  rw [hg_subtype]
  change ⟪A.toCLM κ, (A.toCLM v : ↥(L2ZeroMean P))⟫_ℝ
      = dψ ⟨A.toCLM v, hAv_mem⟩
  rw [h_information v, h_dψ_on_range v hAv_mem]

/-- *vdV eq:25.33 (semiparametric specialization).* In a strict
semiparametric model the score operator splits into a θ-component
`A_θ : H_θ →L[ℝ] ↥(L²₀(P))` and an η-component
`A_η : H_η →L[ℝ] ↥(L²₀(P))`. The efficient score for the
θ-direction `v : H_θ`, defined as the residual of the ordinary
θ-score after projecting onto a fixed η-tangent space `T_η` (typically
the closure of `range A_η`), coincides with `efficientScore` when
the ordinary-score operator is taken to be `A_θ.toCLM`.

Reference: vdV §25.5, eq:25.33. -/
theorem efficientScore_projection_formula
    {H_θ : Type*}
    [NormedAddCommGroup H_θ] [InnerProductSpace ℝ H_θ] [CompleteSpace H_θ]
    (A_θ : ScoreOperator H_θ P)
    (T_η : Submodule ℝ ↥(L2ZeroMean P)) [T_η.HasOrthogonalProjection]
    (v : H_θ) :
    A_θ.toCLM v - T_η.starProjection (A_θ.toCLM v)
      = AsymptoticStatistics.StrictModel.EfficientScore.efficientScore
          A_θ.toCLM T_η v := rfl

/-- *vdV eq:25.33 — the nuisance-score projection identity.* Let
`B := B_{θ,η}` be the nuisance score operator and let `Bstar = B*` satisfy
the adjoint identity `h_adj`.

The book asserts (p.374): *"if the operator `B*B` is continuously
invertible (but in many examples it is not), then the operator
`B(B*B)⁻¹B*` is the orthogonal projection onto the nuisance score
space"* (= the range of `B`).

The explicit operator `B ∘ (B*B)⁻¹ ∘ B*` equals
`(range B).starProjection`.

The invertibility hypothesis is represented by a
`ContinuousLinearEquiv ℝ H H` whose forward map is `B*B`, packaged as
`hBB : ∀ z, Bstar (B z) = e z`. The book is explicit that without it the
identity is false ("in many examples it is not invertible"). The equivalence
`e` records the book's two-sided continuous invertibility, although the proof
uses only `(B*B) ∘ e⁻¹ = id`.

`h_adj` is the defining adjoint identity
`⟪Bstar y, w⟫_H = ⟪y, B w⟫_{L²}`.

Proof: write `Px := B (e⁻¹ (Bstar x))`. By
`eq_starProjection_of_mem_orthogonal` it suffices to show
(i) `Px ∈ range B` — immediate, `Px` is in the image of `B`; and
(ii) `x - Px ∈ (range B)ᗮ` — for any `B w` in the range,
`⟪x - Px, B w⟫ = ⟪Bstar (x - Px), w⟫` by `h_adj`, and
`Bstar (x - Px) = Bstar x - Bstar (B (e⁻¹ (Bstar x)))`
`= Bstar x - e (e⁻¹ (Bstar x)) = Bstar x - Bstar x = 0`, the cancellation
being exactly `(B*B) ∘ e⁻¹ = id`.

Reference: vdV §25.5, eq:25.33, p.374. -/
theorem nuisanceProjection_eq_BinvBstar
    (B : ScoreOperator H P)
    (Bstar : ↥(L2ZeroMean P) →L[ℝ] H)
    (h_adj : ∀ (w : H) (y : ↥(L2ZeroMean P)),
        ⟪Bstar y, w⟫_ℝ = ⟪y, B.toCLM w⟫_ℝ)
    (e : H ≃L[ℝ] H)
    (hBB : ∀ z : H, Bstar (B.toCLM z) = e z)
    [(B.toCLM.range).HasOrthogonalProjection]
    (x : ↥(L2ZeroMean P)) :
    B.toCLM (e.symm (Bstar x))
      = (B.toCLM.range).starProjection x := by
  -- (i) the candidate `Px := B (e⁻¹ (Bstar x))` lies in the range of `B`.
  have hmem : B.toCLM (e.symm (Bstar x)) ∈ B.toCLM.range := ⟨_, rfl⟩
  -- (ii) reduce to `x - Px ⊥ range B`.
  refine (Submodule.eq_starProjection_of_mem_orthogonal hmem ?_).symm
  -- `Bstar (x - Px) = Bstar x - Bstar (B (e⁻¹ (Bstar x)))
  --   = Bstar x - e (e⁻¹ (Bstar x)) = Bstar x - Bstar x = 0`.
  have hcancel : Bstar (x - B.toCLM (e.symm (Bstar x))) = 0 := by
    rw [map_sub, hBB, ContinuousLinearEquiv.apply_symm_apply, sub_self]
  -- For any `g = B w ∈ range B`, `⟪x - Px, g⟫ = ⟪Bstar (x - Px), w⟫ = 0`.
  rw [Submodule.mem_orthogonal]
  rintro g ⟨w, rfl⟩
  -- `⟪B w, x - Px⟫ = ⟪x - Px, B w⟫ = ⟪Bstar (x - Px), w⟫ = ⟪0, w⟫ = 0`.
  -- `ContinuousLinearMap.coe_coe` normalizes the `range`-membership's
  -- `LinearMap`-coercion `↑B.toCLM w` to the `CLM`-coercion `B.toCLM w`
  -- so that `h_adj` matches.
  rw [ContinuousLinearMap.coe_coe, real_inner_comm, ← h_adj w, hcancel,
    inner_zero_left]

/-- *vdV §25.5, thm:25.31 — the differentiability hypothesis.*
`ψ : P_η ↦ χ(η)` is *differentiable relative to the score range* `range A`,
with influence representer `chiTilde : H`, iff there is a continuous-linear
derivative `dψ` on the score range whose value on each score `A v` is the
Riesz inner product `⟪chiTilde, v⟫_H`.

This is the abstract differentiability hypothesis of Theorem 25.31 (vdV
p.372–373): the book writes the derivative `χ_η` as the inner product
`χ_η b = ⟪χ̃, b⟫_H` for `χ̃ ∈ lin H`, and the score range `A H` is the
tangent set against which `ψ` is differentiated. -/
def DifferentiableRelScoreRange (A : ScoreOperator H P) (chiTilde : H) : Prop :=
  ∃ dψ : (A.toCLM.range) →L[ℝ] ℝ,
    ∀ (v : H), dψ ⟨A.toCLM v, ⟨v, rfl⟩⟩ = ⟪chiTilde, v⟫_ℝ

/-- *vdV §25.5, thm:25.31 — the constructive direction.*
If the influence representer `χ̃ = chiTilde` lies in the range of the adjoint
`A*` (i.e. there is `psiTilde` with `A* psiTilde = χ̃`), then `psiTilde` is an
influence function for the parameter-derivative `dψ` on the tangent space
`T = range A`.

This is the book's "if each coordinate of `χ̃` is contained in the range of
`A*`, then `ψ` is differentiable and the influence function satisfies
(25.30)" (vdV Thm 25.31, p.372).

Here the tangent space `T` is required to be exactly the score range
(`h_range_eq : A.toCLM.range = T`), matching the book's tangent set
`A H`: `IsInfluenceFunction` quantifies over *all* `g ∈ T`, and `h_dψ`
only specifies `dψ` on scores `A v`, so faithfully `T` must be the range.

The adjoint `A*` is specified by the identity `h_adj`
(`⟪A* y, v⟫_H = ⟪y, A v⟫_{L²}`), exactly the encoding of
`nuisanceProjection_eq_BinvBstar` and `eif_via_information_operator`.

Proof: for any `g ∈ T = range A`, write `g = A v`; then
`⟪psiTilde, A v⟫ = ⟪A* psiTilde, v⟫ = ⟪χ̃, v⟫ = dψ ⟨A v, _⟩`, the three
steps being `h_adj`, `h_range`, and `h_dψ` respectively. -/
theorem isIF_of_mem_range_adjoint
    (A : ScoreOperator H P) (Astar : ↥(L2ZeroMean P) →L[ℝ] H)
    (h_adj : ∀ (v : H) (y : ↥(L2ZeroMean P)), ⟪Astar y, v⟫_ℝ = ⟪y, A.toCLM v⟫_ℝ)
    (chiTilde : H) (psiTilde : ↥(L2ZeroMean P))
    (h_range : Astar psiTilde = chiTilde)
    {T : Submodule ℝ ↥(L2ZeroMean P)} (h_range_eq : A.toCLM.range = T)
    {dψ : T →L[ℝ] ℝ}
    (h_dψ : ∀ v : H,
        dψ ⟨A.toCLM v, h_range_eq ▸ (⟨v, rfl⟩ : A.toCLM v ∈ A.toCLM.range)⟩
          = ⟪chiTilde, v⟫_ℝ) :
    IsInfluenceFunction P T dψ psiTilde := by
  intro g
  -- `g ∈ T = range A`, so `g = A v` for some `v`.
  have hg_mem : (g : ↥(L2ZeroMean P)) ∈ A.toCLM.range := by
    rw [h_range_eq]; exact g.2
  obtain ⟨v, hv⟩ := hg_mem
  -- `hv : ↑A.toCLM v = ↑g`. Normalize the `LinearMap`-coercion to the CLM form.
  rw [ContinuousLinearMap.coe_coe] at hv
  -- Rewrite `g` as the subtype element `⟨A v, _⟩`.
  have hAv_mem : A.toCLM v ∈ T := h_range_eq ▸ (⟨v, rfl⟩ : A.toCLM v ∈ A.toCLM.range)
  have hg_subtype : g = ⟨A.toCLM v, hAv_mem⟩ := Subtype.ext hv.symm
  rw [hg_subtype]
  -- Goal: `⟪psiTilde, A v⟫ = dψ ⟨A v, _⟩`. Run the adjoint chain.
  change ⟪psiTilde, (A.toCLM v : ↥(L2ZeroMean P))⟫_ℝ = dψ ⟨A.toCLM v, hAv_mem⟩
  rw [h_dψ v, ← h_range, h_adj v psiTilde, real_inner_comm]

/-- *vdV §25.5, thm:25.31 / eq:25.30 — the explicit EIF formula `ψ̃ = A(A*A)⁻¹χ`.*
A corollary of `isIF_of_mem_range_adjoint`. When the information operator
`A*A` is continuously invertible (encoded by `e : H ≃L[ℝ] H` with
`hAA : ∀ z, A* (A z) = e z`), the influence representer `χ̃ = chiTilde` is
automatically in the range of `A*`, with explicit preimage
`A* (A (e⁻¹ χ̃)) = e (e⁻¹ χ̃) = χ̃`. Hence:

* `ψ` is differentiable relative to the score range with representer `χ̃`
  (`DifferentiableRelScoreRange A chiTilde`); the derivative is the Riesz
  form of the candidate `A (e⁻¹ χ̃)` on the score range; and
* the candidate `A (e⁻¹ χ̃)` is an influence function on `T = range A` for
  that derivative.

This is the book's eq:25.30 `ψ̃ = A(A*A)⁻¹χ` (vdV p.372): the efficient
influence function is the image under `A` of the solution `(A*A)⁻¹χ` of the
information equation. The book is explicit that `A*A` need not be invertible;
continuous invertibility is represented by the
two-sided equivalence `e`, matching the book's "continuously invertible".

The construction takes `psiTilde := A (e.symm χ̃)`,
`h_range := A* psiTilde = e (e.symm χ̃) = χ̃`, then `isIF_of_mem_range_adjoint`
with `dψ := ⟪psiTilde, ·⟫` restricted to the score range. The chain
`⟪psiTilde, A v⟫ = ⟪A* psiTilde, v⟫ = ⟪χ̃, v⟫` certifies `h_dψ`. -/
theorem eif_formula_of_information_invertible
    (A : ScoreOperator H P) (Astar : ↥(L2ZeroMean P) →L[ℝ] H)
    (h_adj : ∀ (v : H) (y : ↥(L2ZeroMean P)), ⟪Astar y, v⟫_ℝ = ⟪y, A.toCLM v⟫_ℝ)
    (e : H ≃L[ℝ] H) (hAA : ∀ z : H, Astar (A.toCLM z) = e z)
    (chiTilde : H) :
    DifferentiableRelScoreRange A chiTilde ∧
      IsInfluenceFunction P A.toCLM.range
        ((innerSL ℝ (A.toCLM (e.symm chiTilde))).comp A.toCLM.range.subtypeL)
        (A.toCLM (e.symm chiTilde)) := by
  set psiTilde : ↥(L2ZeroMean P) := A.toCLM (e.symm chiTilde) with hpsi
  -- `χ̃ ∈ range A*`: `A* psiTilde = e (e⁻¹ χ̃) = χ̃`.
  have h_range : Astar psiTilde = chiTilde := by
    rw [hpsi, hAA, ContinuousLinearEquiv.apply_symm_apply]
  -- The candidate derivative on the score range: the Riesz form of `psiTilde`.
  set dψ : A.toCLM.range →L[ℝ] ℝ :=
    (innerSL ℝ psiTilde).comp A.toCLM.range.subtypeL with hdψ
  -- `h_dψ`: on each score `A v`, `dψ ⟨A v, _⟩ = ⟪psiTilde, A v⟫ = ⟪χ̃, v⟫`.
  have h_dψ : ∀ v : H,
      dψ ⟨A.toCLM v, ⟨v, rfl⟩⟩ = ⟪chiTilde, v⟫_ℝ := by
    intro v
    rw [hdψ]
    change ⟪psiTilde, (A.toCLM v : ↥(L2ZeroMean P))⟫_ℝ = ⟪chiTilde, v⟫_ℝ
    rw [← h_range, h_adj v psiTilde, real_inner_comm]
  refine ⟨⟨dψ, h_dψ⟩, ?_⟩
  -- The influence-function identity on `T = range A`.
  exact isIF_of_mem_range_adjoint A Astar h_adj chiTilde psiTilde h_range rfl h_dψ

/-- *vdV §25.5, thm:25.31 — unrestricted score-range form.*
Differentiability on the (possibly nonclosed) actual range of `A` gives a
bounded functional there.  Hahn--Banach extends it to the ambient
`L2ZeroMean P`; ambient Riesz then supplies a representer whose image under
the certified adjoint is `chiTilde`.

Proof idea: `Real.exists_extension_norm_eq`, followed by ambient Riesz and
the adjoint identity.  No closed-range hypothesis is needed.

Joint satisfiability witness: take `H = ℝ`, `A = id` (after identifying the
codomain with a one-dimensional mean-zero subspace), and any Riesz
functional; the representer is already in the actual adjoint range. -/
theorem mem_range_adjoint_of_differentiable_unrestricted
    (A : ScoreOperator H P) (Astar : ↥(L2ZeroMean P) →L[ℝ] H)
    (h_adj : ∀ (v : H) (y : ↥(L2ZeroMean P)), ⟪Astar y, v⟫_ℝ = ⟪y, A.toCLM v⟫_ℝ)
    (chiTilde : H) (h_diff : DifferentiableRelScoreRange A chiTilde) :
    chiTilde ∈ (Astar.range : Submodule ℝ H) := by
  -- The ambient mean-zero `L²(P)` is complete (closed kernel of `integralL2`);
  -- this instance does not auto-synthesize through the `Submodule` coercion.
  have hL2 : CompleteSpace ↥(L2ZeroMean P) :=
    (AsymptoticStatistics.Core.Hilbert.L2ZeroMean_isClosed P).completeSpace_coe
  obtain ⟨dψ, h_dψ⟩ := h_diff
  -- Hahn--Banach extends `dψ` from the possibly nonclosed score range to the
  -- ambient mean-zero `L²(P)` space.
  obtain ⟨dψext, h_ext, _⟩ := exists_extension_norm_eq A.toCLM.range dψ
  -- Ambient Riesz representer of the extension.
  set y₀ : ↥(L2ZeroMean P) :=
    (@InnerProductSpace.toDual ℝ ↥(L2ZeroMean P) _ _ _ hL2).symm dψext with hy₀
  refine ⟨y₀, ?_⟩
  -- Test `A* y₀ = χ̃` against every direction `v`.
  refine ext_inner_right ℝ (fun v => ?_)
  have hriesz : (⟪y₀, A.toCLM v⟫_ℝ : ℝ) = ⟪chiTilde, v⟫_ℝ := by
    rw [hy₀, @InnerProductSpace.toDual_symm_apply ℝ ↥(L2ZeroMean P) _ _ _ hL2]
    rw [h_ext (⟨A.toCLM v, ⟨v, rfl⟩⟩ : ↥(A.toCLM.range))]
    exact h_dψ v
  calc (⟪Astar y₀, v⟫_ℝ : ℝ)
      = ⟪y₀, A.toCLM v⟫_ℝ := h_adj v y₀
    _ = ⟪chiTilde, v⟫_ℝ := hriesz

/-- Closed-range form of the adjoint-range characterization, using Riesz on
the complete score range. -/
theorem mem_range_adjoint_of_differentiable
    (A : ScoreOperator H P) (Astar : ↥(L2ZeroMean P) →L[ℝ] H)
    (h_adj : ∀ (v : H) (y : ↥(L2ZeroMean P)), ⟪Astar y, v⟫_ℝ = ⟪y, A.toCLM v⟫_ℝ)
    (h_closed : IsClosed (A.toCLM.range : Set ↥(L2ZeroMean P)))
    (chiTilde : H) (h_diff : DifferentiableRelScoreRange A chiTilde) :
    chiTilde ∈ (Astar.range : Submodule ℝ H) := by
  -- The ambient mean-zero `L²(P)` is complete (closed kernel of `integralL2`);
  -- this instance does not auto-synthesize through the `Submodule` coercion.
  have hL2 : CompleteSpace ↥(L2ZeroMean P) :=
    (AsymptoticStatistics.Core.Hilbert.L2ZeroMean_isClosed P).completeSpace_coe
  -- Closed range ⟹ the score-range subspace is complete, so Riesz applies.
  haveI hcomplete : CompleteSpace ↥(A.toCLM.range) :=
    completeSpace_coe_iff_isComplete.mpr h_closed.isComplete
  obtain ⟨dψ, h_dψ⟩ := h_diff
  -- Riesz representer `y₀ ∈ range A` of the continuous functional `dψ`.
  set y₀ : ↥(A.toCLM.range) :=
    (InnerProductSpace.toDual ℝ ↥(A.toCLM.range)).symm dψ with hy₀
  -- `χ̃ = A* y₀`, so `χ̃ ∈ range A*`.
  refine ⟨(y₀ : ↥(L2ZeroMean P)), ?_⟩
  -- Show `A* ↑y₀ = χ̃` by testing against every `v` via `h_adj`:
  -- `⟪A* ↑y₀, v⟫ = ⟪↑y₀, A v⟫ = dψ ⟨A v, _⟩ = ⟪χ̃, v⟫`.
  refine ext_inner_right ℝ (fun v => ?_)
  -- `⟪A* ↑y₀, v⟫ = ⟪↑y₀, A v⟫` (adjoint identity), then Riesz + `h_dψ`.
  have hadj := h_adj v (y₀ : ↥(L2ZeroMean P))
  -- Bridge ambient ⟪↑y₀, A v⟫ to the submodule inner, then apply Riesz + `h_dψ`.
  have hsub : (⟪(y₀ : ↥(L2ZeroMean P)), A.toCLM v⟫_ℝ : ℝ)
      = ⟪y₀, (⟨A.toCLM v, ⟨v, rfl⟩⟩ : ↥(A.toCLM.range))⟫_ℝ :=
    (Submodule.coe_inner _ y₀ ⟨A.toCLM v, ⟨v, rfl⟩⟩).symm
  have hriesz : (⟪y₀, (⟨A.toCLM v, ⟨v, rfl⟩⟩ : ↥(A.toCLM.range))⟫_ℝ : ℝ)
      = ⟪chiTilde, v⟫_ℝ := by
    rw [hy₀, InnerProductSpace.toDual_symm_apply]
    exact h_dψ v
  calc (⟪Astar (y₀ : ↥(L2ZeroMean P)), v⟫_ℝ : ℝ)
      = ⟪(y₀ : ↥(L2ZeroMean P)), A.toCLM v⟫_ℝ := hadj
    _ = ⟪y₀, (⟨A.toCLM v, ⟨v, rfl⟩⟩ : ↥(A.toCLM.range))⟫_ℝ := hsub
    _ = ⟪chiTilde, v⟫_ℝ := hriesz

/-- Actual-range form of vdV 25.31: differentiability relative to the score
range is equivalent to membership in the actual adjoint range.  The reverse
direction uses the existing adjoint representer construction; the forward
direction is Hahn--Banach plus ambient Riesz. -/
theorem differentiableRelScoreRange_iff_mem_range_adjoint
    (A : ScoreOperator H P) (Astar : ↥(L2ZeroMean P) →L[ℝ] H)
    (h_adj : ∀ (v : H) (y : ↥(L2ZeroMean P)),
      ⟪Astar y, v⟫_ℝ = ⟪y, A.toCLM v⟫_ℝ)
    (chiTilde : H) :
    DifferentiableRelScoreRange A chiTilde ↔
      chiTilde ∈ (Astar.range : Submodule ℝ H) := by
  constructor
  · exact mem_range_adjoint_of_differentiable_unrestricted A Astar h_adj chiTilde
  · rintro ⟨psiTilde, hpsi⟩
    rw [ContinuousLinearMap.coe_coe] at hpsi
    let dψ : A.toCLM.range →L[ℝ] ℝ :=
      (innerSL ℝ psiTilde).comp A.toCLM.range.subtypeL
    refine ⟨dψ, ?_⟩
    intro v
    change ⟪psiTilde, (A.toCLM v : ↥(L2ZeroMean P))⟫_ℝ = ⟪chiTilde, v⟫_ℝ
    rw [← hpsi, h_adj v psiTilde]

end AsymptoticStatistics.Operators.ScoreOperator
