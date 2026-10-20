module
public import StatLean.AsymptoticStatistics.ForMathlib.InProbability
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# Argmax localization — the quadratic complete-the-square core of vdV Theorem 5.23

This file isolates the **genuinely-new mathematical content** of the M-estimator
asymptotic normality theorem (vdV 5.23), the part that distinguishes it from the
Z-estimator sibling (vdV 5.21, `EmpiricalProcess/ZEstimatorNormality.lean`): the
Z-estimator rides the *linear estimating-equation* engine (19.26), whereas the
M-estimator is a **maximizer of a locally-quadratic criterion** and must be
linearised by a complete-the-square argument.

Everything here is self-contained finite-dimensional linear algebra plus the
varying-base `o_P` calculus of `ForMathlib/InProbability.lean` — no empirical
process, no CLT.

## The identity

Write `q(x) = ½⟪x, Vx⟫ + ⟪x, G⟫` for the local quadratic (`V` the symmetric,
nonsingular, negative-definite second-derivative matrix, `G` the score vector).
Completing the square (`complete_the_square`),

    q(x) − q(−V⁻¹G) = ½⟪x + V⁻¹G, V(x + V⁻¹G)⟫.

In vdV's proof this quadratic form is (i) `≥ −o_P(1)` (near-maximization of the
empirical criterion at `θ̂` versus the comparison point `θ₀ − V⁻¹G/√n`), and
(ii) `≤ 0` (negative-definiteness of `V`). A squeeze forces it `→ₚ 0`, and
negative-definiteness then forces `x + V⁻¹G →ₚ 0` — i.e., with `x = √n(θ̂−θ₀)` and
`G = 𝔾ₙṁ_{θ₀}`, the linear representation `√n(θ̂−θ₀) = −V⁻¹𝔾ₙṁ_{θ₀} + o_P(1)`.

## Main ingredients

* `TendstoInProbZero.add` / `.sub` / `.neg`, `tendstoInProbZero_of_norm_le` — A0
  `o_P` combinators used in the negative-definite squeeze.
* `matrix_toEuclideanCLM_inner_comm` — A1 self-adjointness of a Hermitian matrix.
* `complete_the_square` — A2 the identity above.
* `tendstoInProbZero_of_neg_def_quadform` — A3 the negative-definite squeeze.
* `argmax_localization` — A4 the core theorem.
-/

open MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace Matrix

namespace AsymptoticStatistics.MEstimator

variable {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]

/-! ### A0 — `o_P` combinators with a varying base measure -/

/-- **A0: sum of `→ₚ 0` is `→ₚ 0`.** `‖Z+W‖ ≤ ‖Z‖+‖W‖`, split the `ε`-exceedance
into `{‖Z‖ ≥ ε/2} ∪ {‖W‖ ≥ ε/2}`. -/
theorem TendstoInProbZero.add {G : Type*} [NormedAddCommGroup G]
    {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {Z W : ∀ k, Ω k → G}
    (hZ : TendstoInProbZero P Z) (hW : TendstoInProbZero P W) :
    TendstoInProbZero P (fun k ω => Z k ω + W k ω) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  have hsub : ∀ k, {ω | ε ≤ ‖Z k ω + W k ω‖} ⊆
      {ω | ε / 2 ≤ ‖Z k ω‖} ∪ {ω | ε / 2 ≤ ‖W k ω‖} := by
    intro k ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    have htri := norm_add_le (Z k ω) (W k ω)
    linarith [hcon.1, hcon.2]
  have hbound : ∀ k, (P k).real {ω | ε ≤ ‖Z k ω + W k ω‖} ≤
      (P k).real {ω | ε / 2 ≤ ‖Z k ω‖} + (P k).real {ω | ε / 2 ≤ ‖W k ω‖} := by
    intro k
    refine le_trans (measureReal_mono (hsub k)) ?_
    exact measureReal_union_le _ _
  have hsum : Tendsto (fun k => (P k).real {ω | ε / 2 ≤ ‖Z k ω‖} +
      (P k).real {ω | ε / 2 ≤ ‖W k ω‖}) atTop (𝓝 (0 : ℝ)) := by
    have := Tendsto.add (hZ (ε / 2) hε2) (hW (ε / 2) hε2)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun k => measureReal_nonneg)
    (Eventually.of_forall fun k => hbound k)

/-- **A0: negation preserves `→ₚ 0`.** -/
theorem TendstoInProbZero.neg {G : Type*} [NormedAddCommGroup G]
    {P : ∀ k, Measure (Ω k)} {Z : ∀ k, Ω k → G}
    (hZ : TendstoInProbZero P Z) :
    TendstoInProbZero P (fun k ω => - Z k ω) := by
  intro ε hε
  simpa only [norm_neg] using hZ ε hε

/-- **A0: difference of `→ₚ 0` is `→ₚ 0`.** -/
theorem TendstoInProbZero.sub {G : Type*} [NormedAddCommGroup G]
    {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {Z W : ∀ k, Ω k → G}
    (hZ : TendstoInProbZero P Z) (hW : TendstoInProbZero P W) :
    TendstoInProbZero P (fun k ω => Z k ω - W k ω) := by
  have h := TendstoInProbZero.add hZ (TendstoInProbZero.neg hW)
  simpa only [sub_eq_add_neg] using h

/-- **A0: `→ₚ 0` scaled by a constant.** -/
theorem TendstoInProbZero.const_smul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {P : ∀ k, Measure (Ω k)} {Z : ∀ k, Ω k → G}
    (c : ℝ) (hZ : TendstoInProbZero P Z) :
    TendstoInProbZero P (fun k ω => c • Z k ω) := by
  intro ε hε
  rcases eq_or_ne c 0 with hc0 | hc0
  · subst hc0
    have hset : ∀ k, {ω | ε ≤ ‖(0 : ℝ) • Z k ω‖} = (∅ : Set (Ω k)) := by
      intro k
      ext ω
      simp only [zero_smul, norm_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_le]
      exact hε
    simp only [hset, measureReal_empty]
    exact tendsto_const_nhds
  · have hcpos : 0 < |c| := abs_pos.mpr hc0
    have hset : ∀ k, {ω | ε ≤ ‖c • Z k ω‖} = {ω | ε / |c| ≤ ‖Z k ω‖} := by
      intro k
      ext ω
      simp only [Set.mem_setOf_eq, norm_smul, Real.norm_eq_abs]
      rw [div_le_iff₀ hcpos, mul_comm]
    simp only [hset]
    exact hZ (ε / |c|) (div_pos hε hcpos)

/-- **A0: norm-domination transfers `→ₚ 0`.** If `‖Z k ω‖ ≤ ‖W k ω‖` pointwise and
`W →ₚ 0`, then `Z →ₚ 0`: the exceedance event of `Z` is contained in that of `W`.

The `[IsProbabilityMeasure]` instance is genuinely required — it is the finiteness
witness for `measureReal_mono` on the larger set. Without it the statement is false:
e.g. `P k = volume` on `ℝ`, `W k ≡ 1` (exceedance `univ`, `.real = 0`, so `hW` holds),
`Z k = indicator (Icc 0 1)` (`.real = 1`, so `Z` is not `→ₚ 0`). -/
theorem tendstoInProbZero_of_norm_le {G H : Type*} [NormedAddCommGroup G]
    [NormedAddCommGroup H] {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {Z : ∀ k, Ω k → G} {W : ∀ k, Ω k → H}
    (hle : ∀ k ω, ‖Z k ω‖ ≤ ‖W k ω‖) (hW : TendstoInProbZero P W) :
    TendstoInProbZero P Z := by
  intro ε hε
  have hsub : ∀ k, {ω | ε ≤ ‖Z k ω‖} ⊆ {ω | ε ≤ ‖W k ω‖} := by
    intro k ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact le_trans hω (hle k ω)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hW ε hε)
    (Eventually.of_forall fun k => measureReal_nonneg)
    (Eventually.of_forall fun k => measureReal_mono (hsub k))

/-! ### A1 — Hermitian matrix acts self-adjointly on `EuclideanSpace ℝ (Fin d)`. -/

variable {d : ℕ}

/-- **A1: self-adjointness.** For a Hermitian (real symmetric) matrix `V`,
`⟪x, Vy⟫ = ⟪Vx, y⟫` where `V` acts via `Matrix.toEuclideanCLM`. Reduces to
`∑ᵢⱼ xᵢ Vᵢⱼ yⱼ = ∑ᵢⱼ Vⱼᵢ xᵢ yⱼ`, i.e. `Vᵢⱼ = Vⱼᵢ`. -/
theorem matrix_toEuclideanCLM_inner_comm (V : Matrix (Fin d) (Fin d) ℝ)
    (hV : V.IsHermitian) (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V y⟫
      = ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x, y⟫ := by
  rw [Matrix.inner_toEuclideanCLM, real_inner_comm, Matrix.inner_toEuclideanCLM]
  have hVT : Vᵀ = V := by
    ext i j
    simpa [Matrix.transpose_apply, Matrix.conjTranspose_apply] using
      (congrFun (congrFun hV.eq j) i).symm
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hVT, dotProduct_comm]

/-! ### A2 — complete-the-square identity. -/

/-- **A2: complete the square.** With `q(x) := ½⟪x, Vx⟫ + ⟪x, G⟫` and `V` symmetric
nonsingular,

    q(x) − q(−V⁻¹G) = ½⟪x + V⁻¹G, V(x + V⁻¹G)⟫.

Uses `Matrix.toEuclideanCLM V (Matrix.toEuclideanCLM V⁻¹ g) = g` (from `V * V⁻¹ = 1`)
and A1 self-adjointness. -/
theorem complete_the_square (V : Matrix (Fin d) (Fin d) ℝ)
    (hVunit : IsUnit V.det) (hVsymm : V.IsHermitian)
    (x G : EuclideanSpace ℝ (Fin d)) :
    ((1 / 2) * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ + ⟪x, G⟫)
        - (- (1 / 2) * ⟪G, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ G⟫)
      = (1 / 2) * ⟪x + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ G,
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V
            (x + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ G)⟫ := by
  set Vc := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V with hVc
  set Wc := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ with hWc
  -- key: `Vc (Wc G) = G` from `V * V⁻¹ = 1`.
  have hVg : Vc (Wc G) = G := by
    have hmul : Vc * Wc = 1 := by
      rw [hVc, hWc, ← map_mul, Matrix.mul_nonsing_inv V hVunit, map_one]
    calc Vc (Wc G) = (Vc * Wc) G := (ContinuousLinearMap.mul_apply Vc Wc G).symm
      _ = G := by rw [hmul, ContinuousLinearMap.one_apply]
  -- linearity of `Vc` on the shifted point.
  have hlin : Vc (x + Wc G) = Vc x + G := by rw [map_add, hVg]
  -- self-adjoint cross term.
  have h1 : ⟪Wc G, Vc x⟫ = ⟪x, G⟫ := by
    have hsa := matrix_toEuclideanCLM_inner_comm V hVsymm (Wc G) x
    rw [← hVc] at hsa
    rw [hsa, hVg]
    exact real_inner_comm x G
  rw [hlin, inner_add_left, inner_add_right, inner_add_right, h1, real_inner_comm G (Wc G)]
  ring

/-! ### A3 — negative-definite squeeze. -/

/-- **A3: negative-definite quadratic form squeeze.** If `V` is uniformly negative
definite (`⟪x, Vx⟫ ≤ −c‖x‖²` for a fixed `c > 0`) and the random quadratic form
`⟪u k ω, V(u k ω)⟫ →ₚ 0`, then `u →ₚ 0`. The exceedance `{‖u‖ ≥ ε}` sits inside
`{‖⟪u, Vu⟫‖ ≥ cε²}` because `⟪u,Vu⟫ ≤ 0` makes `‖⟪u,Vu⟫‖ = −⟪u,Vu⟫ ≥ c‖u‖² ≥ cε²`. -/
theorem tendstoInProbZero_of_neg_def_quadform
    {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    (V : Matrix (Fin d) (Fin d) ℝ) {c : ℝ} (hc : 0 < c)
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin d),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ - c * ‖x‖ ^ 2)
    {u : ∀ k, Ω k → EuclideanSpace ℝ (Fin d)}
    (hQ : TendstoInProbZero P (fun k ω =>
      ⟪u k ω, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (u k ω)⟫)) :
    TendstoInProbZero P u := by
  -- The `[IsProbabilityMeasure]` instance is the finiteness witness for `measureReal_mono` on
  -- the larger set `{cε² ≤ ‖⟪u,Vu⟫‖}`; without it the statement is false (analogous
  -- infinite-measure counterexample to `tendstoInProbZero_of_norm_le`).
  intro ε hε
  have hcε : (0 : ℝ) < c * ε ^ 2 := by positivity
  have hsub : ∀ k, {ω | ε ≤ ‖u k ω‖} ⊆
      {ω | c * ε ^ 2 ≤
        ‖⟪u k ω, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (u k ω)⟫‖} := by
    intro k ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hneg := hVneg (u k ω)
    have hSv0 : ⟪u k ω, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (u k ω)⟫ ≤ 0 := by
      nlinarith [hneg, mul_nonneg hc.le (sq_nonneg ‖u k ω‖)]
    rw [Real.norm_eq_abs, abs_of_nonpos hSv0]
    have hsq : ε ^ 2 ≤ ‖u k ω‖ ^ 2 := by
      nlinarith [mul_le_mul hω hω hε.le (norm_nonneg (u k ω))]
    nlinarith [hneg, mul_le_mul_of_nonneg_left hsq hc.le]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hQ (c * ε ^ 2) hcε)
    (Eventually.of_forall fun k => measureReal_nonneg)
    (Eventually.of_forall fun k => measureReal_mono (hsub k))

/-! ### A4 — the argmax localization core. -/

/-- **A4: argmax localization (core of vdV Theorem 5.23).**

Let `h k : Ω k → ℝᵈ` (`= √n(θ̂−θ₀)`), `G k : Ω k → ℝᵈ` (`= 𝔾ₙṁ_{θ₀}`), and scalar
`A B k : Ω k → ℝ` (`= n·ℙₙ` of the criterion increment at `θ̂` resp. at the comparison
point `θ₀ − V⁻¹G/√n`). Assume `V` is symmetric, nonsingular, and uniformly negative
definite, together with the two quadratic expansions and near-maximization

* `hExpA` : `A − (½⟪h,Vh⟫ + ⟪h,G⟫) →ₚ 0`,
* `hExpB` : `B − (−½⟪G, V⁻¹G⟫) →ₚ 0`,
* `hNearMax` : `max 0 (B − A) →ₚ 0`   (i.e. `A ≥ B − o_P(1)`).

Then `h + V⁻¹G →ₚ 0` — the linear representation `√n(θ̂−θ₀) = −V⁻¹𝔾ₙṁ + o_P(1)`.

Proof: set `S := ⟪u, Vu⟫`, `u := h + V⁻¹G`. By `complete_the_square`,
`S = 2(A − B) − 2(rA − rB)` with `rA := A − q(h)`, `rB := B − q(−V⁻¹G)` both `→ₚ 0`.
Then `−S = 2(B − A) + 2(rA − rB) ≤ 2·max0(B−A) + 2‖rA−rB‖ →ₚ 0`, and `S ≤ 0`, so a
comparison gives `S →ₚ 0`; `tendstoInProbZero_of_neg_def_quadform` gives `u →ₚ 0`.

Both squeeze steps go through the reusable combinators `tendstoInProbZero_of_norm_le`
(the `S →ₚ 0` domination) and `tendstoInProbZero_of_neg_def_quadform` (the negative-
definite squeeze); each carries the `IsProbabilityMeasure` instance that supplies
`measureReal_mono`'s finiteness witness (both are false without it). -/
theorem argmax_localization
    {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    (V : Matrix (Fin d) (Fin d) ℝ)
    (hVunit : IsUnit V.det) (hVsymm : V.IsHermitian)
    {c : ℝ} (hc : 0 < c)
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin d),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ - c * ‖x‖ ^ 2)
    (h G : ∀ k, Ω k → EuclideanSpace ℝ (Fin d)) (A B : ∀ k, Ω k → ℝ)
    (hExpA : TendstoInProbZero P (fun k ω => A k ω
      - ((1 / 2) * ⟪h k ω, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (h k ω)⟫
          + ⟪h k ω, G k ω⟫)))
    (hExpB : TendstoInProbZero P (fun k ω => B k ω
      - (- (1 / 2) * ⟪G k ω,
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ (G k ω)⟫)))
    (hNearMax : TendstoInProbZero P (fun k ω => max 0 (B k ω - A k ω))) :
    TendstoInProbZero P (fun k ω =>
      h k ω + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ (G k ω)) := by
  set Vc := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V with hVcdef
  set Wc := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ with hWcdef
  -- `rA − rB →ₚ 0`, hence `‖rA − rB‖ →ₚ 0`.
  have hrdiff : TendstoInProbZero P (fun k ω =>
      ‖(A k ω - ((1 / 2) * ⟪h k ω, Vc (h k ω)⟫ + ⟪h k ω, G k ω⟫))
        - (B k ω - (- (1 / 2) * ⟪G k ω, Wc (G k ω)⟫))‖) := by
    intro ε hε
    simpa only [norm_norm] using (TendstoInProbZero.sub hExpA hExpB) ε hε
  -- the dominating envelope `Wₙ := 2·max0(B−A) + 2·‖rA − rB‖ →ₚ 0`.
  have hWn : TendstoInProbZero P (fun k ω =>
      (2 : ℝ) • max 0 (B k ω - A k ω)
        + (2 : ℝ) • ‖(A k ω - ((1 / 2) * ⟪h k ω, Vc (h k ω)⟫ + ⟪h k ω, G k ω⟫))
            - (B k ω - (- (1 / 2) * ⟪G k ω, Wc (G k ω)⟫))‖) :=
    TendstoInProbZero.add (TendstoInProbZero.const_smul 2 hNearMax)
      (TendstoInProbZero.const_smul 2 hrdiff)
  -- Step 1: the quadratic form `S := ⟪u, Vu⟫ →ₚ 0` by norm-domination (`‖S‖ ≤ ‖Wₙ‖`).
  have hS : TendstoInProbZero P (fun k ω =>
      ⟪h k ω + Wc (G k ω), Vc (h k ω + Wc (G k ω))⟫) := by
    refine tendstoInProbZero_of_norm_le (fun k ω => ?_) hWn
    have hcts := complete_the_square V hVunit hVsymm (h k ω) (G k ω)
    rw [← hVcdef, ← hWcdef] at hcts
    have hSv0 : ⟪h k ω + Wc (G k ω), Vc (h k ω + Wc (G k ω))⟫ ≤ 0 := by
      nlinarith [hVneg (h k ω + Wc (G k ω)),
        mul_nonneg hc.le (sq_nonneg ‖h k ω + Wc (G k ω)‖)]
    have hWn0 : (0 : ℝ) ≤ (2 : ℝ) • max 0 (B k ω - A k ω)
        + (2 : ℝ) • ‖(A k ω - ((1 / 2) * ⟪h k ω, Vc (h k ω)⟫ + ⟪h k ω, G k ω⟫))
            - (B k ω - (- (1 / 2) * ⟪G k ω, Wc (G k ω)⟫))‖ := by
      rw [smul_eq_mul, smul_eq_mul]
      exact add_nonneg (mul_nonneg (by norm_num) (le_max_left _ _))
        (mul_nonneg (by norm_num) (norm_nonneg _))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos hSv0, abs_of_nonneg hWn0,
      smul_eq_mul, smul_eq_mul, Real.norm_eq_abs]
    nlinarith [hcts, le_max_right (0 : ℝ) (B k ω - A k ω),
      le_abs_self ((A k ω - ((1 / 2) * ⟪h k ω, Vc (h k ω)⟫ + ⟪h k ω, G k ω⟫))
        - (B k ω - (- (1 / 2) * ⟪G k ω, Wc (G k ω)⟫)))]
  -- Step 2: negative-definite squeeze `S →ₚ 0 ⟹ u →ₚ 0`.
  exact tendstoInProbZero_of_neg_def_quadform V hc hVneg hS

/-! ### A5 — localization from fixed deterministic comparisons. -/

set_option maxHeartbeats 800000 in
-- The finite-net proof elaborates dependent varying-base events and a large quadratic inequality.
/-- **A5: argmax localization from fixed deterministic comparisons.**

Let `q_G(x) = ½⟪x, Vx⟫ + ⟪x, G⟫`, with `V` symmetric, nonsingular, and
uniformly negative definite. Suppose `hA` and `G` are bounded in probability,
the random objective `A` has the quadratic expansion at `hA`, and for every
fixed deterministic `a` an objective value `B a` has the corresponding
expansion at `a` and is asymptotically no larger than `A`. Then
`hA + V⁻¹G →ₚ 0`.

The fixed-comparison quantifiers are sufficient: on a high-probability event,
boundedness places `hA`, `G`, and the random quadratic maximizer `-V⁻¹G` in
deterministic balls. A finite net of the latter ball reduces the comparison to
finitely many deterministic `a`; strong concavity supplies a uniform quadratic
gap away from the maximizer, while the finite-net approximation controls the
quadratic criterion uniformly on those balls. Thus no random-comparison
objective, random-comparison near-maximization premise, or measurability
provider is required. -/
theorem argmax_localization_of_fixed_comparisons
    -- The varying sequence of probability laws.
    {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    -- The deterministic quadratic Hessian.
    (V : Matrix (Fin d) (Fin d) ℝ)
    -- Nonsingularity and symmetry of the quadratic Hessian.
    (hVunit : IsUnit V.det) (hVsymm : V.IsHermitian)
    -- A uniform negative-definiteness constant.
    {c : ℝ} (hc : 0 < c)
    -- Uniform negative definiteness of the quadratic form.
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin d),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ -c * ‖x‖ ^ 2)
    -- The random local direction and random linear coefficient.
    (hA G : ∀ k, Ω k → EuclideanSpace ℝ (Fin d))
    -- The objective at the random direction and at fixed comparisons.
    (A : ∀ k, Ω k → ℝ)
    (B : EuclideanSpace ℝ (Fin d) → ∀ k, Ω k → ℝ)
    -- Tightness of the random direction and linear coefficient.
    (hhA_bdd : IsBoundedInProb P hA) (hG_bdd : IsBoundedInProb P G)
    -- Quadratic expansion at the random direction.
    (hExpA : TendstoInProbZero P (fun k ω => A k ω
      - ((1 / 2) * ⟪hA k ω, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (hA k ω)⟫
          + ⟪hA k ω, G k ω⟫)))
    -- Quadratic expansion at every fixed comparison.
    (hExpB : ∀ a : EuclideanSpace ℝ (Fin d),
      TendstoInProbZero P (fun k ω => B a k ω
        - ((1 / 2) * ⟪a, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V a⟫
            + ⟪a, G k ω⟫)))
    -- Near-maximality against every fixed deterministic comparison.
    (hNearMax : ∀ a : EuclideanSpace ℝ (Fin d),
      TendstoInProbZero P (fun k ω => max 0 (B a k ω - A k ω))) :
    TendstoInProbZero P (fun k ω =>
      hA k ω + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ (G k ω)) := by
  classical
  set Vc := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V with hVcdef
  set Wc := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹ with hWcdef
  let q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun x g => (1 / 2) * ⟪x, Vc x⟫ + ⟪x, g⟫
  let quad : EuclideanSpace ℝ (Fin d) → ℝ := fun x => (1 / 2) * ⟪x, Vc x⟫
  let acomp : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun g => -Wc g
  let rA : ∀ k, Ω k → ℝ := fun k ω => A k ω - q (hA k ω) (G k ω)
  let rB : EuclideanSpace ℝ (Fin d) → ∀ k, Ω k → ℝ :=
    fun g k ω => B (acomp g) k ω - q (acomp g) (G k ω)
  let near : EuclideanSpace ℝ (Fin d) → ∀ k, Ω k → ℝ :=
    fun g k ω => max 0 (B (acomp g) k ω - A k ω)
  have hrA : TendstoInProbZero P rA := by
    simpa only [rA, q, hVcdef] using hExpA
  have hrB (g : EuclideanSpace ℝ (Fin d)) : TendstoInProbZero P (rB g) := by
    simpa only [rB, q, hVcdef] using hExpB (acomp g)
  have hnear (g : EuclideanSpace ℝ (Fin d)) : TendstoInProbZero P (near g) := by
    simpa only [near] using hNearMax (acomp g)
  have habs {Z : ∀ k, Ω k → ℝ} (hZ : TendstoInProbZero P Z) :
      TendstoInProbZero P (fun k ω => |Z k ω|) := by
    intro ε hε
    simpa only [Real.norm_eq_abs, abs_abs] using hZ ε hε
  have hquad_cont : Continuous quad := by
    exact continuous_const.mul (continuous_id.inner Vc.continuous)
  intro ε hε
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨Mh, hMh⟩ := hhA_bdd (η / 3) (by positivity)
  obtain ⟨Mg, hMg⟩ := hG_bdd (η / 3) (by positivity)
  set small : ℝ := c * ε ^ 2 / 8 with hsmall_def
  have hsmall_pos : 0 < small := by positivity
  have hquad_cont0 : ContinuousAt quad 0 := hquad_cont.continuousAt
  obtain ⟨δx, hδx, hquad_small⟩ :=
    (Metric.continuousAt_iff.mp hquad_cont0) small hsmall_pos
  set δ : ℝ := δx / (‖Wc‖ + 1) with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨t, _htsub, htfin, htcover⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) (max Mg 0)).finite_cover_balls hδ
  let s := htfin.toFinset
  let term : EuclideanSpace ℝ (Fin d) → ∀ k, Ω k → ℝ :=
    fun g k ω => |rB g k ω| + near g k ω
  have hterm (g : EuclideanSpace ℝ (Fin d)) : TendstoInProbZero P (term g) := by
    exact TendstoInProbZero.add (habs (hrB g)) (hnear g)
  have hsum : TendstoInProbZero P (fun k ω => s.sum fun g => term g k ω) := by
    induction s using Finset.induction_on with
    | empty =>
        intro a ha
        simp only [Finset.sum_empty, norm_zero, not_le.mpr ha, Set.setOf_false,
          measureReal_empty]
        exact tendsto_const_nhds
    | @insert g s hgs ih =>
        simpa only [Finset.sum_insert hgs] using TendstoInProbZero.add (hterm g) ih
  let total : ∀ k, Ω k → ℝ :=
    fun k ω => |rA k ω| + s.sum fun g => term g k ω
  have htotal : TendstoInProbZero P total :=
    TendstoInProbZero.add (habs hrA) hsum
  set gap : ℝ := c * ε ^ 2 / 4 with hgap_def
  have hgap_pos : 0 < gap := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (htotal gap hgap_pos) (η / 3) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have hsub : { ω | ε ≤ ‖hA k ω + Wc (G k ω)‖ } ⊆
      { ω | Mh < ‖hA k ω‖ } ∪
        ({ ω | Mg < ‖G k ω‖ } ∪ { ω | gap ≤ ‖total k ω‖ }) := by
    intro ω hfar
    by_cases hAh : Mh < ‖hA k ω‖
    · exact Or.inl hAh
    refine Or.inr ?_
    by_cases hGh : Mg < ‖G k ω‖
    · exact Or.inl hGh
    refine Or.inr ?_
    have hGball : G k ω ∈ Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin d)) (max Mg 0) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (not_lt.mp hGh).trans (le_max_left _ _)
    have hcov := htcover hGball
    simp only [Set.mem_iUnion] at hcov
    obtain ⟨g, hg, hgdist⟩ := hcov
    have hgs : g ∈ s := by simpa only [s, Set.Finite.mem_toFinset] using hg
    rw [Metric.mem_ball, dist_eq_norm] at hgdist
    have hz : acomp g + Wc (G k ω) = Wc (G k ω - g) := by
      simp only [acomp, map_sub]
      abel
    have hden : 0 < ‖Wc‖ + 1 := by positivity
    have hmul : ‖G k ω - g‖ * (‖Wc‖ + 1) < δx := by
      rw [hδ_def, lt_div_iff₀ hden] at hgdist
      exact hgdist
    have hzdist : dist (acomp g + Wc (G k ω)) 0 < δx := by
      rw [dist_zero_right, hz]
      calc
        ‖Wc (G k ω - g)‖ ≤ ‖Wc‖ * ‖G k ω - g‖ := Wc.le_opNorm _
        _ < δx := by nlinarith [norm_nonneg Wc, norm_nonneg (G k ω - g)]
    have hquad_zero : quad 0 = 0 := by simp only [quad, map_zero, inner_zero_right, mul_zero]
    have hquad_net : -small < quad (acomp g + Wc (G k ω)) := by
      have hs := hquad_small hzdist
      rw [Real.dist_eq, hquad_zero, sub_zero] at hs
      exact (abs_lt.mp hs).1
    have hu_sq : ε ^ 2 ≤ ‖hA k ω + Wc (G k ω)‖ ^ 2 := by
      nlinarith [mul_le_mul hfar hfar hε.le (norm_nonneg (hA k ω + Wc (G k ω)))]
    have hquad_far : quad (hA k ω + Wc (G k ω)) ≤ -(c * ε ^ 2 / 2) := by
      have hn := hVneg (hA k ω + Wc (G k ω))
      simp only [quad]
      nlinarith [mul_le_mul_of_nonneg_left hu_sq hc.le]
    have hctsA := complete_the_square V hVunit hVsymm (hA k ω) (G k ω)
    have hctsB := complete_the_square V hVunit hVsymm (acomp g) (G k ω)
    rw [← hVcdef, ← hWcdef] at hctsA hctsB
    have hqgap : gap < q (acomp g) (G k ω) - q (hA k ω) (G k ω) := by
      simp only [q, quad] at hctsA hctsB hquad_net hquad_far ⊢
      rw [hsmall_def] at hquad_net
      rw [hgap_def]
      nlinarith [hctsA, hctsB]
    have hq_upper : q (acomp g) (G k ω) - q (hA k ω) (G k ω)
        ≤ |rA k ω| + term g k ω := by
      simp only [rA, rB, near, term]
      nlinarith [le_max_right (0 : ℝ) (B (acomp g) k ω - A k ω),
        le_abs_self (A k ω - q (hA k ω) (G k ω)),
        neg_le_abs (B (acomp g) k ω - q (acomp g) (G k ω))]
    have hterm_nonneg : ∀ x ∈ s, 0 ≤ term x k ω := by
      intro x _hx
      exact add_nonneg (abs_nonneg _) (le_max_left _ _)
    have hterm_sum : term g k ω ≤ s.sum (fun x => term x k ω) :=
      Finset.single_le_sum hterm_nonneg hgs
    have htotal_nonneg : 0 ≤ total k ω := by
      exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun x _hx => hterm_nonneg x _hx)
    simp only [Set.mem_setOf_eq]
    rw [Real.norm_eq_abs, abs_of_nonneg htotal_nonneg]
    refine le_of_lt (hqgap.trans_le ?_)
    calc
      q (acomp g) (G k ω) - q (hA k ω) (G k ω) ≤ |rA k ω| + term g k ω := hq_upper
      _ ≤ |rA k ω| + s.sum (fun x => term x k ω) := add_le_add_right hterm_sum _
      _ = total k ω := rfl
  have hmeasure : (P k).real { ω | ε ≤ ‖hA k ω + Wc (G k ω)‖ }
      ≤ (P k).real { ω | Mh < ‖hA k ω‖ }
        + ((P k).real { ω | Mg < ‖G k ω‖ }
          + (P k).real { ω | gap ≤ ‖total k ω‖ }) := by
    refine (measureReal_mono hsub).trans ?_
    calc
      (P k).real ({ ω | Mh < ‖hA k ω‖ } ∪
          ({ ω | Mg < ‖G k ω‖ } ∪ { ω | gap ≤ ‖total k ω‖ })) ≤
          (P k).real { ω | Mh < ‖hA k ω‖ } +
            (P k).real ({ ω | Mg < ‖G k ω‖ } ∪ { ω | gap ≤ ‖total k ω‖ }) :=
        measureReal_union_le _ _
      _ ≤ (P k).real { ω | Mh < ‖hA k ω‖ } +
          ((P k).real { ω | Mg < ‖G k ω‖ } +
            (P k).real { ω | gap ≤ ‖total k ω‖ }) :=
        add_le_add_right (measureReal_union_le _ _) _
  have htotal_small : (P k).real { ω | gap ≤ ‖total k ω‖ } < η / 3 := by
    have := hN k hk
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at this
  change dist ((P k).real { ω | ε ≤ ‖hA k ω + Wc (G k ω)‖ }) 0 < η
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  nlinarith [hMh k, hMg k]

end AsymptoticStatistics.MEstimator
