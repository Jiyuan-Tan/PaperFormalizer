module
public import StatLean.StatisticalModels.Gaussian.Conditioning
public import StatLean.StatisticalModels.Gaussian.FinCorridor
public import StatLean.StatisticalModels.GraphicalModels.Core.Coordinates
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

/-!
# The concentration (precision) matrix and Lauritzen's Proposition 5.2

The bridge between the *algebra* of a regular multivariate normal law and the *conditional
independence* vocabulary of `Core.CondIndep`: conditional independence of two coordinates given
all the others is **exactly** a vanishing entry of the inverse covariance matrix.

* `precisionMatrix S := S⁻¹` — Lauritzen's concentration matrix `K = Σ⁻¹`;
* `principalSubmatrix S A` — Lauritzen's `Σ_A`, the principal submatrix on an index block;
* `posDef_submatrix_of_injective`, `posDef_of_fromBlocks_inl/inr` — the positive-definiteness
  plumbing that lets every block statement below derive its own nondegeneracy side conditions
  instead of assuming them;
* **`submatrix_precisionMatrix_fromBlocks_inr_inr` — Lauritzen (C.3)**: the concentration matrix
  of the conditional distribution is obtained from the joint concentration matrix by *deleting*
  the rows and columns of the conditioned-on variables, i.e. it is a principal submatrix of `K`;
  equivalently `condCovMatrix … = (K₂₂)⁻¹` (`condCovMatrix_eq_inv_submatrix_precisionMatrix`,
  the matrix form of Lauritzen (5.10)–(5.11));
* `submatrix_precisionMatrix_fromBlocks_inr_inl` — Lauritzen **(C.4)**, the companion identity
  `K₂₂⁻¹ K₂₁ = −Σ₂₁Σ₁₁⁻¹`;
* `map_multivariateGaussian_fromBlocks_eq_prod_iff` — Lauritzen **Corollary C.6** in block form:
  two blocks of a regular joint Gaussian are independent iff the cross-covariance vanishes iff
  the cross-concentration vanishes;
* `gaussianCoords` — the coordinate random vector `(Y_γ)_{γ ∈ ι}` on `EuclideanSpace ℝ ι`, the
  carrier that lets `CondIndepCoords` speak about a Gaussian law;
* `precisionMatrix_submatrix_inr_inr` and its `Finset` form
  `precisionMatrix_principalSubmatrix_apply_of_row_eq_zero` — the **dual of (C.3)**:
  marginalising a block replaces `K` by its Schur complement, and a row of `K` that already
  vanishes on the deleted block survives marginalisation unchanged. This is what lets a
  conditional independence read on one index block be compared with one read on a smaller
  block, and it is the extra ingredient contraction (C4) needs;
* **`condIndepCoords_gaussianCoords_iff_blockPrecisionMatrix_eq_zero` (HEADLINE, Lauritzen
  Proposition 5.2 in block form)**: for `Σ` regular and **pairwise disjoint** blocks `A`, `B`,
  `C` with union `E`, `Y_A ⫫ Y_B ∣ Y_C ⟺ (K^E)_{AB} = 0`, where `K^E = (Σ_E)⁻¹` is the
  concentration matrix of the marginal law of `Y_E`. It is stated at a single
  `E = A ∪ B ∪ C ∪ D` shared by premises and conclusion, which is what the graphoid axioms need;
* **`condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero` (Lauritzen
  Proposition 5.2, p. 129)**: for `Σ` regular and `γ ≠ μ`,
  `Y_γ ⫫ Y_μ ∣ Y_{Γ∖{γ,μ}} ⟺ k_{γμ} = 0` — the instance `A = {γ}`, `B = {μ}`, `C = Γ ∖ {γ, μ}`
  of the block form, where `E = Γ`.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996 (first edition)**: §5.1.3 "Conditional independence", p. 129 —
Proposition 5.2 and the displays (5.10), (5.11); Appendix C, pp. 256–257 — Proposition C.5 with
(C.2) and the identities (C.3) `K₁₁⁻¹ = Σ₁₁ − Σ₁₂Σ₂₂⁻Σ₂₁` and (C.4) `K₁₁⁻¹K₁₂ = −Σ₁₂Σ₂₂⁻` on
p. 256, the determinant identity (C.5) and Corollary C.6 on p. 257
(`Lauritzen §5.1.3`, `Lauritzen App. C`). Page numbers and item kinds follow
`notes/factor_graphical/books.md`.

*Generalized versus ordinary inverse.* Lauritzen writes `Σ₂₂⁻`, "an arbitrary generalized
inverse", in (C.2)–(C.4), but his own proof of Proposition C.5 assumes `Σ` regular and then
`Σ₂₂⁻ = Σ₂₂⁻¹`. We state the regular case only, matching both his proof and the standing
hypothesis of §5.1.3.

**Proof formalization notes.**

*Book vs Lean, orientation.* Lauritzen partitions `X = (X₁, X₂)` and conditions on the
**second** block (Proposition C.5 computes the law of `X₁` given `X₂`), so his (C.3) reads
`K₁₁⁻¹ = Σ₁₁ − Σ₁₂Σ₂₂⁻¹Σ₂₁`. Here conditioning is on the **first** block:
`condCovMatrix S₁₁ S₁₂ S₂₂ = S₂₂ − S₁₂ᵀ S₁₁⁻¹ S₁₂` is the law of block `ι₂` given block `ι₁`.
Every book identity is therefore transcribed with the two blocks swapped: (C.3) becomes
`K₂₂ = (condCovMatrix …)⁻¹` and (C.4) becomes `K₂₂⁻¹ K₂₁ = −condMeanMatrix …`. Nothing else
changes.

*Book vs Lean, regularity.* Lauritzen says "`Σ` regular"; `Matrix.inv` is a junk-valued total
function (`0` at singular matrices) and `multivariateGaussian` degenerates to a Dirac mass off
the positive-semidefinite cone, so every statement below carries an explicit `PosDef`
hypothesis. `PosDef` rather than `PosSemidef`: an inverse is taken in every one of them.

*Law transfer.* Everything here is stated for the **canonical** coordinate vector
`gaussianCoords` on the Gaussian's own sample space `EuclideanSpace ℝ ι`. Transferring to an
arbitrary random vector `Y : Ω → ι → ℝ` whose law is `N(m, S)` needs the fact that `CondIndep`
depends only on the joint law of `(f, g, h)`; that is `Core.CondIndep.condIndep_congr_law`, and
the block form above uses it for exactly one purpose — to re-read a conditional independence of
`Y` on the *marginal* law of `Y_E`, which lives on a different sample space.

**Bibliographic comments.** The characterisation of conditional independence by zeros of the
inverse covariance is due to A. P. Dempster, "Covariance selection," *Biometrics* **28** (1972),
157–175, who introduced the term *covariance selection* for the resulting model class; the
matrix identities (C.3)–(C.5) are the classical Schur-complement calculus (I. Schur, 1917),
standard in multivariate analysis since T. W. Anderson, *An Introduction to Multivariate
Statistical Analysis*, Wiley, 1958, §2.5. The name *concentration matrix* is Dempster's;
*precision matrix* is the Bayesian synonym.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels.GraphicalModels

section Defs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **concentration matrix** (a.k.a. precision matrix) `K = Σ⁻¹` of a covariance matrix
(Lauritzen §5.1.3, p. 129: "Assume the covariance to be regular such that the concentration
matrix `K = Σ⁻¹` is well defined").

Edge behaviour: `Matrix.inv` is total, with the junk value `0` at every singular matrix
(`Matrix.nonsing_inv_apply_not_isUnit`). So `precisionMatrix S = 0` whenever `S` is singular,
and *every* theorem about it carries an explicit `S.PosDef` hypothesis — `PosDef` and not
`PosSemidef`, because the book's standing assumption is that `Σ` is regular. -/
noncomputable def precisionMatrix (S : Matrix ι ι ℝ) : Matrix ι ι ℝ := S⁻¹

theorem precisionMatrix_def (S : Matrix ι ι ℝ) : precisionMatrix S = S⁻¹ := rfl

/-- The **principal submatrix** `Σ_A` of `S` on an index block (Lauritzen's notation
`Σ_{Γ∖{γ}}`, `Σ_{Γ∖{γ,μ}}`, used in (5.12)).

Edge behaviour: for `A = ∅` this is the empty matrix, whose determinant is `1` — which is the
convention (5.12) needs when `Γ = {γ, μ}`. -/
noncomputable def principalSubmatrix (S : Matrix ι ι ℝ) (A : Finset ι) : Matrix A A ℝ :=
  S.submatrix (fun a => (a : ι)) (fun a => (a : ι))

end Defs

section CoordinateVector

/-- The **coordinate random vector** `Y = (Y_γ)_{γ ∈ ι}` on `EuclideanSpace ℝ ι` — the identity
map, read through the `WithLp` type synonym as a function on the index set. This is the carrier
that turns a Gaussian *measure* into the *random vector* `Y ∼ N_{|Γ|}(ξ, Σ)` of Lauritzen
§5.1.3, so that `CondIndepCoords` applies to it.

Edge behaviour: none — it is `WithLp.ofLp`, a measurable equivalence onto `ι → ℝ`
(`WithLp.measurable_ofLp`); in particular no `Fintype ι` is needed to state it. -/
def gaussianCoords {ι : Type*} : EuclideanSpace ℝ ι → ι → ℝ := fun x => WithLp.ofLp x

theorem measurable_gaussianCoords {ι : Type*} :
    Measurable (gaussianCoords (ι := ι)) :=
  WithLp.measurable_ofLp 2 _

end CoordinateVector

section Basic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}

/-- The concentration matrix of a regular covariance is itself positive definite. -/
theorem precisionMatrix_posDef
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 129
    (hS : S.PosDef) :
    (precisionMatrix S).PosDef :=
  hS.inv

/-- The diagonal of the concentration matrix is strictly positive — the well-definedness fact
behind the scaling `c_{γμ} = k_{γμ}/√(k_{γγ}k_{μμ})` of Lauritzen p. 130. -/
theorem precisionMatrix_diag_pos
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 129
    (hS : S.PosDef) (i : ι) :
    0 < precisionMatrix S i i :=
  (precisionMatrix_posDef hS).diag_pos

/-- The concentration matrix is symmetric. -/
theorem precisionMatrix_transpose
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 129
    (hS : S.PosDef) :
    (precisionMatrix S)ᵀ = precisionMatrix S := by
  have hsymm : Sᵀ = S := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hS.isHermitian
  rw [precisionMatrix_def, Matrix.transpose_nonsing_inv, hsymm]

/-- Entrywise form of `precisionMatrix_transpose`: `k_{γμ} = k_{μγ}`. -/
theorem precisionMatrix_apply_comm
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 129
    (hS : S.PosDef) (i j : ι) :
    precisionMatrix S i j = precisionMatrix S j i :=
  (congrFun (congrFun (precisionMatrix_transpose hS) i) j).symm

/-- `Σ` is recovered from `K`: the concentration and covariance matrices are mutually inverse
(Lauritzen §5.1.3, p. 129). -/
theorem precisionMatrix_precisionMatrix
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 129
    (hS : S.PosDef) :
    precisionMatrix (precisionMatrix S) = S := by
  rw [precisionMatrix_def, precisionMatrix_def,
    Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hS.isUnit)]

end Basic

section PosDefPlumbing

/-- LEAN-ONLY: a principal submatrix of a positive definite matrix along an **injective** index
map is positive definite. Injectivity is essential — a repeated index makes the
extension-by-zero of a nonzero vector cancel. -/
theorem posDef_submatrix_of_injective {n m : Type*} [Fintype n] [Fintype m]
    {M : Matrix n n ℝ}
    -- LEAN-ONLY: the ambient positive definiteness
    (hM : M.PosDef) {f : m → n}
    -- LEAN-ONLY: injectivity of the index selection; see the docstring
    (hf : Function.Injective f) :
    (M.submatrix f f).PosDef := by
  classical
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hM.1.submatrix f, fun x hx => ?_⟩
  set z : n → ℝ := Function.extend f x 0 with hz
  have hzf : ∀ a, z (f a) = x a := fun a => hf.extend_apply x 0 a
  have hz0 : ∀ i, i ∉ Set.range f → z i = 0 := fun i hi => by
    simp [hz, Function.extend_apply' _ _ _ hi]
  -- summing a function supported on the range of `f` is summing its pullback
  have hsum : ∀ g : n → ℝ, (∀ i, i ∉ Set.range f → g i = 0) →
      ∑ i, g i = ∑ a, g (f a) := by
    intro g hg
    rw [← Finset.sum_image (f := g) (g := f) (s := (Finset.univ : Finset m))
      (fun a _ b _ h => hf h)]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro i _ hi
    exact hg i (by simpa [Finset.mem_image, Set.mem_range] using hi)
  have hzne : z ≠ 0 := by
    intro h
    refine hx (funext fun a => ?_)
    have := congrFun h (f a)
    rwa [hzf a] at this
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hzne
  simp only [star_trivial] at hpos ⊢
  refine lt_of_lt_of_eq hpos ?_
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
  rw [hsum (fun i => z i * ∑ j, M i j * z j) (fun i hi => by simp [hz0 i hi])]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hzf a, hsum (fun j => M (f a) j * z j) (fun j hj => by simp [hz0 j hj])]
  exact congrArg _ (Finset.sum_congr rfl fun b _ => by rw [hzf b])

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
  {S₁₁ : Matrix ι₁ ι₁ ℝ} {S₁₂ : Matrix ι₁ ι₂ ℝ} {S₂₂ : Matrix ι₂ ι₂ ℝ}

/-- LEAN-ONLY: the first diagonal block of a regular joint covariance is regular. Derived, not
assumed — this is what lets the block theorems below take only the *joint* `PosDef` hypothesis
that Lauritzen states ("`Σ` regular"), rather than laundering the block nondegeneracy in. -/
theorem posDef_of_fromBlocks_inl
    -- LEAN-ONLY: regular joint covariance; Lauritzen §5.1.3, p. 129
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    S₁₁.PosDef := by
  have hsub : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).submatrix Sum.inl Sum.inl = S₁₁ := by
    ext i j; simp
  exact hsub ▸ posDef_submatrix_of_injective hJ (Sum.inl_injective (β := ι₂))

/-- LEAN-ONLY: the second diagonal block of a regular joint covariance is regular. -/
theorem posDef_of_fromBlocks_inr
    -- LEAN-ONLY: regular joint covariance; Lauritzen §5.1.3, p. 129
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    S₂₂.PosDef := by
  have hsub : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).submatrix Sum.inr Sum.inr = S₂₂ := by
    ext i j; simp
  exact hsub ▸ posDef_submatrix_of_injective hJ (Sum.inr_injective (α := ι₁))

/-- LEAN-ONLY: the Schur complement of a regular block covariance is regular — the conditional
covariance of a regular joint normal is itself regular, which is what makes the conditional
concentration matrix of (C.3) well defined. -/
theorem posDef_condCovMatrix
    -- LEAN-ONLY: regular joint covariance; Lauritzen App. C, (C.3)
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    (condCovMatrix S₁₁ S₁₂ S₂₂).PosDef := by
  have h₁₁ : S₁₁.PosDef := posDef_of_fromBlocks_inl hJ
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  have hconj : S₁₂ᴴ = S₁₂ᵀ := Matrix.conjTranspose_eq_transpose_of_trivial S₁₂
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨(posSemidef_condCovMatrix hJ.posSemidef h₁₁).1, fun x hx => ?_⟩
  have hne : (-((S₁₁⁻¹ * S₁₂) *ᵥ x)) ⊕ᵥ x ≠ 0 := by
    intro h
    exact hx (funext fun b => congrFun h (Sum.inr b))
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hJ).2 hne
  rw [dotProduct_mulVec, ← hconj, Matrix.schur_complement_eq₁₁ S₁₂ S₂₂ _ _ h₁₁.1,
    neg_add_cancel, dotProduct_zero, zero_add, ← dotProduct_mulVec, hconj] at hpos
  exact hpos

end PosDefPlumbing

section BlockIdentities

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- **Lauritzen (C.3), the conditional-concentration identity** (the equation is in the proof of
Proposition C.5, App. C, p. 256; the reading quoted here — "the concentration matrix of the
conditional distribution is obtained from the concentration matrix of the joint distribution by
deleting rows and columns corresponding to the variables conditioned upon" — is the remark on
p. 257). The same matrix is `K_{\{γ,μ\}}` of Lauritzen (5.10), p. 129.

In the repo's orientation the conditioned-on block is `ι₁`, so "deleting the rows and columns of
the conditioning variables" is the principal submatrix at `Sum.inr`. -/
theorem submatrix_precisionMatrix_fromBlocks_inr_inr
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen App. C, (C.3)
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inr Sum.inr
      = (condCovMatrix S₁₁ S₁₂ S₂₂)⁻¹ := by
  have h₁₁ : S₁₁.PosDef := posDef_of_fromBlocks_inl hJ
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  haveI : Invertible (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) := hJ.isUnit.invertible
  haveI : Invertible (S₂₂ - S₁₂ᵀ * ⅟S₁₁ * S₁₂) :=
    Matrix.invertibleOfFromBlocks₁₁Invertible S₁₁ S₁₂ S₁₂ᵀ S₂₂
  rw [precisionMatrix_def, ← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₁₁_eq]
  simp only [Matrix.invOf_eq_nonsing_inv]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, condCovMatrix]

/-- **Lauritzen (C.3) read as (5.10)–(5.11)**: the conditional covariance is the inverse of the
principal submatrix of the joint concentration matrix on the conditioned block. -/
theorem condCovMatrix_eq_inv_submatrix_precisionMatrix
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen App. C, (C.3)
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    condCovMatrix S₁₁ S₁₂ S₂₂
      = ((precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inr Sum.inr)⁻¹ := by
  rw [submatrix_precisionMatrix_fromBlocks_inr_inr S₁₁ S₁₂ S₂₂ hJ,
    Matrix.nonsing_inv_nonsing_inv _
      (Matrix.isUnit_iff_isUnit_det _ |>.mp (posDef_condCovMatrix hJ).isUnit)]

/-- **Lauritzen (C.4)** (App. C, p. 256: `K₁₁⁻¹K₁₂ = −Σ₁₂Σ₂₂⁻`), transcribed with the blocks
swapped: the off-diagonal block of the concentration matrix, scaled by the conditional
covariance, is minus the Gaussian regression matrix `condMeanMatrix S₁₁ S₁₂ = S₂₁S₁₁⁻¹`. This is
the identity behind the partial regression coefficient `β_{γμ} = −k_{γμ}/k_{γγ}`. -/
theorem submatrix_precisionMatrix_fromBlocks_inr_inl
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen App. C, (C.4)
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inr Sum.inl
      = -((condCovMatrix S₁₁ S₁₂ S₂₂)⁻¹ * condMeanMatrix S₁₁ S₁₂) := by
  have h₁₁ : S₁₁.PosDef := posDef_of_fromBlocks_inl hJ
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  haveI : Invertible (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) := hJ.isUnit.invertible
  haveI : Invertible (S₂₂ - S₁₂ᵀ * ⅟S₁₁ * S₁₂) :=
    Matrix.invertibleOfFromBlocks₁₁Invertible S₁₁ S₁₂ S₁₂ᵀ S₂₂
  rw [precisionMatrix_def, ← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₁₁_eq]
  simp only [Matrix.invOf_eq_nonsing_inv]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.neg_apply,
    condCovMatrix, condMeanMatrix, ← Matrix.mul_assoc]

/-- **Lauritzen Corollary C.6, matrix half** (p. 257: "If `Σ` is regular, this holds if and only
if `K₁₂ = 0`"): the cross-concentration block vanishes exactly when the cross-covariance block
does. Immediate from (C.4), both factors being invertible. -/
theorem submatrix_precisionMatrix_fromBlocks_inl_inr_eq_zero_iff
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen Cor. C.6
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inl Sum.inr = 0
      ↔ S₁₂ = 0 := by
  have h₁₁ : S₁₁.PosDef := posDef_of_fromBlocks_inl hJ
  have hcc : (condCovMatrix S₁₁ S₁₂ S₂₂).PosDef := posDef_condCovMatrix hJ
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  haveI : Invertible (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) := hJ.isUnit.invertible
  haveI : Invertible (S₂₂ - S₁₂ᵀ * ⅟S₁₁ * S₁₂) :=
    Matrix.invertibleOfFromBlocks₁₁Invertible S₁₁ S₁₂ S₁₂ᵀ S₂₂
  have hblock : (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inl Sum.inr
      = -(S₁₁⁻¹ * S₁₂ * (condCovMatrix S₁₁ S₁₂ S₂₂)⁻¹) := by
    rw [precisionMatrix_def, ← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₁₁_eq]
    simp only [Matrix.invOf_eq_nonsing_inv]
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply,
      condCovMatrix]
  have hu1 : IsUnit S₁₁.det := (Matrix.isUnit_iff_isUnit_det _).mp h₁₁.isUnit
  have hu2 : IsUnit (condCovMatrix S₁₁ S₁₂ S₂₂).det := (Matrix.isUnit_iff_isUnit_det _).mp hcc.isUnit
  rw [hblock, neg_eq_zero]
  constructor
  · intro h
    have h2 : S₁₁ * (S₁₁⁻¹ * S₁₂ * (condCovMatrix S₁₁ S₁₂ S₂₂)⁻¹) * condCovMatrix S₁₁ S₁₂ S₂₂
        = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu2, Matrix.mul_one] at h2
    exact h2
  · intro h; simp [h]

/-- **Lauritzen Corollary C.6** (p. 257) in measure-level form: two blocks of a regular joint
Gaussian are independent — the joint law transported to the product space is the product of the
block marginals — iff the cross-concentration block vanishes.

The `⟸` direction is that a Gaussian with vanishing cross-covariance splits as a product, once
`submatrix_precisionMatrix_fromBlocks_inl_inr_eq_zero_iff` turns `K₁₂ = 0` into `S₁₂ = 0`; the
`⟹` direction reads the covariance off the product law (the covariance of a product measure is
block diagonal). -/
theorem map_multivariateGaussian_fromBlocks_eq_prod_iff
    (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen Cor. C.6
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    (multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
          (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))
        = (multivariateGaussian m₁ S₁₁).prod (multivariateGaussian m₂ S₂₂)
      ↔ (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inl Sum.inr = 0 := by
  have h₁₁ : S₁₁.PosDef := posDef_of_fromBlocks_inl hJ
  have h₂₂ : S₂₂.PosDef := posDef_of_fromBlocks_inr hJ
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  -- the diagonal joint covariance is a genuine covariance
  have hJ0 : (Matrix.fromBlocks S₁₁ (0 : Matrix ι₁ ι₂ ℝ) (0 : Matrix ι₁ ι₂ ℝ)ᵀ S₂₂).PosSemidef := by
    have := (Matrix.PosDef.fromBlocks₁₁ (A := S₁₁) (0 : Matrix ι₁ ι₂ ℝ) S₂₂ h₁₁).mpr
      (by simpa using h₂₂.posSemidef)
    simpa using this
  have hsplit : (multivariateGaussian (blockPair m₁ m₂)
        (Matrix.fromBlocks S₁₁ (0 : Matrix ι₁ ι₂ ℝ) (0 : Matrix ι₁ ι₂ ℝ)ᵀ S₂₂)).map
          (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))
      = (multivariateGaussian m₁ S₁₁).prod (multivariateGaussian m₂ S₂₂) := by
    simpa using multivariateGaussian_fromBlocks_prod m₁ m₂ S₁₁ S₂₂ h₁₁.posSemidef h₂₂.posSemidef
  rw [submatrix_precisionMatrix_fromBlocks_inl_inr_eq_zero_iff S₁₁ S₁₂ S₂₂ hJ]
  constructor
  · -- read the covariance off the product law
    intro hprod
    have hlaw : multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)
        = multivariateGaussian (blockPair m₁ m₂)
            (Matrix.fromBlocks S₁₁ (0 : Matrix ι₁ ι₂ ℝ) (0 : Matrix ι₁ ι₂ ℝ)ᵀ S₂₂) :=
      ext_of_map_sumMeasEquivProd (hprod.trans hsplit.symm)
    have hcov := congrArg covMatrix hlaw
    rw [covMatrix_multivariateGaussian _ _ hJ.posSemidef,
      covMatrix_multivariateGaussian _ _ hJ0] at hcov
    ext i j
    have := congrFun (congrFun hcov (Sum.inl i)) (Sum.inr j)
    simpa using this
  · intro h
    subst h
    exact hsplit

end BlockIdentities

section Proposition52

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- LEAN-ONLY corridor for the block form of Proposition 5.2: the index equivalence
`C ⊕ (A ⊕ B) ≃ A ∪ B ∪ C` for pairwise disjoint blocks. The conditioning block comes **first**,
because the Gaussian disintegration conditions on the first block. Its three components are the
subtype coercions, so the transported coordinate vector's
blocks are *definitionally* the `coords` sub-vectors of `Core.Coordinates` — which is what makes
the coordinate identification below a `rfl`. -/
private noncomputable def blockSplitE {ι : Type*} [DecidableEq ι] {A B C E : Finset ι}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (hE : A ∪ B ∪ C = E) :
    ↥C ⊕ (↥A ⊕ ↥B) ≃ ↥E := by
  refine Equiv.ofBijective
    (Sum.elim (fun x : ↥C => (⟨(x : ι), hE ▸ Finset.mem_union_right _ x.2⟩ : ↥E))
      (Sum.elim (fun x : ↥A => (⟨(x : ι), hE ▸ Finset.mem_union_left _
          (Finset.mem_union_left _ x.2)⟩ : ↥E))
        (fun x : ↥B => (⟨(x : ι), hE ▸ Finset.mem_union_left _
          (Finset.mem_union_right _ x.2)⟩ : ↥E)))) ⟨?_, ?_⟩
  · rintro (x | (x | x)) (y | (y | y)) h <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact absurd (h ▸ y.2) (Finset.disjoint_right.mp hAC x.2)
    · exact absurd (h ▸ y.2) (Finset.disjoint_right.mp hBC x.2)
    · exact absurd (h ▸ x.2) (Finset.disjoint_right.mp hAC y.2)
    · exact congrArg (fun z => Sum.inr (Sum.inl z)) (Subtype.ext h)
    · exact absurd (h ▸ y.2) (Finset.disjoint_left.mp hAB x.2)
    · exact absurd (h ▸ x.2) (Finset.disjoint_right.mp hBC y.2)
    · exact absurd (h ▸ x.2) (Finset.disjoint_left.mp hAB y.2)
    · exact congrArg (fun z => Sum.inr (Sum.inr z)) (Subtype.ext h)
  · rintro ⟨y, hy⟩
    rw [← hE] at hy
    rcases Finset.mem_union.mp hy with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact ⟨Sum.inr (Sum.inl ⟨y, h⟩), rfl⟩
      · exact ⟨Sum.inr (Sum.inr ⟨y, h⟩), rfl⟩
    · exact ⟨Sum.inl ⟨y, h⟩, rfl⟩

/-- LEAN-ONLY corridor: a `Finset` and its complement split the index type. Again the components
are the subtype coercions, so composites reduce definitionally. -/
private noncomputable def compSplit {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Finset ι) :
    ↥E ⊕ ↥(Eᶜ) ≃ ι := by
  refine Equiv.ofBijective (Sum.elim (fun x : ↥E => (x : ι)) (fun x : ↥(Eᶜ) => (x : ι))) ⟨?_, ?_⟩
  · rintro (x | x) (y | y) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact absurd (h ▸ y.2) (by simp)
    · exact absurd (h ▸ x.2) (by simp)
    · exact congrArg Sum.inr (Subtype.ext h)
  · intro y
    by_cases hy : y ∈ E
    · exact ⟨Sum.inl ⟨y, hy⟩, rfl⟩
    · exact ⟨Sum.inr ⟨y, by simpa using hy⟩, rfl⟩

/-- LEAN-ONLY corridor: the full four-block split `(C ⊕ (A ⊕ B)) ⊕ (A ∪ B ∪ C)ᶜ ≃ Γ`. The last
block is what gets **marginalised away**; the first three are the blocks of the statement. -/
private noncomputable def blockSplit4 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B C E : Finset ι} (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hE : A ∪ B ∪ C = E) :
    (↥C ⊕ (↥A ⊕ ↥B)) ⊕ ↥(Eᶜ) ≃ ι :=
  ((blockSplitE hAB hAC hBC hE).sumCongr (Equiv.refl ↥(Eᶜ))).trans (compSplit E)

/-- LEAN-ONLY: pushing a `⊗ₘ` forward along a measurable equivalence of the *first* factor. -/
private theorem map_compProd_prodMap_left {α α' β : Type*} [MeasurableSpace α]
    [MeasurableSpace α'] [MeasurableSpace β] (ν : Measure α) [SFinite ν]
    (κ : Kernel α β) [IsSFiniteKernel κ] (f : α ≃ᵐ α') :
    (ν ⊗ₘ κ).map (Prod.map f id) = (ν.map f) ⊗ₘ (κ.comap f.symm f.symm.measurable) := by
  have hfm : Measurable (Prod.map (f : α → α') (id : β → β)) :=
    f.measurable.prodMap measurable_id
  ext s hs
  rw [Measure.map_apply hfm hs, Measure.compProd_apply (hfm hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) f.measurable]
  refine lintegral_congr fun a => ?_
  rw [Kernel.comap_apply, MeasurableEquiv.symm_apply_apply]
  rfl

/-- LEAN-ONLY: a positive definite matrix on a sum index is its own block decomposition, with
the lower-left block the transpose of the upper-right one. -/
private theorem eq_fromBlocks_of_posDef {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    {Q : Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℝ} (hQ : Q.PosDef) :
    Q = Matrix.fromBlocks (Q.submatrix Sum.inl Sum.inl) (Q.submatrix Sum.inl Sum.inr)
      (Q.submatrix Sum.inl Sum.inr)ᵀ (Q.submatrix Sum.inr Sum.inr) := by
  have hsymm : ∀ x y, Q x y = Q y x := by
    intro x y
    have hT : Qᵀ = Q := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hQ.isHermitian
    have h2 : Qᵀ x y = Q x y := congrFun (congrFun hT x) y
    simpa [Matrix.transpose_apply] using h2.symm
  ext p q
  cases p <;> cases q <;> simp [Matrix.transpose_apply, hsymm]

/-- **The analytic core of Proposition 5.2**, stated on a sum index with the conditioning block
first: for a regular Gaussian on `EuclideanSpace ℝ (κ_C ⊕ (κ_A ⊕ κ_B))`, the middle block is
conditionally independent of the last given the first **iff** the corresponding rectangle of the
concentration matrix vanishes.

Everything Lauritzen's proof of Proposition 5.2 does happens here, and only here; both the
pairwise Proposition 5.2 and its block form below are index transports of this statement.

*Proof sketch (Lauritzen's own: "almost a direct consequence of Proposition C.5 and its proof",
p. 129).*
1. the Gaussian disintegration writes the law as `N(m₁, T₁₁) ⊗ₘ gaussianCondKernel …`, whose
   conditional covariance `Q = condCovMatrix T₁₁ T₁₂ T₂₂` does **not** depend on the conditioning
   value — this is what makes the disintegration a *product* kernel and hence `CondIndep`;
2. (C.3) identifies `Q⁻¹` with the principal submatrix of the joint concentration matrix on the
   conditioned block — Lauritzen (5.10);
3. Corollary C.6 applied *inside* the conditional law splits it into a product over the two
   sub-blocks iff its cross-concentration vanishes;
4. the `CondIndep` witnesses are the two block marginals of the conditional kernel
   (`Kernel.map` of `gaussianCondKernel` along the two projections), which are Markov; the `⟹`
   direction identifies the anonymous witnesses of `CondIndep` with them by a.e. uniqueness of
   the conditional kernel. -/
private theorem condIndep_blockProj_iff_precisionMatrix_eq_zero {kC kA kB : Type*}
    [Fintype kC] [Fintype kA] [Fintype kB] [DecidableEq kC] [DecidableEq kA] [DecidableEq kB]
    (n : EuclideanSpace ℝ (kC ⊕ (kA ⊕ kB)))
    {T : Matrix (kC ⊕ (kA ⊕ kB)) (kC ⊕ (kA ⊕ kB)) ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen Prop. 5.2, p. 129
    (hT : T.PosDef) :
    CondIndep (multivariateGaussian n T)
        (fun y => WithLp.ofLp (blockFst (blockSnd y)))
        (fun y => WithLp.ofLp (blockSnd (blockSnd y)))
        (fun y => WithLp.ofLp (blockFst y))
      ↔ ∀ (a : kA) (b : kB),
          precisionMatrix T (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) = 0 := by
  classical
  set T₁₁ := T.submatrix Sum.inl Sum.inl with hT₁₁
  set T₁₂ := T.submatrix Sum.inl Sum.inr with hT₁₂
  set T₂₂ := T.submatrix Sum.inr Sum.inr with hT₂₂
  have hTb : T = Matrix.fromBlocks T₁₁ T₁₂ T₁₂ᵀ T₂₂ := eq_fromBlocks_of_posDef hT
  have hTJ : (Matrix.fromBlocks T₁₁ T₁₂ T₁₂ᵀ T₂₂).PosDef := hTb ▸ hT
  set m₁ := blockFst n with hm₁def
  set m₂ := blockSnd n with hm₂def
  have hnb : n = blockPair m₁ m₂ := (blockPair_blockFst_blockSnd _).symm
  set Kcond := gaussianCondKernel m₁ m₂ T₁₁ T₁₂ T₂₂ with hKconddef
  have hdisint : multivariateGaussian m₁ T₁₁ ⊗ₘ Kcond
      = (multivariateGaussian n T).map (sumMeasEquivProd) := by
    rw [hKconddef]
    conv_rhs => rw [hnb, hTb]
    exact compProd_gaussianCondKernel m₁ m₂ T₁₁ T₁₂ T₂₂ hTJ.posSemidef
      (posDef_of_fromBlocks_inl hTJ)
  -- the measurable-equivalence plumbing between `EuclideanSpace` and the plain function types
  set fC : EuclideanSpace ℝ kC ≃ᵐ (kC → ℝ) := (MeasurableEquiv.toLp 2 (kC → ℝ)).symm with hfCdef
  set Θ₂ : EuclideanSpace ℝ (kA ⊕ kB) → ((kA → ℝ) × (kB → ℝ)) :=
    fun v => (WithLp.ofLp (blockFst v), WithLp.ofLp (blockSnd v)) with hΘ₂def
  have hΘ₂meas : Measurable Θ₂ :=
    ((WithLp.measurable_ofLp 2 _).comp blockFst.continuous.measurable).prodMk
      ((WithLp.measurable_ofLp 2 _).comp blockSnd.continuous.measurable)
  have hsum : Measurable (sumMeasEquivProd (ι₁ := kC) (ι₂ := kA ⊕ kB)) :=
    (sumMeasEquivProd (ι₁ := kC) (ι₂ := kA ⊕ kB)).measurable
  have hpm : Measurable (Prod.map (fC : EuclideanSpace ℝ kC → (kC → ℝ)) Θ₂) :=
    fC.measurable.prodMap hΘ₂meas
  have hpm1 : Measurable (Prod.map (fC : EuclideanSpace ℝ kC → (kC → ℝ))
      (id : ((kA → ℝ) × (kB → ℝ)) → _)) := fC.measurable.prodMap measurable_id
  have hpm2 : Measurable (Prod.map (id : EuclideanSpace ℝ kC → _) Θ₂) :=
    measurable_id.prodMap hΘ₂meas
  -- MASTER IDENTITY: the joint law of the three coordinate blocks
  have hmaster : (multivariateGaussian n T).map (fun y =>
        (WithLp.ofLp (blockFst y), (WithLp.ofLp (blockFst (blockSnd y)),
          WithLp.ofLp (blockSnd (blockSnd y)))))
      = ((multivariateGaussian m₁ T₁₁).map fC)
          ⊗ₘ ((Kcond.map Θ₂).comap fC.symm fC.symm.measurable) := by
    have step1 : (multivariateGaussian n T).map (fun y =>
          (WithLp.ofLp (blockFst y), (WithLp.ofLp (blockFst (blockSnd y)),
            WithLp.ofLp (blockSnd (blockSnd y)))))
        = (multivariateGaussian m₁ T₁₁ ⊗ₘ Kcond).map (Prod.map (fC : _ → _) Θ₂) := by
      rw [hdisint, Measure.map_map hpm hsum]
      rfl
    have step2 : (multivariateGaussian m₁ T₁₁ ⊗ₘ Kcond).map (Prod.map (fC : _ → _) Θ₂)
        = ((multivariateGaussian m₁ T₁₁ ⊗ₘ Kcond).map (Prod.map id Θ₂)).map
            (Prod.map (fC : _ → _) id) := by
      rw [Measure.map_map hpm1 hpm2]
      rfl
    rw [step1, step2, ← Measure.compProd_map hΘ₂meas, map_compProd_prodMap_left]
  -- the conditioning variable's law
  have hν : (multivariateGaussian n T).map (fun y => WithLp.ofLp (blockFst y))
      = (multivariateGaussian m₁ T₁₁).map fC := by
    have h1 : (fun y : EuclideanSpace ℝ (kC ⊕ (kA ⊕ kB)) => WithLp.ofLp (blockFst y))
        = (fC : EuclideanSpace ℝ kC → (kC → ℝ)) ∘ (blockFst (ι₁ := kC) (ι₂ := kA ⊕ kB)) := rfl
    rw [h1, ← Measure.map_map fC.measurable blockFst.continuous.measurable]
    congr 1
    conv_lhs => rw [hnb, hTb]
    exact multivariateGaussian_map_blockFst m₁ m₂ T₁₁ T₁₂ T₂₂ hTJ.posSemidef
  -- ## the conditional covariance on the `(κ_A ⊕ κ_B)` block and its blocks
  set Q := condCovMatrix T₁₁ T₁₂ T₂₂ with hQdef
  have hQpd : Q.PosDef := posDef_condCovMatrix hTJ
  set Q₁₁ := Q.submatrix Sum.inl Sum.inl with hQ₁₁
  set Q₁₂ := Q.submatrix Sum.inl Sum.inr with hQ₁₂
  set Q₂₂ := Q.submatrix Sum.inr Sum.inr with hQ₂₂
  have hQb : Q = Matrix.fromBlocks Q₁₁ Q₁₂ Q₁₂ᵀ Q₂₂ := eq_fromBlocks_of_posDef hQpd
  have hQJ : (Matrix.fromBlocks Q₁₁ Q₁₂ Q₁₂ᵀ Q₂₂).PosDef := hQb ▸ hQpd
  -- Lauritzen (5.10): the cross entries of `K` are entries of the conditional concentration
  have hkey : ∀ (a : kA) (b : kB),
      precisionMatrix (Matrix.fromBlocks Q₁₁ Q₁₂ Q₁₂ᵀ Q₂₂) (Sum.inl a) (Sum.inr b)
        = precisionMatrix T (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) := by
    intro a b
    have h1 := submatrix_precisionMatrix_fromBlocks_inr_inr T₁₁ T₁₂ T₂₂ hTJ
    have h2 : precisionMatrix Q (Sum.inl a) (Sum.inr b)
        = precisionMatrix (Matrix.fromBlocks T₁₁ T₁₂ T₁₂ᵀ T₂₂)
            (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) :=
      (congrFun (congrFun h1 (Sum.inl a)) (Sum.inr b)).symm
    rw [← hQb, h2, ← hTb]
  have hzeroiff :
      (precisionMatrix (Matrix.fromBlocks Q₁₁ Q₁₂ Q₁₂ᵀ Q₂₂)).submatrix Sum.inl Sum.inr = 0
        ↔ ∀ (a : kA) (b : kB),
            precisionMatrix T (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) = 0 := by
    constructor
    · intro h a b
      rw [← hkey a b]
      simpa using congrFun (congrFun h a) b
    · intro h
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.zero_apply]
      rw [hkey a b, h a b]
  -- Lauritzen Corollary C.6 inside the conditional law
  have hgauss : ∀ (n₁ : EuclideanSpace ℝ kA) (n₂ : EuclideanSpace ℝ kB),
      ((multivariateGaussian (blockPair n₁ n₂) Q).map sumMeasEquivProd
          = (multivariateGaussian n₁ Q₁₁).prod (multivariateGaussian n₂ Q₂₂))
        ↔ (precisionMatrix (Matrix.fromBlocks Q₁₁ Q₁₂ Q₁₂ᵀ Q₂₂)).submatrix Sum.inl Sum.inr
            = 0 := by
    intro n₁ n₂
    rw [hQb]
    exact map_multivariateGaussian_fromBlocks_eq_prod_iff n₁ n₂ Q₁₁ Q₁₂ Q₂₂ hQJ
  have hKap : ∀ x : EuclideanSpace ℝ kC,
      ∃ nn : EuclideanSpace ℝ (kA ⊕ kB), Kcond x = multivariateGaussian nn Q := fun x =>
    ⟨_, by rw [hKconddef, gaussianCondKernel_apply]⟩
  -- the two coordinate projections of the pair block
  set fI : EuclideanSpace ℝ kA ≃ᵐ (kA → ℝ) := (MeasurableEquiv.toLp 2 (kA → ℝ)).symm with hfIdef
  set fJ : EuclideanSpace ℝ kB ≃ᵐ (kB → ℝ) := (MeasurableEquiv.toLp 2 (kB → ℝ)).symm with hfJdef
  set pI : EuclideanSpace ℝ (kA ⊕ kB) → (kA → ℝ) :=
    fun v => WithLp.ofLp (blockFst v) with hpIdef
  set pJ : EuclideanSpace ℝ (kA ⊕ kB) → (kB → ℝ) :=
    fun v => WithLp.ofLp (blockSnd v) with hpJdef
  have hpImeas : Measurable pI :=
    (WithLp.measurable_ofLp 2 _).comp blockFst.continuous.measurable
  have hpJmeas : Measurable pJ :=
    (WithLp.measurable_ofLp 2 _).comp blockSnd.continuous.measurable
  have hsum2 : Measurable (sumMeasEquivProd (ι₁ := kA) (ι₂ := kB)) :=
    (sumMeasEquivProd (ι₁ := kA) (ι₂ := kB)).measurable
  have hfIJ : Measurable (Prod.map (fI : _ → _) (fJ : _ → _)) :=
    fI.measurable.prodMap fJ.measurable
  have hΘ₂comp : Θ₂ = (Prod.map (fI : _ → _) (fJ : _ → _)) ∘
      ⇑(sumMeasEquivProd (ι₁ := kA) (ι₂ := kB)) := rfl
  -- the two block marginals of the conditional law
  have hmargI : ∀ (n₁ : EuclideanSpace ℝ kA) (n₂ : EuclideanSpace ℝ kB),
      (multivariateGaussian (blockPair n₁ n₂) Q).map pI
        = (multivariateGaussian n₁ Q₁₁).map fI := by
    intro n₁ n₂
    rw [show pI = (fI : _ → _) ∘ (blockFst (ι₁ := kA) (ι₂ := kB)) from rfl,
      ← Measure.map_map fI.measurable blockFst.continuous.measurable, hQb,
      multivariateGaussian_map_blockFst n₁ n₂ Q₁₁ Q₁₂ Q₂₂ hQJ.posSemidef]
  have hmargJ : ∀ (n₁ : EuclideanSpace ℝ kA) (n₂ : EuclideanSpace ℝ kB),
      (multivariateGaussian (blockPair n₁ n₂) Q).map pJ
        = (multivariateGaussian n₂ Q₂₂).map fJ := by
    intro n₁ n₂
    rw [show pJ = (fJ : _ → _) ∘ (blockSnd (ι₁ := kA) (ι₂ := kB)) from rfl,
      ← Measure.map_map fJ.measurable blockSnd.continuous.measurable, hQb,
      multivariateGaussian_map_blockSnd n₁ n₂ Q₁₁ Q₁₂ Q₂₂ hQJ.posSemidef]
  haveI : IsMarkovKernel (Kcond.map pI) := Kernel.IsMarkovKernel.map _ hpImeas
  haveI : IsMarkovKernel (Kcond.map pJ) := Kernel.IsMarkovKernel.map _ hpJmeas
  haveI : IsMarkovKernel (Kcond.map Θ₂) := Kernel.IsMarkovKernel.map _ hΘ₂meas
  haveI : IsProbabilityMeasure ((multivariateGaussian m₁ T₁₁).map fC) :=
    Measure.isProbabilityMeasure_map fC.measurable.aemeasurable
  constructor
  · -- ⟹ : conditional independence forces the concentration entries to vanish
    rintro ⟨κ, η, hκ, hη, heq⟩
    rw [hmaster, hν] at heq
    set ν := (multivariateGaussian m₁ T₁₁).map fC with hνdef
    set Kbig := (Kcond.map Θ₂).comap fC.symm fC.symm.measurable with hKbigdef
    have hfst : (ν ⊗ₘ Kbig).fst = ν := Measure.fst_compProd _ _
    have e1 : ∀ᵐ x ∂(ν ⊗ₘ Kbig).fst, Kbig x = (ν ⊗ₘ Kbig).condKernel x :=
      eq_condKernel_of_measure_eq_compProd Kbig (by rw [hfst])
    have e2 : ∀ᵐ x ∂(ν ⊗ₘ Kbig).fst, (κ ×ₖ η) x = (ν ⊗ₘ Kbig).condKernel x :=
      eq_condKernel_of_measure_eq_compProd (κ ×ₖ η) (by rw [hfst]; exact heq)
    have hboth := e1.and e2
    rw [hfst] at hboth
    obtain ⟨c, hc1, hc2⟩ := hboth.exists
    have hc : (κ ×ₖ η) c = Kbig c := hc2.trans hc1.symm
    rw [hKbigdef] at hc
    rw [Kernel.prod_apply, Kernel.comap_apply, Kernel.map_apply _ hΘ₂meas] at hc
    obtain ⟨nn, hn⟩ := hKap (fC.symm c)
    have hn' : Kcond (fC.symm c)
        = multivariateGaussian (blockPair (blockFst nn) (blockSnd nn)) Q := by
      rw [hn, blockPair_blockFst_blockSnd]
    rw [hn', hΘ₂comp, ← Measure.map_map hfIJ hsum2] at hc
    have hid : (Prod.map (fI.symm : _ → _) (fJ.symm : _ → _)) ∘
        (Prod.map (fI : _ → _) (fJ : _ → _)) = id := by
      funext p
      simp [Prod.map]
    have hc2 : ((κ c).map fI.symm).prod ((η c).map fJ.symm)
        = (multivariateGaussian (blockPair (blockFst nn) (blockSnd nn)) Q).map
            (sumMeasEquivProd (ι₁ := kA) (ι₂ := kB)) := by
      have hmapped := congrArg
        (fun ρ => Measure.map (Prod.map (fI.symm : _ → _) (fJ.symm : _ → _)) ρ) hc
      simp only at hmapped
      rw [← Measure.map_prod_map _ _ fI.symm.measurable fJ.symm.measurable,
        Measure.map_map (fI.symm.measurable.prodMap fJ.symm.measurable) hfIJ, hid,
        Measure.map_id] at hmapped
      exact hmapped
    haveI : IsProbabilityMeasure ((κ c).map fI.symm) :=
      Measure.isProbabilityMeasure_map fI.symm.measurable.aemeasurable
    haveI : IsProbabilityMeasure ((η c).map fJ.symm) :=
      Measure.isProbabilityMeasure_map fJ.symm.measurable.aemeasurable
    have hA : (κ c).map fI.symm = multivariateGaussian (blockFst nn) Q₁₁ := by
      have hfst : Measure.map Prod.fst (((κ c).map fI.symm).prod ((η c).map fJ.symm))
          = (κ c).map fI.symm := Measure.fst_prod
      rw [← hfst, hc2, Measure.map_map measurable_fst hsum2, hQb]
      exact multivariateGaussian_map_blockFst _ _ Q₁₁ Q₁₂ Q₂₂ hQJ.posSemidef
    have hB : (η c).map fJ.symm = multivariateGaussian (blockSnd nn) Q₂₂ := by
      have hsnd : Measure.map Prod.snd (((κ c).map fI.symm).prod ((η c).map fJ.symm))
          = (η c).map fJ.symm := Measure.snd_prod
      rw [← hsnd, hc2, Measure.map_map measurable_snd hsum2, hQb]
      exact multivariateGaussian_map_blockSnd _ _ Q₁₁ Q₁₂ Q₂₂ hQJ.posSemidef
    rw [hA, hB] at hc2
    exact hzeroiff.mp ((hgauss (blockFst nn) (blockSnd nn)).mp hc2.symm)
  · -- ⟸ : vanishing concentration entries give an explicit product disintegration
    intro hzero
    have hz2 : (precisionMatrix (Matrix.fromBlocks Q₁₁ Q₁₂ Q₁₂ᵀ Q₂₂)).submatrix Sum.inl Sum.inr
        = 0 := hzeroiff.mpr hzero
    refine ⟨(Kcond.map pI).comap fC.symm fC.symm.measurable,
      (Kcond.map pJ).comap fC.symm fC.symm.measurable, inferInstance, inferInstance, ?_⟩
    rw [hmaster, hν]
    congr 1
    refine Kernel.ext fun c => ?_
    obtain ⟨nn, hn⟩ := hKap (fC.symm c)
    have hn' : Kcond (fC.symm c)
        = multivariateGaussian (blockPair (blockFst nn) (blockSnd nn)) Q := by
      rw [hn, blockPair_blockFst_blockSnd]
    rw [Kernel.comap_apply, Kernel.prod_apply, Kernel.comap_apply, Kernel.comap_apply,
      Kernel.map_apply _ hΘ₂meas, Kernel.map_apply _ hpImeas, Kernel.map_apply _ hpJmeas,
      hn', hmargI, hmargJ, hΘ₂comp, ← Measure.map_map hfIJ hsum2,
      (hgauss (blockFst nn) (blockSnd nn)).mpr hz2,
      ← Measure.map_prod_map _ _ fI.measurable fJ.measurable]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **HEADLINE — Lauritzen Proposition 5.2 in block form** (*Graphical Models*, 1996, §5.1.3,
p. 129, at general blocks rather than a pair of coordinates).

Let `Y ∼ N_{|Γ|}(ξ, Σ)` with `Σ` regular and let `A`, `B`, `C` be **pairwise disjoint** blocks
with union `E`. Write `K^E = (Σ_E)⁻¹` for the concentration matrix of the principal submatrix on
`E` — equivalently of the marginal law of `Y_E`. Then

`Y_A ⫫ Y_B ∣ Y_C  ⟺  (K^E)_{AB} = 0`.

For `A = {γ}`, `B = {μ}`, `C = Γ ∖ {γ, μ}` this is `E = Γ` and the pairwise Proposition 5.2
(`condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero`, derived from this below).

*Why `E` is a parameter with `hE : A ∪ B ∪ C = E` rather than the literal union.* The index type
`↥E` — and hence the *type* of `K^E` — depends on `E`, so two presentations of the same union
(`A ∪ (B ∪ D) ∪ C` and `A ∪ B ∪ (C ∪ D)`, say) would give propositionally equal but not
syntactically equal blocks and force a dependent transport at every use. Taking `E` as a
parameter lets the graphoid axioms fix **one** `E` and read all their premises and conclusions
on it, which is exactly what makes (C3) and (C5) bookkeeping.

*Proof sketch.* Marginalise, then apply the analytic core. `blockSplit4` transports `Σ` to the
four-block index `(C ⊕ (A ⊕ B)) ⊕ Eᶜ`; deleting the `Eᶜ` block — the *marginal* of a Gaussian
being the principal submatrix, which is where `Σ_E` comes from — leaves the conditional
independence to be re-read on the marginalised law, the two triples having the same joint law by
construction. The concentration entries transport back along `Matrix.inv_submatrix_equiv`. -/
theorem condIndepCoords_gaussianCoords_iff_blockPrecisionMatrix_eq_zero
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen Prop. 5.2, p. 129
    (hS : S.PosDef) {A B C E : Finset ι}
    -- USER-INPUT: Lauritzen's blocks are disjoint; §3.1, p. 29 and §5.1.3, p. 129
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    -- USER-INPUT: the index block carrying the marginal law, i.e. `E = A ∪ B ∪ C`
    (hE : A ∪ B ∪ C = E) :
    CondIndepCoords (multivariateGaussian m S) gaussianCoords A B C
      ↔ ∀ (a b : ↥E), (a : ι) ∈ A → (b : ι) ∈ B →
          precisionMatrix (principalSubmatrix S E) a b = 0 := by
  classical
  set eb := blockSplitE hAB hAC hBC hE with hebdef
  set e := blockSplit4 hAB hAC hBC hE with hedef
  set Φ := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm with hΦdef
  set T := S.submatrix e e with hTdef
  have hT : T.PosDef := posDef_submatrix_of_injective hS e.injective
  have hΦmeas : Measurable (Φ : EuclideanSpace ℝ ι → _) := Φ.continuous.measurable
  have hmap : (multivariateGaussian m S).map Φ = multivariateGaussian (Φ m) T := by
    have h := multivariateGaussian_map_reindex e.symm m S hS.posSemidef
    simpa [hTdef, hΦdef] using h
  set T₁₁ := T.submatrix Sum.inl Sum.inl with hT₁₁def
  set T₁₂ := T.submatrix Sum.inl Sum.inr with hT₁₂def
  set T₂₂ := T.submatrix Sum.inr Sum.inr with hT₂₂def
  have hTb : T = Matrix.fromBlocks T₁₁ T₁₂ T₁₂ᵀ T₂₂ := eq_fromBlocks_of_posDef hT
  have hTJ : (Matrix.fromBlocks T₁₁ T₁₂ T₁₂ᵀ T₂₂).PosDef := hTb ▸ hT
  have hT₁₁ : T₁₁.PosDef := posDef_of_fromBlocks_inl hTJ
  -- the law of the `E`-block: a Gaussian marginal is the principal submatrix
  have hmargE : ((multivariateGaussian m S).map Φ).map
        (blockFst (ι₁ := ↥C ⊕ (↥A ⊕ ↥B)) (ι₂ := ↥(Eᶜ)))
      = multivariateGaussian (blockFst (Φ m)) T₁₁ := by
    rw [hmap]
    conv_lhs => rw [show Φ m = blockPair (blockFst (Φ m)) (blockSnd (Φ m)) from
      (blockPair_blockFst_blockSnd _).symm, hTb]
    exact multivariateGaussian_map_blockFst _ _ T₁₁ T₁₂ T₂₂ hTJ.posSemidef
  have hmeas1 : Measurable (fun ω : EuclideanSpace ℝ ι => (coords C gaussianCoords ω,
      (coords A gaussianCoords ω, coords B gaussianCoords ω))) :=
    (measurable_coords C measurable_gaussianCoords).prodMk
      ((measurable_coords A measurable_gaussianCoords).prodMk
        (measurable_coords B measurable_gaussianCoords))
  have hmeas2 : Measurable (fun y : EuclideanSpace ℝ (↥C ⊕ (↥A ⊕ ↥B)) =>
      (WithLp.ofLp (blockFst y), (WithLp.ofLp (blockFst (blockSnd y)),
        WithLp.ofLp (blockSnd (blockSnd y))))) :=
    ((WithLp.measurable_ofLp 2 _).comp blockFst.continuous.measurable).prodMk
      ((((WithLp.measurable_ofLp 2 _).comp blockFst.continuous.measurable).comp
          blockSnd.continuous.measurable).prodMk
        (((WithLp.measurable_ofLp 2 _).comp blockSnd.continuous.measurable).comp
          blockSnd.continuous.measurable))
  -- the coordinate blocks on `Γ` and the projections on the transported marginal are the same
  -- random elements: their joint laws agree
  have htriple : (multivariateGaussian m S).map (fun ω => (coords C gaussianCoords ω,
        (coords A gaussianCoords ω, coords B gaussianCoords ω)))
      = (multivariateGaussian (blockFst (Φ m)) T₁₁).map (fun y =>
          (WithLp.ofLp (blockFst y), (WithLp.ofLp (blockFst (blockSnd y)),
            WithLp.ofLp (blockSnd (blockSnd y))))) := by
    rw [← hmargE, Measure.map_map hmeas2 blockFst.continuous.measurable,
      Measure.map_map (hmeas2.comp blockFst.continuous.measurable) hΦmeas]
    rfl
  rw [CondIndepCoords, condIndep_congr_law hmeas1 hmeas2 htriple,
    condIndep_blockProj_iff_precisionMatrix_eq_zero _ hT₁₁]
  -- transport the concentration entries back to the principal submatrix on `E`
  have hsub : T₁₁ = (principalSubmatrix S E).submatrix eb eb := rfl
  have hentry : ∀ p q : ↥C ⊕ (↥A ⊕ ↥B),
      precisionMatrix T₁₁ p q = precisionMatrix (principalSubmatrix S E) (eb p) (eb q) := by
    intro p q
    rw [hsub, precisionMatrix_def, Matrix.inv_submatrix_equiv]
    rfl
  constructor
  · intro h a b ha hb
    have h1 : eb (Sum.inr (Sum.inl ⟨(a : ι), ha⟩)) = a := Subtype.ext rfl
    have h2 : eb (Sum.inr (Sum.inr ⟨(b : ι), hb⟩)) = b := Subtype.ext rfl
    have h3 := h ⟨(a : ι), ha⟩ ⟨(b : ι), hb⟩
    rw [hentry, h1, h2] at h3
    exact h3
  · intro h a b
    rw [hentry]
    exact h _ _ a.2 b.2

/-- **HEADLINE — Lauritzen Proposition 5.2** (*Graphical Models*, 1996, §5.1.3, p. 129).

Let `Y ∼ N_{|Γ|}(ξ, Σ)` with `Σ` regular, and let `K = {k_{αβ}} = Σ⁻¹` be its concentration
matrix. Then for two distinct coordinates `γ ≠ μ`,
`Y_γ ⫫ Y_μ ∣ Y_{Γ∖{γ,μ}}  ⟺  k_{γμ} = 0`.

This is the fundamental relation on which every model of Lauritzen ch. 5 rests: "Corresponding
to the different Markov properties studied in Chapter 3, we have multivariate normal models
defined through restricting particular elements in suitable concentration matrices to be equal
to zero" (p. 129).

The conditional independence is stated with the contracted `CondIndepCoords` of
`Core.Coordinates` for the canonical coordinate vector `gaussianCoords` on the Gaussian's own
sample space. The degenerate case `Γ = {γ, μ}` (empty conditioning block) is included and is
Corollary C.6.

The conditioning block is written `Finset.univ \ {i, j}` rather than `({i, j} : Finset ι)ᶜ` so
that this theorem lands **syntactically on the nose** of the pairwise Markov property.

*Proof sketch.* The instance `A = {γ}`, `B = {μ}`, `C = Γ ∖ {γ, μ}` of the block form above, whose
index block is then all of `Γ`; `Matrix.inv_submatrix_equiv` along `Equiv.subtypeUnivEquiv`
identifies `K^Γ` with `K`. -/
theorem condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen Prop. 5.2, p. 129
    (hS : S.PosDef) {i j : ι}
    -- USER-INPUT: two distinct coordinates `γ ≠ μ`; Lauritzen Prop. 5.2, p. 129
    (hij : i ≠ j) :
    CondIndepCoords (multivariateGaussian m S) gaussianCoords {i} {j} (Finset.univ \ {i, j})
      ↔ precisionMatrix S i j = 0 := by
  classical
  have hAB : Disjoint ({i} : Finset ι) {j} := Finset.disjoint_singleton.mpr hij
  have hAC : Disjoint ({i} : Finset ι) (Finset.univ \ {i, j}) :=
    Finset.disjoint_singleton_left.mpr (by simp)
  have hBC : Disjoint ({j} : Finset ι) (Finset.univ \ {i, j}) :=
    Finset.disjoint_singleton_left.mpr (by simp)
  have hE : ({i} : Finset ι) ∪ {j} ∪ (Finset.univ \ {i, j}) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, true_iff]
    tauto
  rw [condIndepCoords_gaussianCoords_iff_blockPrecisionMatrix_eq_zero m hS hAB hAC hBC hE]
  -- the principal submatrix on all of `Γ` is `Σ` itself, reindexed
  set u : ↥(Finset.univ : Finset ι) ≃ ι := Equiv.subtypeUnivEquiv Finset.mem_univ with hudef
  have hsub : principalSubmatrix S (Finset.univ : Finset ι) = S.submatrix u u := rfl
  have hentry : ∀ p q : ↥(Finset.univ : Finset ι),
      precisionMatrix (principalSubmatrix S (Finset.univ : Finset ι)) p q
        = precisionMatrix S (u p) (u q) := by
    intro p q
    rw [hsub, precisionMatrix_def, Matrix.inv_submatrix_equiv]
    rfl
  constructor
  · intro h
    have h3 := h ⟨i, Finset.mem_univ i⟩ ⟨j, Finset.mem_univ j⟩ (Finset.mem_singleton_self i)
      (Finset.mem_singleton_self j)
    rwa [hentry] at h3
  · intro h a b ha hb
    rw [Finset.mem_singleton] at ha hb
    rw [hentry]
    have hua : u a = i := ha
    have hub : u b = j := hb
    rw [hua, hub]
    exact h

end Proposition52

section Marginalisation

/-! ### Marginalisation is Schur complementation of the concentration matrix

The dual of Lauritzen (C.3). (C.3) says the concentration matrix of a **conditional** law is a
*principal submatrix* of the joint concentration matrix (delete the rows and columns of the
conditioned-on variables). Applying it to `K` in place of `Σ` gives the companion statement for
**marginal** laws: the concentration matrix of a marginal is a *Schur complement* of the joint
concentration matrix. The two together are what make the graphoid axioms
provable — the block form of Proposition 5.2 reads a conditional independence off `K^E` for the
block `E` carrying the statement, and contraction (C4) is the one axiom whose two premises live
on *different* blocks, so it needs to compare `K^E` with `K^{E''}` for `E'' ⊆ E`. -/

variable {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂]

/-- **Marginalisation is Schur complementation of the concentration matrix** — the dual of
Lauritzen (C.3), and its immediate consequence: apply (C.3) to `K = Σ⁻¹` instead of to `Σ`, and
turn `K⁻¹` back into `Σ`.

In words: deleting the `κ₁` block from a regular joint law replaces `K` by
`K₂₂ − K₂₁K₁₁⁻¹K₁₂`, the Schur complement of its `κ₁` block. -/
theorem precisionMatrix_submatrix_inr_inr {M : Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen App. C
    (hM : M.PosDef) :
    precisionMatrix (M.submatrix Sum.inr Sum.inr)
      = condCovMatrix ((precisionMatrix M).submatrix Sum.inl Sum.inl)
          ((precisionMatrix M).submatrix Sum.inl Sum.inr)
          ((precisionMatrix M).submatrix Sum.inr Sum.inr) := by
  have hKpd : (precisionMatrix M).PosDef := precisionMatrix_posDef hM
  set K₁₁ := (precisionMatrix M).submatrix Sum.inl Sum.inl with hK₁₁
  set K₁₂ := (precisionMatrix M).submatrix Sum.inl Sum.inr with hK₁₂
  set K₂₂ := (precisionMatrix M).submatrix Sum.inr Sum.inr with hK₂₂
  have hKb : precisionMatrix M = Matrix.fromBlocks K₁₁ K₁₂ K₁₂ᵀ K₂₂ :=
    eq_fromBlocks_of_posDef hKpd
  have hKJ : (Matrix.fromBlocks K₁₁ K₁₂ K₁₂ᵀ K₂₂).PosDef := hKb ▸ hKpd
  have h1 := submatrix_precisionMatrix_fromBlocks_inr_inr K₁₁ K₁₂ K₂₂ hKJ
  rw [← hKb, precisionMatrix_precisionMatrix hM] at h1
  rw [h1, precisionMatrix_def, Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (posDef_condCovMatrix hKJ).isUnit)]

/-- **A zero row survives marginalisation.** If row `a` of the joint concentration matrix
vanishes on the block about to be deleted, then the whole of row `a` is unchanged by the
deletion: the Schur correction term `K₂₁K₁₁⁻¹K₁₂` has a zero row at `a`.

This is the step that makes contraction (C4) work: its first premise `(K^E)_{AB} = 0` is
*exactly* the hypothesis that kills the correction term produced by deleting `B`. -/
theorem precisionMatrix_submatrix_apply_of_row_eq_zero {M : Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen App. C
    (hM : M.PosDef) {a : κ₂}
    -- USER-INPUT: row `a` of `K` vanishes on the deleted block
    (hzero : ∀ b : κ₁, precisionMatrix M (Sum.inr a) (Sum.inl b) = 0) (x : κ₂) :
    precisionMatrix (M.submatrix Sum.inr Sum.inr) a x
      = precisionMatrix M (Sum.inr a) (Sum.inr x) := by
  rw [precisionMatrix_submatrix_inr_inr hM, condCovMatrix]
  have hrow : ∀ y : κ₁, (((precisionMatrix M).submatrix Sum.inl Sum.inr)ᵀ
      * ((precisionMatrix M).submatrix Sum.inl Sum.inl)⁻¹) a y = 0 := by
    intro y
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hb : ((precisionMatrix M).submatrix Sum.inl Sum.inr)ᵀ a b = 0 := by
      have hsymm : precisionMatrix M (Sum.inl b) (Sum.inr a)
          = precisionMatrix M (Sum.inr a) (Sum.inl b) :=
        precisionMatrix_apply_comm hM _ _
      simpa [Matrix.transpose_apply, hsymm] using hzero b
    rw [hb, zero_mul]
  have hcorr : (((precisionMatrix M).submatrix Sum.inl Sum.inr)ᵀ
      * ((precisionMatrix M).submatrix Sum.inl Sum.inl)⁻¹
      * ((precisionMatrix M).submatrix Sum.inl Sum.inr)) a x = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun y _ => by rw [hrow y, zero_mul]
  simp only [Matrix.sub_apply, hcorr, sub_zero, Matrix.submatrix_apply]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- LEAN-ONLY corridor: a sub-block and its relative complement split a `Finset`, with the
**deleted** block first (matching the orientation of `precisionMatrix_submatrix_inr_inr`). Built
from subtype coercions, so the induced submatrix identities are `rfl`. -/
private noncomputable def sdiffSplit {F E : Finset ι} (hFE : F ⊆ E) : ↥(E \ F) ⊕ ↥F ≃ ↥E := by
  refine Equiv.ofBijective
    (Sum.elim (fun x : ↥(E \ F) => (⟨(x : ι), (Finset.mem_sdiff.mp x.2).1⟩ : ↥E))
      (fun x : ↥F => (⟨(x : ι), hFE x.2⟩ : ↥E))) ⟨?_, ?_⟩
  · rintro (x | x) (y | y) h <;> simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact absurd (h ▸ y.2) (Finset.mem_sdiff.mp x.2).2
    · exact absurd (h ▸ x.2) (Finset.mem_sdiff.mp y.2).2
    · exact congrArg Sum.inr (Subtype.ext h)
  · rintro ⟨y, hy⟩
    by_cases h : y ∈ F
    · exact ⟨Sum.inr ⟨y, h⟩, rfl⟩
    · exact ⟨Sum.inl ⟨y, Finset.mem_sdiff.mpr ⟨hy, h⟩⟩, rfl⟩

/-- **A zero row survives marginalisation, at index blocks.** The `Finset` form of
`precisionMatrix_submatrix_apply_of_row_eq_zero`: if row `a` of `K^E` vanishes outside a
sub-block `F ⊆ E`, then `K^F` and `K^E` agree on the whole of row `a`.

This is what links the two premises of contraction (C4), which live on the different blocks
`E = A ∪ B ∪ C ∪ D` and `F = A ∪ C ∪ D`. -/
theorem precisionMatrix_principalSubmatrix_apply_of_row_eq_zero {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 129
    (hS : S.PosDef) {F E : Finset ι}
    -- USER-INPUT: the surviving block sits inside the ambient one
    (hFE : F ⊆ E) {a : ι} (ha : a ∈ F)
    -- USER-INPUT: row `a` of `K^E` vanishes on the deleted part `E ∖ F`
    (hzero : ∀ b : ↥E, (b : ι) ∉ F →
      precisionMatrix (principalSubmatrix S E) ⟨a, hFE ha⟩ b = 0)
    {x : ι} (hx : x ∈ F) :
    precisionMatrix (principalSubmatrix S F) ⟨a, ha⟩ ⟨x, hx⟩
      = precisionMatrix (principalSubmatrix S E) ⟨a, hFE ha⟩ ⟨x, hFE hx⟩ := by
  classical
  set ep := sdiffSplit hFE with hepdef
  have hSE : (principalSubmatrix S E).PosDef :=
    posDef_submatrix_of_injective hS (fun p q h => Subtype.ext h)
  set M := (principalSubmatrix S E).submatrix ep ep with hMdef
  have hM : M.PosDef := posDef_submatrix_of_injective hSE ep.injective
  have hentry : ∀ p q, precisionMatrix M p q
      = precisionMatrix (principalSubmatrix S E) (ep p) (ep q) := by
    intro p q
    rw [hMdef, precisionMatrix_def, Matrix.inv_submatrix_equiv]
    rfl
  have hMsub : M.submatrix Sum.inr Sum.inr = principalSubmatrix S F := rfl
  have hrow : ∀ b : ↥(E \ F), precisionMatrix M (Sum.inr ⟨a, ha⟩) (Sum.inl b) = 0 := by
    intro b
    rw [hentry]
    have h1 : ep (Sum.inr ⟨a, ha⟩) = (⟨a, hFE ha⟩ : ↥E) := Subtype.ext rfl
    rw [h1]
    exact hzero _ (Finset.mem_sdiff.mp b.2).2
  have hstep := precisionMatrix_submatrix_apply_of_row_eq_zero hM hrow (⟨x, hx⟩ : ↥F)
  rw [hMsub, hentry] at hstep
  have h1 : ep (Sum.inr ⟨a, ha⟩) = (⟨a, hFE ha⟩ : ↥E) := Subtype.ext rfl
  have h2 : ep (Sum.inr ⟨x, hx⟩) = (⟨x, hFE hx⟩ : ↥E) := Subtype.ext rfl
  rw [hstep, h1, h2]

end Marginalisation

end StatLean.StatisticalModels.GraphicalModels
