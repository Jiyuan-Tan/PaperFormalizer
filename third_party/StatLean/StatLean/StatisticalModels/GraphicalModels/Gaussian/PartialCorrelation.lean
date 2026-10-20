module
public import StatLean.StatisticalModels.GraphicalModels.Gaussian.Precision
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Real.Sqrt

@[expose] public section

/-!
# Partial correlations — the scaled concentration matrix

The statistical reading of the entries of the concentration matrix `K = Σ⁻¹` (Lauritzen §5.1.3,
p. 129–130, the unnumbered displays following Proposition 5.2):

* the **diagonal** entries are reciprocal conditional variances, `k_{γγ} = V(Y_γ ∣ Y_{Γ∖{γ}})⁻¹`;
* the **off-diagonal** entries, scaled so that `K` has unit diagonal, are minus the *partial
  correlation coefficients*.

* `partialCorr S γ μ` — Lauritzen's `ρ_{γμ ∣ Γ∖{γ,μ}} = −k_{γμ}/√(k_{γγ}k_{μμ})`;
* `partialCorr_eq_zero_iff` and **`condIndepCoords_gaussianCoords_iff_partialCorr_eq_zero`** —
  the chain `ρ = 0 ⟺ k_{γμ} = 0 ⟺ Y_γ ⫫ Y_μ ∣ Y_{Γ∖{γ,μ}}`;
* `precisionMatrix_diag_eq_inv_condCovMatrix` — the conditional-variance identity, p. 129;
* `neg_inv_apply_div_sqrt_eq` + `neg_precision_div_sqrt_eq_condCorr` — the reason the *minus
  sign* is there: on a two-element block, minus the scaled entry of the inverse is the ordinary
  correlation of the conditional law;
* `partialCorr_sq` — Lauritzen **(5.12)**, the determinant formula for `ρ²`.

## ⚠ The sign

**The partial correlation is MINUS the scaled precision entry.** Lauritzen defines
`c_{γμ} = k_{γμ}/√(k_{γγ}k_{μμ})` (the entries of `K` scaled to unit diagonal) and then states,
p. 130: "Then `c_{γμ}`, the off-diagonal elements in `C`, are equal to the **negative** partial
correlation coefficients", `ρ_{γμ ∣ Γ∖{γ,μ}} = −c_{γμ}`. Verified against the book text.

Sanity check that fixes the sign beyond doubt (`|Γ| = 2`, `Σ = !![a, b; b, d]`): here
`K = (ad − b²)⁻¹ · !![d, −b; −b, a]`, so
`−k_{12}/√(k_{11}k_{22}) = (b/(ad−b²)) · (ad−b²)/√(ad) = b/√(ad)`, the ordinary correlation —
whereas `+k_{12}/√(k_{11}k_{22})` would give its negative.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996 (first edition)**, §5.1.3, pp. 129–130: the identity
`k_{γγ} = V(Y_γ ∣ Y_{Γ∖{γ}})⁻¹` (unnumbered, foot of p. 129), the definition of `c_{γμ}` and the
partial correlation `ρ_{γμ ∣ Γ∖{γ,μ}} = −c_{γμ}` (unnumbered displays, p. 130), and the
determinant identity **(5.12)**, p. 130 — the only *numbered* item of the three
(`Lauritzen §5.1.3`). Page numbers and item kinds follow `notes/factor_graphical/books.md`,
whose "sign trap" entry independently records that the partial correlation is *minus* the
scaled precision entry.

**Proof formalization notes.**

*Book vs Lean, edge behaviour.* `Real.sqrt` is `0` on negatives and `x / 0 = 0` in Lean, so
`partialCorr` is total; under `S.PosDef` the diagonal `k_{γγ}` is strictly positive
(`precisionMatrix_diag_pos`), the square root is positive, and the definition is the book's. All
substantive statements therefore carry `hS : S.PosDef`.

*Book vs Lean, the diagonal.* Lauritzen scales `C` to have unit diagonal, i.e. `c_{γγ} = 1`, so
his convention forces `ρ_{γγ} = −1`. We record that as `partialCorr_self` rather than special-
casing the definition: the book's formula is used verbatim, degenerate diagonal and all.

*Book vs Lean, the two-variable displays of p. 130.* Lauritzen also records
`V(Y_γ ∣ Y_{Γ∖{γ,μ}}) = k_{μμ}/(k_{γγ}k_{μμ} − k_{γμ}²)` and
`Cov(Y_γ, Y_μ ∣ Y_{Γ∖{γ,μ}}) = −k_{γμ}/(k_{γγ}k_{μμ} − k_{γμ}²)`. These are the entries of the
explicit `2 × 2` inverse (5.11); `neg_inv_apply_div_sqrt_eq` packages exactly the combination of
them that the partial correlation needs, and the full entrywise form is the `2 × 2` adjugate
formula after a `Fin 2` reindexing.

**Bibliographic comments.** Partial correlation is K. Pearson and G. U. Yule's (1896–1907); the
identification of the scaled inverse covariance with minus the partial correlations is classical
multivariate analysis (T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*,
Wiley, 1958, §2.5). Its use as the *parametrisation* of a graphical model — zeros of the scaled
inverse being the missing edges — is A. P. Dempster's covariance selection, "Covariance
selection," *Biometrics* **28** (1972), 157–175.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels.GraphicalModels

section Defs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **partial correlation coefficient** `ρ_{γμ ∣ Γ∖{γ,μ}}` of two coordinates given all the
others (Lauritzen §5.1.3, p. 130, unnumbered display):
`ρ_{γμ ∣ Γ∖{γ,μ}} = −k_{γμ}/√(k_{γγ}k_{μμ}) = −c_{γμ}`, where `c` is `K` scaled to unit diagonal.

**The minus sign is the book's** — see the module docstring for the verification and a numerical
check.

Edge behaviour: total, by Lean's `Real.sqrt` (zero on negatives) and `x / 0 = 0`. If `S` is
singular then `precisionMatrix S = 0` and `partialCorr S γ μ = 0` vacuously, so every
substantive statement below assumes `S.PosDef`. On the diagonal the book's own scaling gives
`partialCorr S γ γ = −1` (`partialCorr_self`), not `1`. -/
noncomputable def partialCorr (S : Matrix ι ι ℝ) (i j : ι) : ℝ :=
  -(precisionMatrix S i j) / Real.sqrt (precisionMatrix S i i * precisionMatrix S j j)

end Defs

section Basic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}

/-- Symmetry of the partial correlation, from symmetry of the concentration matrix. -/
theorem partialCorr_comm
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hS : S.PosDef) (i j : ι) :
    partialCorr S i j = partialCorr S j i := by
  rw [partialCorr, partialCorr, precisionMatrix_apply_comm hS i j,
    mul_comm (precisionMatrix S i i)]

/-- Edge behaviour of the book's scaling on the diagonal: `c_{γγ} = 1`, hence
`ρ_{γγ} = −c_{γγ} = −1`. Recorded, not patched — the definition follows Lauritzen verbatim. -/
theorem partialCorr_self
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hS : S.PosDef) (i : ι) :
    partialCorr S i i = -1 := by
  have h := precisionMatrix_diag_pos hS i
  rw [partialCorr, Real.sqrt_mul_self h.le, neg_div, div_self h.ne']

/-- **The partial correlation vanishes exactly when the concentration entry does.** The scaling
`√(k_{γγ}k_{μμ})` is strictly positive for a regular `Σ`, so it cannot create or destroy zeros.
No `γ ≠ μ` hypothesis is needed: on the diagonal both sides are false. -/
theorem partialCorr_eq_zero_iff
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hS : S.PosDef) (i j : ι) :
    partialCorr S i j = 0 ↔ precisionMatrix S i j = 0 := by
  have hden : Real.sqrt (precisionMatrix S i i * precisionMatrix S j j) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr
      (mul_pos (precisionMatrix_diag_pos hS i) (precisionMatrix_diag_pos hS j)))
  rw [partialCorr, div_eq_zero_iff]
  simp [hden]

/-- **Lauritzen Proposition 5.2 in partial-correlation form** (§5.1.3, pp. 129–130): for a
regular `Σ` and `γ ≠ μ`, conditional independence of the two coordinates given all the others is
equivalent to a vanishing *partial correlation*. Composition of Proposition 5.2 with
`partialCorr_eq_zero_iff`. -/
theorem condIndepCoords_gaussianCoords_iff_partialCorr_eq_zero
    (m : EuclideanSpace ℝ ι)
    -- USER-INPUT: `Σ` regular; Lauritzen Prop. 5.2, p. 129
    (hS : S.PosDef) {i j : ι}
    -- USER-INPUT: two distinct coordinates `γ ≠ μ`; Lauritzen Prop. 5.2, p. 129
    (hij : i ≠ j) :
    CondIndepCoords (multivariateGaussian m S) gaussianCoords {i} {j} (Finset.univ \ {i, j})
      ↔ partialCorr S i j = 0 :=
  (condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero m hS hij).trans
    (partialCorr_eq_zero_iff hS i j).symm

end Basic

section ConditionalVariance

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- **The conditional-variance identity** (Lauritzen §5.1.3, p. 129, unnumbered display):
"the diagonal elements `k_{γγ}` are reciprocals of the conditional variances, given the remaining
variables", `k_{γγ} = V(Y_γ ∣ Y_{Γ∖{γ}})⁻¹`.

Stated on the sum index with a **singleton** conditioned block `ι₂` (Lauritzen's `{γ}`), where
`condCovMatrix S₁₁ S₁₂ S₂₂` is the `1 × 1` conditional covariance, i.e. the conditional variance
`V(Y_γ ∣ Y_{Γ∖{γ}})`; the general-block version is `condCovMatrix_eq_inv_submatrix_precisionMatrix`
(Lauritzen (C.3)), of which this is the `1 × 1` instance. -/
theorem precisionMatrix_diag_eq_inv_condCovMatrix
    -- LEAN-ONLY: the conditioned block is Lauritzen's singleton `{γ}`; `Subsingleton` plus the
    -- witness `a` is the type-level form of `|{γ}| = 1`, under which a `1 × 1` matrix inverse is
    -- the scalar inverse
    [Subsingleton ι₂]
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 129
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) (a : ι₂) :
    precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inr a)
      = (condCovMatrix S₁₁ S₁₂ S₂₂ a a)⁻¹ := by
  haveI : Unique ι₂ := uniqueOfSubsingleton a
  have hC : (condCovMatrix S₁₁ S₁₂ S₂₂).PosDef := posDef_condCovMatrix hJ
  have hmul : (condCovMatrix S₁₁ S₁₂ S₂₂)⁻¹ * condCovMatrix S₁₁ S₁₂ S₂₂ = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hC.isUnit)
  have hscalar : (condCovMatrix S₁₁ S₁₂ S₂₂)⁻¹ a a * condCovMatrix S₁₁ S₁₂ S₂₂ a a = 1 := by
    have h := congrFun (congrFun hmul a) a
    simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton,
      Matrix.one_apply_eq] at h
    rwa [Subsingleton.elim (default : ι₂) a] at h
  have hK := congrFun (congrFun (submatrix_precisionMatrix_fromBlocks_inr_inr S₁₁ S₁₂ S₂₂ hJ) a) a
  simp only [Matrix.submatrix_apply] at hK
  rw [hK]
  exact eq_inv_of_mul_eq_one_left hscalar

end ConditionalVariance

section TwoBySignTrap

/-- LEAN-ONLY corridor: a two-element index type is `Fin 2`, with the equivalence pinned to a
prescribed pair of distinct elements. Used to transport the explicit `2 × 2` determinant and
adjugate formulas onto an abstract index type. -/
private noncomputable def pairEquiv {ι₂ : Type*} [Fintype ι₂] [DecidableEq ι₂] {a b : ι₂}
    (hcard : Fintype.card ι₂ = 2) (hab : a ≠ b) : Fin 2 ≃ ι₂ :=
  Equiv.ofBijective ![a, b] <| by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp [hcard]⟩
    intro p q h
    fin_cases p <;> fin_cases q <;> simp_all

private theorem pairEquiv_zero {ι₂ : Type*} [Fintype ι₂] [DecidableEq ι₂] {a b : ι₂}
    (hcard : Fintype.card ι₂ = 2) (hab : a ≠ b) : pairEquiv hcard hab 0 = a := rfl

private theorem pairEquiv_one {ι₂ : Type*} [Fintype ι₂] [DecidableEq ι₂] {a b : ι₂}
    (hcard : Fintype.card ι₂ = 2) (hab : a ≠ b) : pairEquiv hcard hab 1 = b := rfl

/-- LEAN-ONLY: the explicit determinant of a matrix on an abstract two-element index type. -/
private theorem det_eq_of_card_two {ι₂ : Type*} [Fintype ι₂] [DecidableEq ι₂]
    (M : Matrix ι₂ ι₂ ℝ) (hcard : Fintype.card ι₂ = 2) {a b : ι₂} (hab : a ≠ b) :
    M.det = M a a * M b b - M a b * M b a := by
  have h := Matrix.det_submatrix_equiv_self (pairEquiv hcard hab) M
  rw [← h, Matrix.det_fin_two]
  simp [Matrix.submatrix_apply, pairEquiv_zero, pairEquiv_one]

/-- LEAN-ONLY: the explicit `2 × 2` inverse on an abstract two-element index type, transported
along `pairEquiv`. -/
private theorem inv_apply_of_card_two {ι₂ : Type*} [Fintype ι₂] [DecidableEq ι₂]
    (M : Matrix ι₂ ι₂ ℝ) (hcard : Fintype.card ι₂ = 2) {a b : ι₂} (hab : a ≠ b) :
    M⁻¹ a a = (M.det)⁻¹ * M b b ∧ M⁻¹ a b = (M.det)⁻¹ * (-(M a b)) := by
  have hsub := Matrix.inv_submatrix_equiv M (pairEquiv hcard hab) (pairEquiv hcard hab)
  have hdet : (M.submatrix (pairEquiv hcard hab) (pairEquiv hcard hab)).det = M.det :=
    Matrix.det_submatrix_equiv_self _ M
  have hform : ∀ p q : Fin 2,
      (M.submatrix (pairEquiv hcard hab) (pairEquiv hcard hab))⁻¹ p q
        = (M.det)⁻¹ * (!![M b b, -(M a b); -(M b a), M a a] p q) := by
    intro p q
    rw [Matrix.inv_def, Matrix.adjugate_fin_two, hdet]
    fin_cases p <;> fin_cases q <;>
      simp [Ring.inverse_eq_inv', Matrix.submatrix_apply, pairEquiv_zero, pairEquiv_one]
  refine ⟨?_, ?_⟩
  · have h := (congrFun (congrFun hsub 0) 0).symm
    rw [hform 0 0] at h
    simpa [pairEquiv_zero, pairEquiv_one] using h
  · have h := (congrFun (congrFun hsub 0) 1).symm
    rw [hform 0 1] at h
    simpa [pairEquiv_zero, pairEquiv_one] using h

/-- **The algebraic heart of the sign convention.** For a positive definite `2 × 2` matrix `M`,
minus the off-diagonal entry of `M⁻¹`, scaled by the geometric mean of the diagonal entries of
`M⁻¹`, is the ordinary correlation built from `M` itself.

This is `−c = ρ` stripped of all probability: apply it to `M := ` the conditional covariance
matrix on a two-element block, whose inverse is the corresponding principal submatrix of `K` by
Lauritzen (C.3), and Lauritzen's p. 130 display drops out. -/
theorem neg_inv_apply_div_sqrt_eq {ι₂ : Type*} [Fintype ι₂] [DecidableEq ι₂]
    {M : Matrix ι₂ ι₂ ℝ}
    -- USER-INPUT: regular covariance; Lauritzen §5.1.3, p. 130
    (hM : M.PosDef)
    -- USER-INPUT: exactly two variables — Lauritzen's pair `{γ, μ}`; the identity is **false**
    -- for larger blocks, where the two scalings differ by the remaining variables
    (hcard : Fintype.card ι₂ = 2) {a b : ι₂}
    -- USER-INPUT: `γ ≠ μ`; Lauritzen §5.1.3, p. 130
    (hab : a ≠ b) :
    -(M⁻¹ a b) / Real.sqrt (M⁻¹ a a * M⁻¹ b b) = M a b / Real.sqrt (M a a * M b b) := by
  obtain ⟨hinvaa, hinvab⟩ := inv_apply_of_card_two M hcard hab
  obtain ⟨hinvbb, -⟩ := inv_apply_of_card_two M hcard hab.symm
  have hd : 0 < M.det := hM.det_pos
  have hdinv : (0 : ℝ) < (M.det)⁻¹ := inv_pos.mpr hd
  have hsqrt : Real.sqrt (M⁻¹ a a * M⁻¹ b b) = (M.det)⁻¹ * Real.sqrt (M a a * M b b) := by
    rw [hinvaa, hinvbb, show (M.det)⁻¹ * M b b * ((M.det)⁻¹ * M a a)
        = ((M.det)⁻¹) ^ 2 * (M a a * M b b) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hdinv.le]
  rw [hinvab, hsqrt, show -((M.det)⁻¹ * -(M a b)) = (M.det)⁻¹ * M a b by ring]
  exact mul_div_mul_left _ _ hdinv.ne'

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- **Lauritzen p. 130, `ρ_{γμ ∣ Γ∖{γ,μ}} = −c_{γμ}`** in block form: for a joint Gaussian whose
non-conditioned block is exactly the pair `{γ, μ}`, minus the scaled entry of the concentration
matrix equals the correlation of the *conditional* law of `(Y_γ, Y_μ)` given all the rest.

The cardinality hypothesis is essential and is the book's setting, not an artefact: for a larger
second block the left-hand side conditions on the remaining coordinates of that block as well,
and the two sides genuinely differ. -/
theorem neg_precision_div_sqrt_eq_condCorr
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef)
    -- USER-INPUT: the non-conditioned block is exactly Lauritzen's pair `{γ, μ}`
    (hcard : Fintype.card ι₂ = 2) {a b : ι₂}
    -- USER-INPUT: `γ ≠ μ`; Lauritzen §5.1.3, p. 130
    (hab : a ≠ b) :
    -(precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inr b))
          / Real.sqrt (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inr a)
              * precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr b) (Sum.inr b))
      = condCovMatrix S₁₁ S₁₂ S₂₂ a b
          / Real.sqrt (condCovMatrix S₁₁ S₁₂ S₂₂ a a * condCovMatrix S₁₁ S₁₂ S₂₂ b b) := by
  have hK := submatrix_precisionMatrix_fromBlocks_inr_inr S₁₁ S₁₂ S₂₂ hJ
  have hKe : ∀ x y : ι₂,
      precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr x) (Sum.inr y)
        = (condCovMatrix S₁₁ S₁₂ S₂₂)⁻¹ x y := fun x y => congrFun (congrFun hK x) y
  rw [hKe, hKe, hKe]
  exact neg_inv_apply_div_sqrt_eq (posDef_condCovMatrix hJ) hcard hab

end TwoBySignTrap

section Identity512

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}

/-- LEAN-ONLY corridor: the index equivalence `Aᶜ ⊕ A ≃ Γ` that turns a principal-submatrix
statement into a `Matrix.fromBlocks` statement. Its two components are the subtype coercions,
so every block of `S.submatrix (splitEquiv A) (splitEquiv A)` is a `principalSubmatrix`. -/
private def splitEquiv (A : Finset ι) : ↥(Aᶜ) ⊕ ↥A ≃ ι :=
  (Equiv.sumCongr (Equiv.refl ↥(Aᶜ))
      (Equiv.subtypeEquivRight (fun x => by simp))).trans (Equiv.sumCompl (· ∈ Aᶜ))

private theorem splitEquiv_inl (A : Finset ι) (x : ↥(Aᶜ)) : splitEquiv A (Sum.inl x) = x := rfl

private theorem splitEquiv_inr (A : Finset ι) (y : ↥A) : splitEquiv A (Sum.inr y) = y := rfl

/-- **Lauritzen (C.5)** (App. C, p. 257) in principal-submatrix form: `det K_A · det Σ =
det Σ_{Γ∖A}`, i.e. the principal minor of the concentration matrix on `A` is the complementary
principal minor of `Σ` divided by `det Σ`. Applied at `A = {γ}`, `{μ}`, `{γ, μ}` this is the
"(C.5) four times" bookkeeping behind (5.12). -/
private theorem det_principalSubmatrix_precisionMatrix
    (hS : S.PosDef) (A : Finset ι) :
    (principalSubmatrix (precisionMatrix S) A).det * S.det
      = (principalSubmatrix S Aᶜ).det := by
  have hsymm : ∀ x y : ι, S x y = S y x := by
    intro x y
    have hT : Sᵀ = S := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hS.isHermitian
    have h2 : Sᵀ x y = S x y := congrFun (congrFun hT x) y
    simpa [Matrix.transpose_apply] using h2.symm
  set T₁₁ : Matrix ↥(Aᶜ) ↥(Aᶜ) ℝ := principalSubmatrix S Aᶜ with hT₁₁
  set T₁₂ : Matrix ↥(Aᶜ) ↥A ℝ :=
    S.submatrix (fun x : ↥(Aᶜ) => (x : ι)) (fun y : ↥A => (y : ι)) with hT₁₂
  set T₂₂ : Matrix ↥A ↥A ℝ := principalSubmatrix S A with hT₂₂
  have hTeq : S.submatrix (splitEquiv A) (splitEquiv A)
      = Matrix.fromBlocks T₁₁ T₁₂ T₁₂ᵀ T₂₂ := by
    ext p q
    cases p <;> cases q <;>
      simp [hT₁₁, hT₁₂, hT₂₂, principalSubmatrix, splitEquiv_inl, splitEquiv_inr, hsymm]
  have hT : (Matrix.fromBlocks T₁₁ T₁₂ T₁₂ᵀ T₂₂).PosDef :=
    hTeq ▸ posDef_submatrix_of_injective hS (splitEquiv A).injective
  haveI : Invertible T₁₁ := (posDef_of_fromBlocks_inl hT).isUnit.invertible
  have hdetT : (Matrix.fromBlocks T₁₁ T₁₂ T₁₂ᵀ T₂₂).det = S.det := by
    rw [← hTeq]; exact Matrix.det_submatrix_equiv_self _ S
  have hSdet : S.det = T₁₁.det * (condCovMatrix T₁₁ T₁₂ T₂₂).det := by
    rw [← hdetT, Matrix.det_fromBlocks₁₁, condCovMatrix, Matrix.invOf_eq_nonsing_inv]
  have hKA : principalSubmatrix (precisionMatrix S) A = (condCovMatrix T₁₁ T₁₂ T₂₂)⁻¹ := by
    rw [← submatrix_precisionMatrix_fromBlocks_inr_inr T₁₁ T₁₂ T₂₂ hT, ← hTeq]
    ext p q
    simp [principalSubmatrix, precisionMatrix_def, Matrix.inv_submatrix_equiv,
      splitEquiv_inr]
  have hcc : (condCovMatrix T₁₁ T₁₂ T₂₂).det ≠ 0 := (posDef_condCovMatrix hT).det_pos.ne'
  rw [hKA, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hSdet]
  field_simp

/-- **Lauritzen (5.12)** (§5.1.3, p. 130): the squared partial correlation in terms of principal
minors of the covariance matrix,
`ρ²_{γμ ∣ Γ∖{γ,μ}} = c²_{γμ} = 1 − (det Σ · det Σ_{Γ∖{γ,μ}}) / (det Σ_{Γ∖{γ}} · det Σ_{Γ∖{μ}})`.

Lauritzen derives it from (C.5) applied four times; `principalSubmatrix` is his `Σ_A`, with the
empty-matrix determinant `1` covering the case `Γ = {γ, μ}` (where the identity reduces to the
familiar `ρ² = 1 − det Σ / (σ_{γγ}σ_{μμ})`). -/
theorem partialCorr_sq
    -- USER-INPUT: `Σ` regular; Lauritzen (5.12), p. 130
    (hS : S.PosDef) {i j : ι}
    -- USER-INPUT: two distinct coordinates `γ ≠ μ`; Lauritzen (5.12), p. 130
    (hij : i ≠ j) :
    partialCorr S i j ^ 2
      = 1 - (S.det * (principalSubmatrix S (Finset.univ \ {i, j})).det)
            / ((principalSubmatrix S (Finset.univ \ {i})).det
                * (principalSubmatrix S (Finset.univ \ {j})).det) := by
  have hKii : 0 < precisionMatrix S i i := precisionMatrix_diag_pos hS i
  have hKjj : 0 < precisionMatrix S j j := precisionMatrix_diag_pos hS j
  have hdS : 0 < S.det := hS.det_pos
  -- (C.5) at a singleton block: `k_{γγ} · det Σ = det Σ_{Γ∖{γ}}`
  have hsingle : ∀ k : ι, precisionMatrix S k k * S.det
      = (principalSubmatrix S (Finset.univ \ {k})).det := by
    intro k
    haveI : Subsingleton ↥({k} : Finset ι) :=
      ⟨fun x y => Subtype.ext (by
        rw [Finset.mem_singleton.mp x.2, Finset.mem_singleton.mp y.2])⟩
    haveI : Unique ↥({k} : Finset ι) :=
      uniqueOfSubsingleton ⟨k, Finset.mem_singleton_self k⟩
    have h := det_principalSubmatrix_precisionMatrix hS {k}
    rw [Finset.compl_eq_univ_sdiff] at h
    rw [← h]
    congr 1
    have hd : ((default : ↥({k} : Finset ι)) : ι) = k :=
      Finset.mem_singleton.mp (default : ↥({k} : Finset ι)).2
    rw [Matrix.det_unique (principalSubmatrix (precisionMatrix S) {k})]
    simp only [principalSubmatrix, Matrix.submatrix_apply, hd]
  -- (C.5) at the pair block: `(k_{γγ}k_{μμ} − k²_{γμ}) · det Σ = det Σ_{Γ∖{γ,μ}}`
  have hpair : (precisionMatrix S i i * precisionMatrix S j j
        - precisionMatrix S i j * precisionMatrix S i j) * S.det
      = (principalSubmatrix S (Finset.univ \ {i, j})).det := by
    have hcard : Fintype.card ↥({i, j} : Finset ι) = 2 := by
      rw [Fintype.card_coe, Finset.card_pair hij]
    have hne : (⟨i, by simp⟩ : ↥({i, j} : Finset ι)) ≠ ⟨j, by simp⟩ := by
      simpa using hij
    have hdet := det_eq_of_card_two (principalSubmatrix (precisionMatrix S) {i, j}) hcard hne
    have h := det_principalSubmatrix_precisionMatrix hS {i, j}
    rw [Finset.compl_eq_univ_sdiff] at h
    rw [← h, hdet]
    simp only [principalSubmatrix, Matrix.submatrix_apply]
    rw [precisionMatrix_apply_comm hS j i]
  rw [partialCorr, div_pow, neg_sq, Real.sq_sqrt (mul_pos hKii hKjj).le,
    ← hsingle i, ← hsingle j, ← hpair]
  field_simp
  ring

end Identity512

end StatLean.StatisticalModels.GraphicalModels
