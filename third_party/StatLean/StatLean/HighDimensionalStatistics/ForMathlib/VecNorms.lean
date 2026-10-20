module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Fintype.Order

@[expose] public section

/-!
# ℓ¹ and ℓ∞ vector norms on `EuclideanSpace ℝ (Fin d)`

Theorem-agnostic bricks (`ForMathlib` layer) used by the Lasso / OLS rate
proofs (Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Ch7 Ordinary Least Squares / Ch10 Statistical
Properties of Lasso): the ℓ¹ and ℓ∞ vector norms, the
Hölder pairing `|⟨x,y⟩| ≤ ‖x‖₁ ‖y‖∞`, the support-restriction operator
`x ↦ x|_S`, and the `√|S|`-bound `‖x|_S‖₁ ≤ √|S| · ‖x‖₂`.

Design choice: vectors live in `EuclideanSpace ℝ (Fin d)` (the ambient
ℓ²/inner-product space used everywhere else in the library). We do **not**
stack additional `PiLp p`/`WithLp p` instances on the same carrier — that
creates instance diamonds — and instead expose ℓ¹ / ℓ∞ as explicit functions
defined coordinate-wise via `x.ofLp`.

For `d = 0` the index set is empty: every quantity below collapses to `0`
(`Real.sSup_empty : sSup ∅ = 0`), and all inequalities hold trivially.
-/

namespace StatLean.HighDimensionalStatistics

open scoped InnerProductSpace
open Finset

variable {d : ℕ}

/-- ℓ¹ vector norm on `EuclideanSpace ℝ (Fin d)`: formalizes the textbook
`‖x‖₁ = ∑ᵢ |xᵢ|`. Defined as an explicit function (not a `PiLp 1`
instance) to avoid an instance diamond with the ambient ℓ² inner-product
structure. -/
def l1Norm (x : EuclideanSpace ℝ (Fin d)) : ℝ := ∑ i, |x.ofLp i|

/-- ℓ∞ vector norm on `EuclideanSpace ℝ (Fin d)`: formalizes the textbook
`‖x‖∞ = supᵢ |xᵢ|`. Defined via `iSup` over a finite index set so the
value is unconditionally a real number; the range `Set.range (fun i => |x.ofLp i|)`
is finite and hence `BddAbove`, so `iSup` agrees with the finite maximum
whenever `Fin d` is nonempty. For `d = 0` the value is
`sSup ∅ = 0` (Mathlib convention on ℝ). -/
noncomputable def linfNorm (x : EuclideanSpace ℝ (Fin d)) : ℝ := ⨆ i, |x.ofLp i|

@[simp] lemma l1Norm_nonneg (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ l1Norm x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Each coordinate is dominated by the ℓ∞ norm. -/
lemma abs_le_linfNorm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |x.ofLp i| ≤ linfNorm x := by
  unfold linfNorm
  exact le_ciSup (Set.finite_range (fun j : Fin d => |x.ofLp j|)).bddAbove i

lemma linfNorm_nonneg (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ linfNorm x := by
  by_cases h : Nonempty (Fin d)
  · obtain ⟨i⟩ := h
    exact (abs_nonneg _).trans (abs_le_linfNorm x i)
  · rw [not_nonempty_iff] at h
    haveI : IsEmpty (Fin d) := h
    have heq : linfNorm x = 0 := by
      change sSup (Set.range (fun i : Fin d => |x.ofLp i|)) = 0
      rw [Set.range_eq_empty_iff.mpr ‹_›, Real.sSup_empty]
    linarith

/-- Hölder / ℓ¹–ℓ∞ duality (Lu, *Big Data Analysis* (Springer, 2025), Ch10 Statistical Properties of Lasso): for `x y : EuclideanSpace ℝ (Fin d)`,
`|⟪x, y⟫_ℝ| ≤ ‖x‖₁ · ‖y‖∞`. -/
theorem abs_inner_le_l1Norm_mul_linfNorm (x y : EuclideanSpace ℝ (Fin d)) :
    |⟪x, y⟫_ℝ| ≤ l1Norm x * linfNorm y := by
  have hinner : (⟪x, y⟫_ℝ : ℝ) = ∑ i, x.ofLp i * y.ofLp i := by
    simp only [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- ⟪a, b⟫_ℝ = b * conj a = b * a defeq (RCLike.inner_apply is rfl)
    change y.ofLp i * x.ofLp i = x.ofLp i * y.ofLp i
    ring
  rw [hinner]
  calc |∑ i, x.ofLp i * y.ofLp i|
      ≤ ∑ i, |x.ofLp i * y.ofLp i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |x.ofLp i| * |y.ofLp i| := by
        refine Finset.sum_congr rfl ?_
        intro i _; exact abs_mul _ _
    _ ≤ ∑ i, |x.ofLp i| * linfNorm y :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (abs_le_linfNorm y i) (abs_nonneg _)
    _ = (∑ i, |x.ofLp i|) * linfNorm y := by rw [← Finset.sum_mul]
    _ = l1Norm x * linfNorm y := rfl

/-- Coordinate form of the Hölder bound, often the more directly usable shape:
`|∑ᵢ xᵢ yᵢ| ≤ (∑ᵢ |xᵢ|) · supᵢ |yᵢ|`. -/
theorem abs_sum_mul_le_l1Norm_mul_linfNorm (x y : EuclideanSpace ℝ (Fin d)) :
    |∑ i, x.ofLp i * y.ofLp i| ≤ (∑ i, |x.ofLp i|) * ⨆ i, |y.ofLp i| := by
  have h := abs_inner_le_l1Norm_mul_linfNorm x y
  have hinner : (⟪x, y⟫_ℝ : ℝ) = ∑ i, x.ofLp i * y.ofLp i := by
    simp only [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- ⟪a, b⟫_ℝ = b * conj a = b * a defeq (RCLike.inner_apply is rfl)
    change y.ofLp i * x.ofLp i = x.ofLp i * y.ofLp i
    ring
  rw [hinner] at h
  exact h

/-- Support-restriction operator: zero out coordinates outside `S`.
Used in Lasso / sparse-recovery analyses (Lu, *Big Data Analysis* (Springer, 2025), Ch10 Statistical Properties of Lasso). -/
def restrict (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => if i ∈ S then x.ofLp i else 0)

@[simp] lemma restrict_ofLp_apply
    (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (restrict S x).ofLp i = if i ∈ S then x.ofLp i else 0 := by
  unfold restrict
  rw [WithLp.ofLp_toLp]

/-- `‖x|_S‖₂ ≤ ‖x‖₂`: the support restriction shrinks the ℓ² norm. -/
lemma norm_restrict_le_norm (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    ‖restrict S x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum ?_
  intro i _
  rw [restrict_ofLp_apply]
  split_ifs with h
  · exact le_refl _
  · simp [Real.norm_eq_abs, sq_nonneg]

/-- `‖x|_S‖₁ = ∑_{i ∈ S} |xᵢ|`. -/
lemma l1Norm_restrict_eq_sum (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    l1Norm (restrict S x) = ∑ i ∈ S, |x.ofLp i| := by
  unfold l1Norm
  have h1 : ∀ i, |(restrict S x).ofLp i| = if i ∈ S then |x.ofLp i| else 0 := by
    intro i
    rw [restrict_ofLp_apply]
    split_ifs <;> simp
  simp_rw [h1]
  exact Fintype.sum_ite_mem S _

/-- √s ℓ¹–ℓ² bound on the support (Lu, *Big Data Analysis* (Springer, 2025), Ch10 Statistical Properties of Lasso):
`‖x|_S‖₁ ≤ √|S| · ‖x‖₂`. Proof: Cauchy–Schwarz with the all-ones vector on `S`
gives `(∑_{i∈S} |xᵢ|)² ≤ |S| · ∑_{i∈S} xᵢ²`; taking square roots and bounding
`∑_{i∈S} xᵢ² ≤ ∑ᵢ xᵢ² = ‖x‖²` yields the claim. The Mathlib brick is
`Finset.sum_mul_sq_le_sq_mul_sq` (polynomial Cauchy–Schwarz over a finset). -/
theorem l1Norm_restrict_le_sqrt_card_mul_norm
    (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    l1Norm (restrict S x) ≤ Real.sqrt (S.card : ℝ) * ‖x‖ := by
  rw [l1Norm_restrict_eq_sum]
  set f : Fin d → ℝ := fun i => x.ofLp i with hf
  -- Cauchy–Schwarz applied to (1, |f|) on `S`:
  have hCS :
      (∑ i ∈ S, |f i|) ^ 2 ≤ (S.card : ℝ) * (∑ i ∈ S, (f i) ^ 2) := by
    have key := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => |f i|)
    -- LHS: (∑ i ∈ S, 1 * |f i|)² = (∑ i ∈ S, |f i|)²
    -- RHS: (∑ i ∈ S, 1²) * (∑ i ∈ S, |f i|²) = |S| * ∑ i ∈ S, (f i)²
    simp only [one_mul, one_pow, Finset.sum_const, Nat.smul_one_eq_cast, sq_abs] at key
    exact key
  -- Nonnegativity prerequisites for taking square roots.
  have h_sum_abs_nonneg : 0 ≤ ∑ i ∈ S, |f i| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h_card_nonneg : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have h_sum_sq_nonneg : 0 ≤ ∑ i ∈ S, (f i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- Take √ of `hCS` and rewrite both sides.
  have h1 : ∑ i ∈ S, |f i| ≤
      Real.sqrt ((S.card : ℝ) * (∑ i ∈ S, (f i) ^ 2)) := by
    have := Real.sqrt_le_sqrt hCS
    rwa [Real.sqrt_sq h_sum_abs_nonneg] at this
  rw [Real.sqrt_mul h_card_nonneg] at h1
  -- Bound `∑_{i∈S} (f i)² ≤ ∑ᵢ (f i)² = ‖x‖²`, then take √ and combine.
  have h_sub : ∑ i ∈ S, (f i) ^ 2 ≤ ∑ i, (f i) ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  have h_normsq : ‖x‖ = Real.sqrt (∑ i, (f i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [hf, Real.norm_eq_abs, sq_abs]
  refine h1.trans ?_
  rw [h_normsq]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h_sub) (Real.sqrt_nonneg _)

/-! ## Additional bricks for compressed sensing (Lu, *Big Data Analysis* (Springer, 2025), Ch8 Compressive Sensing – Ch9 Restricted Isometry Property) -/

/-- The ℓ² norm as the square root of the sum of squared `.ofLp` coordinates. -/
private lemma norm_eq_sqrt_sum_ofLp (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ = Real.sqrt (∑ i, (v.ofLp i) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.norm_eq_abs, sq_abs]

/-- ℓ¹ triangle inequality: `‖x + y‖₁ ≤ ‖x‖₁ + ‖y‖₁`. -/
theorem l1Norm_add_le (x y : EuclideanSpace ℝ (Fin d)) :
    l1Norm (x + y) ≤ l1Norm x + l1Norm y := by
  unfold l1Norm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [WithLp.ofLp_add, Pi.add_apply]
  exact abs_add_le _ _

/-- ℓ¹ norm is invariant under negation: `‖-x‖₁ = ‖x‖₁`. -/
theorem l1Norm_neg (x : EuclideanSpace ℝ (Fin d)) : l1Norm (-x) = l1Norm x := by
  unfold l1Norm
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [WithLp.ofLp_neg, Pi.neg_apply, abs_neg]

/-- Reverse triangle inequality for the ℓ¹ norm: `‖a‖₁ - ‖b‖₁ ≤ ‖a + b‖₁`. -/
theorem l1Norm_sub_le (a b : EuclideanSpace ℝ (Fin d)) :
    l1Norm a - l1Norm b ≤ l1Norm (a + b) := by
  have h := l1Norm_add_le (a + b) (-b)
  rw [add_neg_cancel_right, l1Norm_neg] at h
  linarith

/-- The restriction operator is additive: `(x + y)|_S = x|_S + y|_S`. -/
theorem restrict_add (S : Finset (Fin d)) (x y : EuclideanSpace ℝ (Fin d)) :
    restrict S (x + y) = restrict S x + restrict S y := by
  apply WithLp.ofLp_injective 2
  funext i
  simp only [WithLp.ofLp_add, Pi.add_apply, restrict_ofLp_apply]
  split_ifs <;> simp

/-- If `x` is supported on `S` (`xᵢ = 0` off `S`) then `x|_S = x`. -/
theorem restrict_eq_self (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ i ∉ S, x.ofLp i = 0) : restrict S x = x := by
  apply WithLp.ofLp_injective 2
  funext i
  rw [restrict_ofLp_apply]
  split_ifs with hi
  · rfl
  · exact (h i hi).symm

/-- The ℓ¹ norm of the zero vector is `0`. -/
@[simp] theorem l1Norm_zero : l1Norm (0 : EuclideanSpace ℝ (Fin d)) = 0 := by
  unfold l1Norm
  simp

/-- If `x` is supported on `S` then its restriction to the complement vanishes. -/
theorem restrict_compl_eq_zero (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ i ∉ S, x.ofLp i = 0) : restrict Sᶜ x = 0 := by
  apply WithLp.ofLp_injective 2
  funext i
  rw [restrict_ofLp_apply, show ((0 : EuclideanSpace ℝ (Fin d)).ofLp i) = (0 : ℝ) from by simp]
  split_ifs with hi
  · exact h i (Finset.mem_compl.mp hi)
  · rfl

/-- **Support split of the ℓ¹ norm** (Lu, *Big Data Analysis* (Springer, 2025), Ch8 §8.2 Compressive Sensing, Eq (8.3) workhorse):
`‖x‖₁ = ‖x|_S‖₁ + ‖x|_{Sᶜ}‖₁`. -/
theorem l1Norm_split (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    l1Norm x = l1Norm (restrict S x) + l1Norm (restrict Sᶜ x) := by
  rw [l1Norm_restrict_eq_sum, l1Norm_restrict_eq_sum]
  exact (Finset.sum_add_sum_compl S (fun i => |x.ofLp i|)).symm

/-- A vector is the sum of its restriction to `S` and to the complement `Sᶜ`. -/
theorem restrict_add_restrict_compl (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    restrict S x + restrict Sᶜ x = x := by
  apply WithLp.ofLp_injective 2
  funext i
  simp only [WithLp.ofLp_add, Pi.add_apply, restrict_ofLp_apply, Finset.mem_compl]
  split_ifs <;> simp_all

/-- **ℓ²–ℓ∞ bound on a block** (Lu, *Big Data Analysis* (Springer, 2025), Ch9 Restricted Isometry Property, the `‖x‖₂ ≤ √k‖x‖∞` step for `k`-sparse
vectors): `‖x|_S‖₂ ≤ √|S| · ‖x|_S‖∞`. -/
theorem norm_le_sqrt_card_mul_linfNorm (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    ‖restrict S x‖ ≤ Real.sqrt (S.card : ℝ) * linfNorm (restrict S x) := by
  rw [norm_eq_sqrt_sum_ofLp]
  set c := linfNorm (restrict S x) with hc
  have hcnn : 0 ≤ c := linfNorm_nonneg _
  rw [show Real.sqrt (S.card : ℝ) * c = Real.sqrt ((S.card : ℝ) * c ^ 2) by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hcnn]]
  apply Real.sqrt_le_sqrt
  rw [← Finset.sum_subset (Finset.subset_univ S)
      (fun i _ hi => by simp only [restrict_ofLp_apply, if_neg hi]; ring)]
  calc ∑ i ∈ S, ((restrict S x).ofLp i) ^ 2
      ≤ ∑ _i ∈ S, c ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := abs_le_linfNorm (restrict S x) i
        nlinarith [sq_abs ((restrict S x).ofLp i), abs_nonneg ((restrict S x).ofLp i), h1]
    _ = (S.card : ℝ) * c ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The full sum of squared coordinates of a restriction collapses to the sum over `S`. -/
private lemma sum_sq_restrict (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    ∑ i, ((restrict S x).ofLp i) ^ 2 = ∑ i ∈ S, (x.ofLp i) ^ 2 := by
  rw [← Finset.sum_subset (Finset.subset_univ S)
      (fun i _ hi => by simp only [restrict_ofLp_apply, if_neg hi]; ring)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [restrict_ofLp_apply, if_pos hi]

/-- The ℓ² norm of a restriction is monotone in the index set: `S ⊆ T ⟹
‖x|_S‖₂ ≤ ‖x|_T‖₂`. -/
theorem norm_restrict_le_of_subset {S T : Finset (Fin d)} (h : S ⊆ T)
    (x : EuclideanSpace ℝ (Fin d)) : ‖restrict S x‖ ≤ ‖restrict T x‖ := by
  rw [norm_eq_sqrt_sum_ofLp, norm_eq_sqrt_sum_ofLp, sum_sq_restrict, sum_sq_restrict]
  exact Real.sqrt_le_sqrt
    (Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => sq_nonneg _))

end StatLean.HighDimensionalStatistics
