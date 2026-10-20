module
public import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Prod.Lex

@[expose] public section

/-!
# Top-`k` coordinate blocks ("shelling")

The greedy decreasing-magnitude partition of the complement `Sᶜ` used in the RIP
recovery proof (Lu, *Big Data Analysis* Chapter 9, Restricted Isometry Property,
§9.1, Theorem 9.1 (Perfect Recovery Under RIP)): block `0` holds the `k`
largest-`|·|` coordinates of `x` outside `S`, block `1` the next `k`, and so on.

Mathlib has no packaged "top-`k` coordinates" selector; this file builds it from
`Finset.sort` on the values and exposes the interface the recovery proof needs:
the blocks are disjoint, each has `≤ k` coordinates, together they cover `Sᶜ`, and
the **monotone-averaging** estimate `‖x|_{B_{j+1}}‖∞ ≤ (1/k)‖x|_{B_j}‖₁` holds.

Theorem-agnostic (`ForMathlib`); depends only on `restrict`/`l1Norm`/`linfNorm`
from `VecNorms.lean`.

## Construction

The coordinates of `Sᶜ` are listed in `sortedCompl` by *decreasing* `|xᵢ|`, ties
broken by index, using `Finset.sort` for the lexicographic key `(-|xᵢ|, i)`. Block
`j` is the `j`-th consecutive window of `k` entries of that list. All interface
lemmas are derived from index arithmetic on this sorted, duplicate-free list.
-/

namespace StatLean.HighDimensionalStatistics

open Finset

variable {d : ℕ}

/-- Lexicographic sorting key `(-|xᵢ|, i)` for ordering coordinates by *decreasing*
magnitude (smaller key = larger `|xᵢ|`), with ties broken by the index `i`.
Lands in `ℝ ×ₗ ℕ` so that the ambient lexicographic `LinearOrder` supplies totality,
transitivity and antisymmetry for `Finset.sort`. -/
noncomputable def magKey (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : ℝ ×ₗ ℕ :=
  toLex (-|x.ofLp i|, (i : ℕ))

/-- The decreasing-magnitude order on coordinates: `magRel x a b` iff `a`'s key
precedes `b`'s, i.e. `a` is (weakly) larger in magnitude, ties by smaller index. -/
noncomputable def magRel (x : EuclideanSpace ℝ (Fin d)) (a b : Fin d) : Prop :=
  magKey x a ≤ magKey x b

noncomputable instance instDecidableMagRel (x : EuclideanSpace ℝ (Fin d)) :
    DecidableRel (magRel x) := fun _ _ => Classical.dec _

instance instTransMagRel (x : EuclideanSpace ℝ (Fin d)) : IsTrans (Fin d) (magRel x) where
  trans _ _ _ hab hbc := le_trans hab hbc

instance instAntisymmMagRel (x : EuclideanSpace ℝ (Fin d)) : Std.Antisymm (magRel x) where
  antisymm a b hab hba := by
    have heq : magKey x a = magKey x b := le_antisymm hab hba
    have h2 : (a : ℕ) = (b : ℕ) := by
      have := congrArg (fun p => (ofLex p).2) heq
      simpa [magKey] using this
    exact Fin.val_injective h2

instance instTotalMagRel (x : EuclideanSpace ℝ (Fin d)) : Std.Total (magRel x) where
  total a b := le_total (magKey x a) (magKey x b)

/-- `magRel` compares magnitudes: if `a` precedes `b` then `|x b| ≤ |x a|`. -/
lemma magRel_abs_le (x : EuclideanSpace ℝ (Fin d)) {a b : Fin d} (h : magRel x a b) :
    |x.ofLp b| ≤ |x.ofLp a| := by
  unfold magRel magKey at h
  rw [Prod.Lex.le_iff'] at h
  have h1 : -|x.ofLp a| ≤ -|x.ofLp b| := h.1
  linarith

/-- `Sᶜ` listed in decreasing order of `|x·|` (ties by index). -/
noncomputable def sortedCompl (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    List (Fin d) :=
  Sᶜ.sort (magRel x)

lemma mem_sortedCompl {S : Finset (Fin d)} {x : EuclideanSpace ℝ (Fin d)} {i : Fin d} :
    i ∈ sortedCompl S x ↔ i ∈ Sᶜ := by
  unfold sortedCompl; exact Finset.mem_sort _

lemma sortedCompl_nodup (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    (sortedCompl S x).Nodup := by
  unfold sortedCompl; exact Finset.sort_nodup _ _

lemma length_sortedCompl (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    (sortedCompl S x).length = Sᶜ.card := by
  unfold sortedCompl; exact Finset.length_sort _

lemma sortedCompl_pairwise (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    (sortedCompl S x).Pairwise (magRel x) := by
  unfold sortedCompl; exact Finset.pairwise_sort _ _

/-- Earlier entries of the sorted list have (weakly) larger magnitude. -/
lemma sortedCompl_abs_le {S : Finset (Fin d)} {x : EuclideanSpace ℝ (Fin d)} {p q : ℕ}
    (hp : p < (sortedCompl S x).length) (hq : q < (sortedCompl S x).length) (hpq : p < q) :
    |x.ofLp ((sortedCompl S x)[q])| ≤ |x.ofLp ((sortedCompl S x)[p])| := by
  have hrel : magRel x ((sortedCompl S x)[p]) ((sortedCompl S x)[q]) :=
    (List.pairwise_iff_getElem.mp (sortedCompl_pairwise S x)) p q hp hq hpq
  exact magRel_abs_le x hrel

/-- Greedy partition of `Sᶜ` into consecutive blocks of at most `k` coordinates,
ordered by decreasing `|x·|`. Block `j` is the `j`-th window of `k` coordinates in
the magnitude-sorted listing `sortedCompl S x`. -/
noncomputable def orderedBlocks (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    (k : ℕ) : ℕ → Finset (Fin d) :=
  fun j => (((sortedCompl S x).drop (j * k)).take k).toFinset

/-- Membership in block `j` exposes the precise index range `[j·k, j·k + k)` of the
sorted list occupied by that block. -/
lemma orderedBlocks_index_range {S : Finset (Fin d)} {x : EuclideanSpace ℝ (Fin d)}
    {k j : ℕ} {i : Fin d} (hi : i ∈ orderedBlocks S x k j) :
    ∃ p, ∃ (_ : p < (sortedCompl S x).length),
      j * k ≤ p ∧ p < j * k + k ∧ (sortedCompl S x)[p] = i := by
  simp only [orderedBlocks, List.mem_toFinset] at hi
  obtain ⟨r, hr, hri⟩ := List.mem_iff_getElem.mp hi
  have hrk : r < k := by
    have h := hr; rw [List.length_take, List.length_drop] at h; omega
  have hp : j * k + r < (sortedCompl S x).length := by
    have h := hr; rw [List.length_take, List.length_drop] at h; omega
  have hval : (((sortedCompl S x).drop (j * k)).take k)[r] = (sortedCompl S x)[j * k + r] := by
    rw [List.getElem_take, List.getElem_drop]
  exact ⟨j * k + r, hp, Nat.le_add_right _ _, by omega, by rw [← hval]; exact hri⟩

/-- Conversely, every index in `[j·k, j·k + k)` (within range) lands in block `j`. -/
lemma mem_orderedBlocks_of_index {S : Finset (Fin d)} {x : EuclideanSpace ℝ (Fin d)}
    {k j p : ℕ} (hp : p < (sortedCompl S x).length) (h1 : j * k ≤ p) (h2 : p < j * k + k) :
    (sortedCompl S x)[p] ∈ orderedBlocks S x k j := by
  obtain ⟨r, rfl⟩ : ∃ r, p = j * k + r := ⟨p - j * k, by omega⟩
  have hrk : r < k := by omega
  simp only [orderedBlocks, List.mem_toFinset]
  rw [List.mem_iff_getElem]
  have hr : r < (((sortedCompl S x).drop (j * k)).take k).length := by
    rw [List.length_take, List.length_drop]; omega
  refine ⟨r, hr, ?_⟩
  rw [List.getElem_take, List.getElem_drop]

/-- Each block lies in the complement of the support set `S`. -/
theorem orderedBlocks_subset_compl (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    (k j : ℕ) : orderedBlocks S x k j ⊆ Sᶜ := by
  intro i hi
  simp only [orderedBlocks, List.mem_toFinset] at hi
  have : i ∈ sortedCompl S x := List.mem_of_mem_drop (List.mem_of_mem_take hi)
  rwa [mem_sortedCompl] at this

/-- Distinct blocks are disjoint. -/
theorem orderedBlocks_disjoint (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    (k : ℕ) {j j' : ℕ} (h : j ≠ j') :
    Disjoint (orderedBlocks S x k j) (orderedBlocks S x k j') := by
  rw [Finset.disjoint_left]
  intro i hij hij'
  obtain ⟨p, hp, hp1, hp2, hpi⟩ := orderedBlocks_index_range hij
  obtain ⟨q, hq, hq1, hq2, hqi⟩ := orderedBlocks_index_range hij'
  have hpq : p = q := by
    have hLeq : (sortedCompl S x)[p] = (sortedCompl S x)[q] := by rw [hpi, hqi]
    exact (List.Nodup.getElem_inj_iff (sortedCompl_nodup S x)).mp hLeq
  subst hpq
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have e2 : (j + 1) * k ≤ j' * k := Nat.mul_le_mul_right k (by omega)
    have e1 : (j + 1) * k = j * k + k := by ring
    omega
  · have e2 : (j' + 1) * k ≤ j * k := Nat.mul_le_mul_right k (by omega)
    have e1 : (j' + 1) * k = j' * k + k := by ring
    omega

/-- Each block has at most `k` coordinates. -/
theorem orderedBlocks_card_le (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    (k j : ℕ) : (orderedBlocks S x k j).card ≤ k := by
  simp only [orderedBlocks]
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.length_take]
  exact min_le_left _ _

/-- The blocks cover `Sᶜ`: every coordinate outside `S` lies in some block. -/
theorem mem_orderedBlocks_of_notMem (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    {k : ℕ} (hk : 0 < k) {i : Fin d} (hi : i ∉ S) :
    ∃ j, i ∈ orderedBlocks S x k j := by
  have hiC : i ∈ sortedCompl S x := mem_sortedCompl.mpr (Finset.mem_compl.mpr hi)
  obtain ⟨p, hp, hpi⟩ := List.mem_iff_getElem.mp hiC
  refine ⟨p / k, ?_⟩
  have hlow : p / k * k ≤ p := Nat.div_mul_le_self p k
  have hdm : p / k * k + p % k = p := Nat.div_add_mod' p k
  have hmod : p % k < k := Nat.mod_lt p hk
  have hmem := mem_orderedBlocks_of_index hp hlow (by omega)
  rwa [hpi] at hmem

/-- Only finitely many blocks are nonempty: once `j·k ≥ |Sᶜ|` the block is empty. -/
theorem orderedBlocks_eq_empty (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    {k j : ℕ} (hk : 0 < k) (hj : Sᶜ.card ≤ j * k) :
    orderedBlocks S x k j = ∅ := by
  simp only [orderedBlocks]
  have hnil : (sortedCompl S x).drop (j * k) = [] :=
    List.drop_eq_nil_of_le (by rw [length_sortedCompl]; exact hj)
  rw [hnil, List.take_nil, List.toFinset_nil]

/-- Magnitude domination across consecutive blocks: every coordinate of block `j+1`
is (weakly) smaller in magnitude than every coordinate of block `j`. -/
lemma orderedBlocks_abs_le {S : Finset (Fin d)} {x : EuclideanSpace ℝ (Fin d)} {k j : ℕ}
    {a b : Fin d} (ha : a ∈ orderedBlocks S x k j) (hb : b ∈ orderedBlocks S x k (j + 1)) :
    |x.ofLp b| ≤ |x.ofLp a| := by
  obtain ⟨p, hp, hp1, hp2, hpa⟩ := orderedBlocks_index_range ha
  obtain ⟨q, hq, hq1, hq2, hqb⟩ := orderedBlocks_index_range hb
  have hpq : p < q := by
    have e : (j + 1) * k = j * k + k := by ring
    omega
  have hrel := sortedCompl_abs_le hp hq hpq
  rwa [hpa, hqb] at hrel

/-- `linfNorm` is bounded by any uniform bound on coordinates (handles `d = 0`). -/
lemma linfNorm_le_of_forall {x : EuclideanSpace ℝ (Fin d)} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |x.ofLp i| ≤ c) : linfNorm x ≤ c := by
  unfold linfNorm
  by_cases hd : Nonempty (Fin d)
  · haveI := hd
    exact ciSup_le h
  · rw [not_nonempty_iff] at hd
    haveI : IsEmpty (Fin d) := hd
    have heq : (⨆ i, |x.ofLp i|) = 0 := by
      change sSup (Set.range (fun i : Fin d => |x.ofLp i|)) = 0
      rw [Set.range_eq_empty_iff.mpr ‹IsEmpty (Fin d)›, Real.sSup_empty]
    rw [heq]; exact hc

/-- **Monotone-averaging** (Lu, *Big Data Analysis* Chapter 9, §9.1, the shelling
estimate): the ℓ∞ norm of the next
block is bounded by the average ℓ¹ mass of the current block,
`‖x|_{B_{j+1}}‖∞ ≤ (1/k)·‖x|_{B_j}‖₁`. -/
theorem linfNorm_restrict_orderedBlocks_succ_le (S : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    linfNorm (restrict (orderedBlocks S x k (j + 1)) x)
      ≤ (1 / (k : ℝ)) * l1Norm (restrict (orderedBlocks S x k j) x) := by
  refine linfNorm_le_of_forall (mul_nonneg (by positivity) (l1Norm_nonneg _)) ?_
  intro i
  rw [restrict_ofLp_apply]
  split_ifs with hiB
  · -- `i ∈ B_{j+1}`: the averaging argument.
    obtain ⟨q, hq, hq1, hq2, hqi⟩ := orderedBlocks_index_range hiB
    -- `B_{j+1}` nonempty ⇒ `B_j` is a full window of `k` coordinates.
    have hn : j * k + k ≤ (sortedCompl S x).length := by
      have e : (j + 1) * k = j * k + k := by ring
      omega
    have hwnd : (((sortedCompl S x).drop (j * k)).take k).Nodup :=
      ((List.take_sublist k _).trans (List.drop_sublist (j * k) _)).nodup (sortedCompl_nodup S x)
    have hcard : (orderedBlocks S x k j).card = k := by
      simp only [orderedBlocks]
      rw [List.toFinset_card_of_nodup hwnd, List.length_take, List.length_drop]
      omega
    -- every coordinate of `B_j` dominates `|x i|`.
    have hbound : ∀ m ∈ orderedBlocks S x k j, |x.ofLp i| ≤ |x.ofLp m| :=
      fun m hm => orderedBlocks_abs_le hm hiB
    have hsum : (orderedBlocks S x k j).card • |x.ofLp i|
        ≤ ∑ m ∈ orderedBlocks S x k j, |x.ofLp m| :=
      Finset.card_nsmul_le_sum _ _ _ hbound
    rw [hcard, nsmul_eq_mul] at hsum
    rw [l1Norm_restrict_eq_sum]
    set A := |x.ofLp i| with hA
    set Stot := ∑ m ∈ orderedBlocks S x k j, |x.ofLp m| with hStot
    -- `hsum : k * A ≤ Stot`; divide by `k > 0`.
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hk'
    have hmul := mul_le_mul_of_nonneg_left hsum (le_of_lt (by positivity : (0 : ℝ) < 1 / (k : ℝ)))
    rwa [← mul_assoc, one_div_mul_cancel hk0, one_mul] at hmul
  · -- `i ∉ B_{j+1}`: the coordinate is zero.
    rw [abs_zero]
    exact mul_nonneg (by positivity) (l1Norm_nonneg _)

end StatLean.HighDimensionalStatistics
