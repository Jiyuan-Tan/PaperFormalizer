module
public import StatLean.MultipleTesting.ForMathlib.OrderStatistics
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.Fintype.Perm

@[expose] public section

/-!
# Order statistics under affine maps and coordinate replacement — `ForMathlib` layer

Theorem-agnostic bricks about the order statistics `orderStat v i = v (Tuple.sort v i)`
(reused from `StatLean.MultipleTesting.ForMathlib.OrderStatistics`): counting
characterizations, behaviour under affine transformations of the data, and the
*replacement-perturbation* bound — changing at most `m` coordinates of a tuple moves each
order statistic by at most `m` index positions. The perturbation bound is the combinatorial
engine behind the finite-sample breakdown analysis of the median and the trimmed mean
(`MMY §3.2.5`), but the statements here are pure finite combinatorics on real tuples, with
no statistical content.

* `sum_orderStat` — order statistics are a permutation of the data, so sums agree.
* `orderStat_nonneg`, `orderStat_mem_range` — pointwise range facts.
* `card_le_orderStat_le`, `card_orderStat_le` — counting characterizations: at least `i + 1`
  entries are `≤ v₍ᵢ₎` and at least `n - i` entries are `≥ v₍ᵢ₎`.
* `le_orderStat_of_card_le`, `orderStat_le_of_card_le` — converse counting bounds.
* `orderStat_add_const`, `orderStat_const_mul_of_nonneg`, `orderStat_neg` — equivariance of
  order statistics under monotone affine maps (with index reversal `Fin.rev` for negation).
* `orderStat_le_of_hammingDist` — the replacement-perturbation bound.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) The perturbation
bound is implicit in the finite-sample breakdown computations of `MMY §3.2.5`.

**Bibliographic comments.** Order statistics are classical — H. A. David and H. N. Nagaraja,
*Order Statistics*, 3rd ed., Wiley, 2003 — but the perturbation bounds under coordinate
replacement collected here are the combinatorial engine of finite-sample breakdown analysis,
implicit throughout D. L. Donoho and P. J. Huber, "The notion of breakdown point," in *A
Festschrift for Erich L. Lehmann*, Wadsworth, 1983, pp. 157–184.
-/

open Finset

namespace StatLean.RobustStatistics

open StatLean.MultipleTesting

variable {n : ℕ} (v : Fin n → ℝ)

/-! ### Order statistics as a rearrangement -/

/-- The order statistics are a permutation of the data: sums agree. -/
theorem sum_orderStat : ∑ i, orderStat v i = ∑ i, v i :=
  Equiv.sum_comp (Tuple.sort v) v

/-- Order statistics of a nonnegative tuple are nonnegative. -/
theorem orderStat_nonneg (hv : ∀ i, 0 ≤ v i) (i : Fin n) : 0 ≤ orderStat v i :=
  hv (Tuple.sort v i)

/-- Every order statistic is one of the data values. -/
theorem orderStat_mem_range (i : Fin n) : orderStat v i ∈ Set.range v :=
  ⟨Tuple.sort v i, rfl⟩

/-! ### Counting characterizations

All four counting statements are instances of Mathlib's
`Fin.lt_card_filter_univ_iff_apply_of_imp` (packaged as
`Tuple.lt_card_le_iff_apply_le_of_monotone` / `Tuple.lt_card_ge_iff_apply_ge_of_antitone`)
applied to the *sorted* tuple `orderStat v = v ∘ Tuple.sort v`, together with the
observation that filtering along a permutation does not change cardinalities. The `≥`
statements use the reversed tuple `j ↦ v₍ⱼ.ᵣₑᵥ₎`, which is antitone. -/

/-- Filtering along a permutation of the index type does not change cardinalities. -/
private theorem card_filter_comp_perm (σ : Equiv.Perm (Fin n)) (p : Fin n → Prop)
    [DecidablePred p] :
    (univ.filter fun i => p (σ i)).card = (univ.filter fun i => p i).card := by
  refine Finset.card_bij (fun a _ => σ a) ?_ ?_ ?_
  · intro a ha
    rw [mem_filter] at ha ⊢
    exact ⟨mem_univ _, ha.2⟩
  · intro a _ b _ hab
    exact σ.injective hab
  · intro b hb
    rw [mem_filter] at hb
    refine ⟨σ.symm b, ?_, σ.apply_symm_apply b⟩
    rw [mem_filter, σ.apply_symm_apply]
    exact ⟨mem_univ _, hb.2⟩

/-- Counting `≤ t` among the order statistics is counting `≤ t` among the data. -/
private theorem card_filter_le_const (w : Fin n → ℝ) (t : ℝ) :
    (univ.filter fun j => orderStat w j ≤ t).card = (univ.filter fun j => w j ≤ t).card := by
  unfold orderStat
  exact card_filter_comp_perm (Tuple.sort w) (fun j => w j ≤ t)

/-- Counting `≥ t` among the order statistics is counting `≥ t` among the data. -/
private theorem card_filter_const_le (w : Fin n → ℝ) (t : ℝ) :
    (univ.filter fun j => t ≤ orderStat w j).card = (univ.filter fun j => t ≤ w j).card := by
  unfold orderStat
  exact card_filter_comp_perm (Tuple.sort w) (fun j => t ≤ w j)

/-- Reversing the index does not change the count. -/
private theorem card_filter_rev (w : Fin n → ℝ) (t : ℝ) :
    (univ.filter fun j : Fin n => t ≤ orderStat w j.rev).card
      = (univ.filter fun j : Fin n => t ≤ orderStat w j).card :=
  card_filter_comp_perm Fin.revPerm (fun j : Fin n => t ≤ orderStat w j)

/-- The reversed order statistics are antitone. -/
private theorem antitone_orderStat_rev (w : Fin n → ℝ) :
    Antitone (fun j : Fin n => orderStat w j.rev) := fun _ _ hab =>
  orderStat_monotone w (Fin.rev_strictAnti.antitone hab)

/-- At least `i + 1` data values are `≤` the `i`-th order statistic. -/
theorem card_le_orderStat_le (i : Fin n) :
    (i : ℕ) + 1 ≤ (univ.filter fun j => v j ≤ orderStat v i).card := by
  have h := (Tuple.lt_card_le_iff_apply_le_of_monotone (f := orderStat v) (j := i)
    (a := orderStat v i) (orderStat_monotone v)).2 le_rfl
  rw [card_filter_le_const] at h
  omega

/-- At least `n - i` data values are `≥` the `i`-th order statistic. -/
theorem card_orderStat_le (i : Fin n) :
    n - (i : ℕ) ≤ (univ.filter fun j => orderStat v i ≤ v j).card := by
  have h := (Tuple.lt_card_ge_iff_apply_ge_of_antitone
    (f := fun j : Fin n => orderStat v j.rev) (j := i.rev) (a := orderStat v i)
    (antitone_orderStat_rev v)).2 (by simp)
  rw [card_filter_rev, card_filter_const_le] at h
  have hrev : ((i.rev : Fin n) : ℕ) = n - ((i : ℕ) + 1) := Fin.val_rev i
  have hi := i.isLt
  omega

/-- Converse counting bound: if at least `i + 1` data values are `≤ t`, then the `i`-th
order statistic is `≤ t`. -/
theorem orderStat_le_of_card_le (i : Fin n) (t : ℝ)
    (h : (i : ℕ) + 1 ≤ (univ.filter fun j => v j ≤ t).card) :
    orderStat v i ≤ t := by
  refine (Tuple.lt_card_le_iff_apply_le_of_monotone (f := orderStat v) (j := i) (a := t)
    (orderStat_monotone v)).1 ?_
  rw [card_filter_le_const]
  omega

/-- Converse counting bound: if at least `n - i` data values are `≥ t`, then the `i`-th
order statistic is `≥ t`. -/
theorem le_orderStat_of_card_le (i : Fin n) (t : ℝ)
    (h : n - (i : ℕ) ≤ (univ.filter fun j => t ≤ v j).card) :
    t ≤ orderStat v i := by
  have hrev : ((i.rev : Fin n) : ℕ) = n - ((i : ℕ) + 1) := Fin.val_rev i
  have hi := i.isLt
  have h2 : ((i.rev : Fin n) : ℕ) < (univ.filter fun j : Fin n => t ≤ orderStat v j.rev).card := by
    rw [card_filter_rev, card_filter_const_le]
    omega
  have h3 := (Tuple.lt_card_ge_iff_apply_ge_of_antitone
    (f := fun j : Fin n => orderStat v j.rev) (j := i.rev) (a := t)
    (antitone_orderStat_rev v)).1 h2
  simpa using h3

/-! ### Equivariance under monotone affine maps -/

/-- Order statistics commute with any monotone map: `(g ∘ v)₍ᵢ₎ = g (v₍ᵢ₎)`. The proof is
uniqueness of the monotone rearrangement (`Tuple.unique_monotone`): both `Tuple.sort (g ∘ v)`
and `Tuple.sort v` sort `g ∘ v`. -/
private theorem orderStat_comp_monotone {g : ℝ → ℝ} (hg : Monotone g) (i : Fin n) :
    orderStat (fun j => g (v j)) i = g (orderStat v i) := by
  have hmono : Monotone ((fun j => g (v j)) ∘ Tuple.sort v) := fun _ _ hab =>
    hg (Tuple.monotone_sort v hab)
  exact congrFun (Tuple.unique_monotone (f := fun j => g (v j))
    (σ := Tuple.sort fun j => g (v j)) (τ := Tuple.sort v) (Tuple.monotone_sort _) hmono) i

/-- Order statistics commute with adding a constant. -/
theorem orderStat_add_const (a : ℝ) (i : Fin n) :
    orderStat (fun j => v j + a) i = orderStat v i + a :=
  orderStat_comp_monotone v (g := fun t => t + a) (fun _ _ hpq => by linarith) i

/-- Order statistics commute with multiplication by a nonnegative constant. -/
theorem orderStat_const_mul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (i : Fin n) :
    orderStat (fun j => c * v j) i = c * orderStat v i :=
  orderStat_comp_monotone v (g := fun t => c * t)
    (fun _ _ hpq => mul_le_mul_of_nonneg_left hpq hc) i

/-- Negation reverses order statistics: the `i`-th smallest of `-v` is minus the `i`-th
largest of `v`. -/
theorem orderStat_neg (i : Fin n) :
    orderStat (fun j => -v j) i = -orderStat v i.rev := by
  have hmono : Monotone ((fun j => -v j) ∘ (Fin.revPerm.trans (Tuple.sort v))) := by
    intro a b hab
    exact neg_le_neg (orderStat_monotone v (Fin.rev_strictAnti.antitone hab))
  exact congrFun (Tuple.unique_monotone (f := fun j => -v j)
    (σ := Tuple.sort fun j => -v j) (τ := Fin.revPerm.trans (Tuple.sort v))
    (Tuple.monotone_sort _) hmono) i

/-! ### The replacement-perturbation bound

Changing at most `m` coordinates moves each order statistic by at most `m` index
positions. This single inequality (applied twice, via `hammingDist_comm`) yields both the
resistance of the median to `⌊(n-1)/2⌋` replacements and the resistance of the `m`-trimmed
mean to `m` replacements. -/

/-- **Replacement-perturbation bound.** If `x` and `y` differ in at most `m` coordinates
and `j + m ≤ i`, then the `j`-th order statistic of `x` is `≤` the `i`-th order statistic
of `y`. -/
theorem orderStat_le_of_hammingDist {x y : Fin n → ℝ} {m : ℕ}
    (h : hammingDist x y ≤ m) {i j : Fin n} (hij : (j : ℕ) + m ≤ i) :
    orderStat x j ≤ orderStat y i := by
  -- `A`: the (at least `i + 1`) coordinates of `y` below `y₍ᵢ₎`; `D`: the (at most `m`)
  -- coordinates where `x` and `y` differ.  On `A \ D` (at least `i + 1 - m ≥ j + 1`
  -- coordinates) we have `x k = y k ≤ y₍ᵢ₎`, so the converse counting bound applies.
  have hAcard : (i : ℕ) + 1 ≤ (univ.filter fun k => y k ≤ orderStat y i).card :=
    card_le_orderStat_le y i
  have hDcard : (univ.filter fun k => x k ≠ y k).card ≤ m := h
  have hsub : (univ.filter fun k => y k ≤ orderStat y i) \ (univ.filter fun k => x k ≠ y k)
      ⊆ univ.filter fun k => x k ≤ orderStat y i := by
    intro k hk
    rw [mem_sdiff, mem_filter, mem_filter] at hk
    have hxy : x k = y k := by
      by_contra hne
      exact hk.2 ⟨mem_univ k, hne⟩
    rw [mem_filter]
    exact ⟨mem_univ k, hxy ▸ hk.1.2⟩
  have hle := Finset.le_card_sdiff (univ.filter fun k => x k ≠ y k)
    (univ.filter fun k => y k ≤ orderStat y i)
  have hcard := Finset.card_le_card hsub
  refine orderStat_le_of_card_le x j (orderStat y i) ?_
  omega

end StatLean.RobustStatistics
