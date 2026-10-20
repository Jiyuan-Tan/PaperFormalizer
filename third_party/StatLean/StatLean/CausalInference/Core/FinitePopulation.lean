module
public import StatLean.CausalInference.Core.FiniteDefs

@[expose] public section

/-!
# The finite-population causal estimand and the fundamental problem

Elementary consequences of the definitions in `Core.FiniteDefs`: how the observed outcome
relates to the potential outcomes, the two forms of the finite-population average causal
effect, what the sharp null buys, and the **fundamental problem of causal inference** —
the observed data under a fixed assignment does not determine the average causal effect.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §2.2–2.3: the individual effect
`τᵢ = Yᵢ(1) - Yᵢ(0)`, the average causal effect `τ = n⁻¹∑τᵢ`, the observed outcome
equation (2.2), and §2.3's discussion of the missing potential outcome; §3.2 for the
sharp null. (`Ding §2.2–2.3; §3.2`.)

**Proof formalization notes.** The non-identification statement is the design-based form
of the fundamental problem: it fixes an assignment `z` under which some unit is *not*
treated and produces two science tables agreeing on every observed entry but with
different average causal effects. The two tables differ only in potential outcomes that
`z` never reveals, which is exactly the textbook argument.

**Bibliographic comments.** "The fundamental problem of causal inference" is
P. W. Holland's phrase, "Statistics and causal inference," *J. Amer. Statist. Assoc.*
**81** (1986), 945–960.
-/

namespace StatLean.CausalInference

variable {n : ℕ}

/-! ### LEAN-ONLY big-operator helpers

`Core.FiniteDefs` imports only a small part of Mathlib's big-operator library, so the two
standard facts below (distributing a scalar over a finite sum, and positivity of a sum of
nonnegative terms with one positive term) are re-proved here by induction on the index set
rather than imported. They carry no mathematical content. -/

private lemma mul_sum_aux {ι : Type*} (c : ℝ) (s : Finset ι) (f : ι → ℝ) :
    c * ∑ i ∈ s, f i = ∑ i ∈ s, c * f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mul_add, ih]

private lemma sum_nonneg_aux {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∀ i ∈ s, 0 ≤ f i) → 0 ≤ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => intro _; simp
  | insert a s ha ih =>
      intro h
      rw [Finset.sum_insert ha]
      exact add_nonneg (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma sum_pos_aux {ι : Type*} {s : Finset ι} {f : ι → ℝ} {a : ι}
    (ha : a ∈ s) (hnn : ∀ i ∈ s, 0 ≤ f i) (hpos : 0 < f a) : 0 < ∑ i ∈ s, f i := by
  classical
  rw [← Finset.sum_erase_add s f ha]
  exact add_pos_of_nonneg_of_pos
    (sum_nonneg_aux (s.erase a) f fun i hi => hnn i (Finset.mem_of_mem_erase hi)) hpos

/-- The observed outcome of a treated unit is its treated potential outcome
(Ding eq. (2.2)). -/
theorem observed_eq_y1 (S : ScienceTable n) {z : Assignment n} {i : Fin n} (hi : z i = true) :
    S.observed z i = S.y1 i := by
  simp [ScienceTable.observed, hi]

/-- The observed outcome of a control unit is its control potential outcome
(Ding eq. (2.2)). -/
theorem observed_eq_y0 (S : ScienceTable n) {z : Assignment n} {i : Fin n} (hi : z i = false) :
    S.observed z i = S.y0 i := by
  simp [ScienceTable.observed, hi]

/-- The observed outcome equation in arithmetic form: `Yᵢ = ZᵢYᵢ(1) + (1 - Zᵢ)Yᵢ(0)`
(Ding eq. (2.2)). -/
theorem observed_eq_ind_combination (S : ScienceTable n) (z : Assignment n) (i : Fin n) :
    S.observed z i = ind (z i) * S.y1 i + (1 - ind (z i)) * S.y0 i := by
  cases hzi : z i <;> simp [ScienceTable.observed, ind, hzi]

/-- The average causal effect is the difference of the two potential-outcome means
(Ding §2.2). -/
theorem finiteATE_eq_sub_popMean (S : ScienceTable n) :
    S.finiteATE = popMean S.y1 - popMean S.y0 := by
  simp only [ScienceTable.finiteATE, popMean, ScienceTable.unitEffect,
    Finset.sum_sub_distrib, mul_sub]

/-- Under the sharp null every observed outcome vector equals the control vector, so all
missing potential outcomes are imputable (Ding §3.2). -/
theorem SharpNull.observed_eq (S : ScienceTable n) (h : S.SharpNull) (z : Assignment n) :
    S.observed z = S.y0 := by
  funext i
  cases hzi : z i <;> simp [ScienceTable.observed, hzi, h i]

/-- The sharp null implies the null average causal effect (the converse fails). -/
theorem SharpNull.finiteATE_eq_zero (S : ScienceTable n) (h : S.SharpNull) :
    S.finiteATE = 0 := by
  have hz : ∀ i, S.unitEffect i = 0 := fun i => sub_eq_zero_of_eq (h i)
  simp [ScienceTable.finiteATE, popMean, hz]

/-- The **average causal effect over a subgroup** of units. Junk value `0` on the empty
subgroup. -/
noncomputable def subgroupATE (S : ScienceTable n) (A : Finset (Fin n)) : ℝ :=
  (A.card : ℝ)⁻¹ * ∑ i ∈ A, S.unitEffect i

/-- **Subgroup decomposition** (Ding §2.2): the average causal effect is the
size-weighted average of the subgroup effects, for any partition of the units into the
level sets of a map `g`. Empty subgroups contribute `0`. -/
theorem finiteATE_eq_sum_subgroupATE (S : ScienceTable n) {K : Type*} [Fintype K]
    [DecidableEq K] (g : Fin n → K)
    -- LEAN-ONLY: a nonempty population, so that `n⁻¹` is not a junk value; no scope change
    (hn : 0 < n) :
    S.finiteATE
      = ∑ k : K, (((Finset.univ.filter fun i => g i = k).card : ℝ) / (n : ℝ))
          * subgroupATE S (Finset.univ.filter fun i => g i = k) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- each subgroup term is `n⁻¹` times the subgroup total; the empty subgroup contributes `0`
  -- on both sides, which is where `subgroupATE`'s junk value is absorbed
  have key : ∀ k : K,
      (((Finset.univ.filter fun i => g i = k).card : ℝ) / (n : ℝ))
          * subgroupATE S (Finset.univ.filter fun i => g i = k)
        = (n : ℝ)⁻¹ * ∑ i ∈ Finset.univ.filter fun i => g i = k, S.unitEffect i := by
    intro k
    rcases Finset.eq_empty_or_nonempty (Finset.univ.filter fun i => g i = k) with hk | hk
    · rw [hk]
      simp [subgroupATE]
    · have hc : ((Finset.univ.filter fun i => g i = k).card : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hk).ne'
      rw [subgroupATE, div_mul_eq_mul_div, ← mul_assoc, mul_inv_cancel₀ hc, one_mul,
        div_eq_inv_mul]
  rw [Finset.sum_congr rfl fun k _ => key k, ← mul_sum_aux,
    ScienceTable.finiteATE, popMean]
  exact congrArg _ (Finset.sum_fiberwise Finset.univ g S.unitEffect).symm

/-- **The fundamental problem of causal inference** (Ding §2.3), design-based form: fix an
assignment under which some unit is untreated; then two science tables can agree on every
*observed* outcome yet have different average causal effects. Hence the observed data
alone never identifies `τ`. -/
theorem exists_sameObserved_ne_finiteATE (z : Assignment n)
    -- USER-INPUT: some unit is not treated, so some potential outcome is missing; Ding §2.3
    {i₀ : Fin n} (hi₀ : z i₀ = false) :
    ∃ S S' : ScienceTable n, S.observed z = S'.observed z ∧ S.finiteATE ≠ S'.finiteATE := by
  -- both tables have `Y(0) ≡ 0`; they differ only in the treated potential outcomes of the
  -- units that `z` leaves untreated, which `z` never reveals
  refine ⟨⟨fun _ => 0, fun _ => 0⟩, ⟨fun i => if z i then 0 else 1, fun _ => 0⟩, ?_, ?_⟩
  · funext i
    cases hzi : z i <;> simp [ScienceTable.observed, hzi]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) i₀.isLt
    have hval : ∀ i : Fin n,
        ScienceTable.unitEffect (n := n) ⟨fun i => if z i then 0 else 1, fun _ => 0⟩ i
          = if z i then (0 : ℝ) else 1 := by
      intro i
      cases hzi : z i <;> simp [ScienceTable.unitEffect, hzi]
    have hzero : ScienceTable.finiteATE (n := n) ⟨fun _ => 0, fun _ => 0⟩ = 0 := by
      simp [ScienceTable.finiteATE, popMean, ScienceTable.unitEffect]
    have hpos : (0 : ℝ) < ScienceTable.finiteATE (n := n)
        ⟨fun i => if z i then 0 else 1, fun _ => 0⟩ := by
      rw [ScienceTable.finiteATE, popMean]
      refine mul_pos (inv_pos.mpr hnpos) (sum_pos_aux (Finset.mem_univ i₀) (fun i _ => ?_) ?_)
      · rw [hval i]
        cases z i <;> norm_num
      · rw [hval i₀, hi₀]
        norm_num
    rw [hzero]
    exact ne_of_lt hpos

end StatLean.CausalInference
