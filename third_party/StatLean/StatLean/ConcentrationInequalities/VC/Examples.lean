module
public import StatLean.ConcentrationInequalities.VC.Defs

@[expose] public section

/-!
# Worked VC dimension computations: intervals and a three-point class

Two exact VC dimension computations:
$$ \mathrm{vc}\bigl(\{[a,b] : a \le b\}\bigr) = 2
   \qquad\text{on } \Omega = \mathbb{R}, $$
and, on the three-point set $\Omega = \{0,1,2\}$, the four-member class
encoded by the Boolean strings $\{001, 010, 100, 111\}$ also has VC
dimension $2$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.1, Example 8.3.2 (intervals) and
Example 8.3.4 (the three-point class).

**Proof formalization notes.** Lower bounds are explicit shattering
witnesses, fully precomputed: for intervals shatter `{0, 1}` with the four
intervals `[2,3]` (∅), `[0,0]`, `[1,1]`, `[0,1]`; for the three-point class
shatter `{0, 2}` (the strings `001/100/111` and `010` realize all four
labelings). Upper bounds are case analyses: for intervals, any three-point
set ordered `a < b < c` cannot realize the `101` labeling (an interval
containing `a` and `c` contains the middle point `b`) — extraction via
`Finset.card_eq_three`; for the three-point class, the only 3-set `{0,1,2}`
is not shattered (`{0,1}` is not a trace). `decide` is unavailable for
`Set`-membership propositions, so the case analyses are by hand. Constants:
exact equalities, no slack. Named-sorry fallback of this work item:
`vcDim_intervalClass` (the harder computation; `vcDim_threePointClass` on
`Fin 3` must close).

**Bibliographic comments.** Both examples are standard warm-up computations
for the VC dimension; the interval class goes back to the original
Vapnik–Chervonenkis paper (*Theory Probab. Appl.* 16 (1971), 264–280) as the
canonical example of a class with a two-point cap on shattering.
-/

namespace StatLean.ConcentrationInequalities

/-- The class of closed bounded intervals `[a, b]`, `a ≤ b`, on ℝ
(HDP §8.3.1, Example 8.3.2). Edge behavior: singletons `[a, a]` are members;
the empty set is *not* a member (the `a ≤ b` convention), so realizing the
empty labeling uses an interval disjoint from the given points. -/
def intervalClass : Set (Set ℝ) := {S | ∃ a b : ℝ, a ≤ b ∧ S = Set.Icc a b}

/-- The pair `{0, 1}` is shattered by intervals (HDP §8.3.1, Example 8.3.2,
lower bound; four explicit interval witnesses). -/
theorem shatters_intervalClass_pair :
    Shatters intervalClass ({0, 1} : Finset ℝ) := by
  classical
  intro T hT
  -- Realize each labeling by an explicit interval `[lo, hi]`.
  -- `∅ → [2,3]`, `{0} → [0,0]`, `{1} → [1,1]`, `{0,1} → [0,1]`.
  by_cases h0 : (0 : ℝ) ∈ T <;> by_cases h1 : (1 : ℝ) ∈ T
  · -- T = {0,1}, use [0,1]
    refine ⟨Set.Icc 0 1, ⟨0, 1, by norm_num, rfl⟩, ?_⟩
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_inter_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Icc, Finset.mem_coe]
    constructor
    · rintro ⟨hx | hx, _⟩ <;> subst hx <;> [exact h0; exact h1]
    · intro hx
      have : x ∈ T := hx
      have hxΛ : x = 0 ∨ x = 1 := by
        rcases Finset.mem_insert.mp (hT this) with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_singleton.mp h)
      refine ⟨hxΛ, ?_⟩
      rcases hxΛ with h | h <;> subst h <;> norm_num
  · -- T = {0}, use [0,0]
    refine ⟨Set.Icc 0 0, ⟨0, 0, le_refl _, rfl⟩, ?_⟩
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_inter_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Icc, Finset.mem_coe]
    constructor
    · rintro ⟨hx | hx, hle, hge⟩
      · subst hx; exact h0
      · subst hx; exact absurd (le_antisymm hle hge) (by norm_num)
    · intro hx
      have hx0 : x = 0 := by
        rcases Finset.mem_insert.mp (hT hx) with h | h
        · exact h
        · exact absurd (Finset.mem_singleton.mp h ▸ hx) h1
      subst hx0; exact ⟨Or.inl rfl, le_refl _, le_refl _⟩
  · -- T = {1}, use [1,1]
    refine ⟨Set.Icc 1 1, ⟨1, 1, le_refl _, rfl⟩, ?_⟩
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_inter_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Icc, Finset.mem_coe]
    constructor
    · rintro ⟨hx | hx, hle, hge⟩
      · subst hx; exact absurd (le_antisymm hge hle) (by norm_num)
      · subst hx; exact h1
    · intro hx
      have hx1 : x = 1 := by
        rcases Finset.mem_insert.mp (hT hx) with h | h
        · exact absurd (h ▸ hx) h0
        · exact Finset.mem_singleton.mp h
      subst hx1; exact ⟨Or.inr rfl, le_refl _, le_refl _⟩
  · -- T = ∅, use [2,3]
    refine ⟨Set.Icc 2 3, ⟨2, 3, by norm_num, rfl⟩, ?_⟩
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_inter_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Icc, Finset.mem_coe]
    constructor
    · rintro ⟨hx | hx, hle, _⟩ <;> subst hx <;> norm_num at hle
    · intro hx
      exact absurd (Finset.mem_insert.mp (hT hx)) (by
        rintro (h | h)
        · exact h0 (h ▸ hx)
        · exact h1 (Finset.mem_singleton.mp h ▸ hx))

/-- No three-point subset of ℝ is shattered by intervals (HDP §8.3.1,
Example 8.3.2, upper bound: the `101` labeling of the ordered triple fails
since an interval containing the endpoints contains the middle point). -/
theorem not_shatters_intervalClass_of_card_three {Λ : Finset ℝ}
    -- LEAN-ONLY: cardinality-three extraction via `Finset.card_eq_three`;
    -- encoding of "any three points", no scope change.
    (h : Λ.card = 3) :
    ¬ Shatters intervalClass Λ := by
  classical
  intro hshat
  obtain ⟨x, y, z, hxy, hxz, hyz, hΛeq⟩ := Finset.card_eq_three.mp h
  -- Sort the three distinct reals to `p < q < r`.
  obtain ⟨p, q, r, hpq, hqr, hset⟩ :
      ∃ p q r : ℝ, p < q ∧ q < r ∧ Λ = {p, q, r} := by
    -- Choose the ordered triple by `min`/`max`; the six cases collapse.
    rcases lt_trichotomy x y with hxy' | hxy' | hxy'
    · rcases lt_trichotomy y z with hyz' | hyz' | hyz'
      · exact ⟨x, y, z, hxy', hyz', hΛeq⟩
      · exact absurd hyz' hyz
      · rcases lt_trichotomy x z with hxz' | hxz' | hxz'
        · exact ⟨x, z, y, hxz', hyz', by rw [hΛeq]; ext w; simp [Finset.mem_insert]; tauto⟩
        · exact absurd hxz' hxz
        · exact ⟨z, x, y, hxz', hxy', by rw [hΛeq]; ext w; simp [Finset.mem_insert]; tauto⟩
    · exact absurd hxy' hxy
    · rcases lt_trichotomy y z with hyz' | hyz' | hyz'
      · rcases lt_trichotomy x z with hxz' | hxz' | hxz'
        · exact ⟨y, x, z, hxy', hxz', by rw [hΛeq]; ext w; simp [Finset.mem_insert]; tauto⟩
        · exact absurd hxz' hxz
        · exact ⟨y, z, x, hyz', hxz', by rw [hΛeq]; ext w; simp [Finset.mem_insert]; tauto⟩
      · exact absurd hyz' hyz
      · exact ⟨z, y, x, hyz', hxy', by rw [hΛeq]; ext w; simp [Finset.mem_insert]; tauto⟩
  -- Take `T = {p, r}` (the "101" labeling). Any interval realizing it must
  -- contain `p` and `r`, hence the middle `q`, contradiction.
  have hpr : p < r := hpq.trans hqr
  have hTsub : ({p, r} : Finset ℝ) ⊆ Λ := by
    rw [hset]
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · rw [Finset.mem_singleton] at h; subst h
      simp
  obtain ⟨S, ⟨a, b, hab, hSeq⟩, hStr⟩ := hshat ({p, r} : Finset ℝ) hTsub
  subst hSeq
  -- `p` and `r` are in `Λ ∩ [a,b]`, so `a ≤ p` and `r ≤ b`.
  have hpmem : p ∈ (↑Λ : Set ℝ) ∩ Set.Icc a b := by
    rw [hStr]; exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
  have hrmem : r ∈ (↑Λ : Set ℝ) ∩ Set.Icc a b := by
    rw [hStr]
    exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
  have hap : a ≤ p := hpmem.2.1
  have hrb : r ≤ b := hrmem.2.2
  -- Then `q ∈ [a,b]` too and `q ∈ Λ`, so `q ∈ Λ ∩ [a,b] = {p,r}`.
  have hqmem : q ∈ (↑Λ : Set ℝ) ∩ Set.Icc a b := by
    refine ⟨Finset.mem_coe.mpr ?_, ⟨hap.trans hpq.le, hqr.le.trans hrb⟩⟩
    rw [hset]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  rw [hStr] at hqmem
  -- But `q ∉ {p, r}` since `p < q < r`.
  have : q = p ∨ q = r := by
    have := Finset.mem_coe.mp hqmem
    rcases Finset.mem_insert.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  rcases this with h | h
  · exact absurd h.symm (ne_of_lt hpq)
  · exact absurd h (ne_of_lt hqr)

/-- **Intervals have VC dimension 2** (HDP §8.3.1, Example 8.3.2). -/
theorem vcDim_intervalClass : vcDim intervalClass = 2 := by
  classical
  have hcard2 : ({0, 1} : Finset ℝ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by norm_num), Finset.card_singleton]
  apply le_antisymm
  · rw [vcDim_le_iff]
    intro Λ hΛ
    have hnat : Λ.card ≤ 2 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨Λ', hsub, hc⟩ :=
        Finset.exists_subset_card_eq (show 3 ≤ Λ.card from hcon)
      exact not_shatters_intervalClass_of_card_three hc (hΛ.mono_right hsub)
    exact_mod_cast hnat
  · have h := shatters_intervalClass_pair.card_le_vcDim
    rw [hcard2] at h
    exact_mod_cast h

/-- The four-member class on `Fin 3` encoded by the Boolean strings
`001, 010, 100, 111` (HDP §8.3.1, Example 8.3.4; string position `i` is
membership of `i`, so `001 = {2}`, `010 = {1}`, `100 = {0}`,
`111 = univ`). -/
def threePointClass : Set (Set (Fin 3)) :=
  {({2} : Set (Fin 3)), {1}, {0}, Set.univ}

/-- `{0, 2}` is shattered by the three-point class (lower bound; witnesses
`{1}` for `∅`, `{0}`, `{2}`, `univ` for `{0,2}`). -/
private theorem shatters_threePointClass_pair :
    Shatters threePointClass ({0, 2} : Finset (Fin 3)) := by
  classical
  intro T hT
  -- Membership facts for the two points of `Λ = {0, 2}`.
  by_cases h0 : (0 : Fin 3) ∈ T <;> by_cases h2 : (2 : Fin 3) ∈ T
  · -- T = {0,2}, use univ
    refine ⟨Set.univ, by simp [threePointClass], ?_⟩
    rw [Set.inter_univ]
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_coe]
    constructor
    · rintro (rfl | rfl) <;> [exact h0; exact h2]
    · intro hx
      have := hT hx
      rcases Finset.mem_insert.mp this with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
  · -- T = {0}, use {0}
    refine ⟨{0}, by simp [threePointClass], ?_⟩
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_inter_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe]
    constructor
    · rintro ⟨_, rfl⟩; exact h0
    · intro hx
      have hxΛ := hT hx
      refine ⟨?_, ?_⟩
      · rcases Finset.mem_insert.mp hxΛ with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_singleton.mp h)
      · rcases Finset.mem_insert.mp hxΛ with h | h
        · exact h
        · exact absurd (Finset.mem_singleton.mp h ▸ hx) h2
  · -- T = {2}, use {2}
    refine ⟨{2}, by simp [threePointClass], ?_⟩
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_inter_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe]
    constructor
    · rintro ⟨_, rfl⟩; exact h2
    · intro hx
      have hxΛ := hT hx
      refine ⟨?_, ?_⟩
      · rcases Finset.mem_insert.mp hxΛ with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_singleton.mp h)
      · rcases Finset.mem_insert.mp hxΛ with h | h
        · exact absurd (h ▸ hx) h0
        · exact Finset.mem_singleton.mp h
  · -- T = ∅, use {1}
    refine ⟨{1}, by simp [threePointClass], ?_⟩
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_inter_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe]
    constructor
    · rintro ⟨hxΛ, rfl⟩
      rcases hxΛ with h | h <;> exact absurd h (by decide)
    · intro hx
      exact absurd (hT hx) (by
        intro hxΛ
        rcases Finset.mem_insert.mp hxΛ with h | h
        · exact h0 (h ▸ hx)
        · exact h2 (Finset.mem_singleton.mp h ▸ hx))

/-- The full set `{0,1,2} = univ` is not shattered by the three-point class
(upper bound; the labeling `{0,2}` is not a trace: no member `S` satisfies
`univ ∩ S = {0,2}`). -/
private theorem not_shatters_threePointClass_univ :
    ¬ Shatters threePointClass (Finset.univ : Finset (Fin 3)) := by
  classical
  intro hshat
  -- Target labeling `{0, 2}`.
  have hsub : ({0, 2} : Finset (Fin 3)) ⊆ Finset.univ := Finset.subset_univ _
  obtain ⟨S, hSmem, hSeq⟩ := hshat ({0, 2} : Finset (Fin 3)) hsub
  rw [Finset.coe_univ, Set.univ_inter] at hSeq
  -- `S = {0,2}` as sets, but no member of the class equals `{0,2}`.
  simp only [threePointClass, Set.mem_insert_iff, Set.mem_singleton_iff] at hSmem
  have hcoe : (↑({0, 2} : Finset (Fin 3)) : Set (Fin 3)) = ({0, 2} : Set (Fin 3)) := by
    simp
  rw [hcoe] at hSeq
  -- Evaluate membership of `1` and `0` in `S` under each case.
  rcases hSmem with rfl | rfl | rfl | rfl
  · -- S = {2}: 0 ∈ {0,2} but 0 ∉ {2}
    have : (0 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := Or.inl rfl
    rw [← hSeq] at this
    simp only [Set.mem_singleton_iff] at this
    exact absurd this (by decide)
  · -- S = {1}: 0 ∈ {0,2} but 0 ∉ {1}
    have : (0 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := Or.inl rfl
    rw [← hSeq] at this
    simp only [Set.mem_singleton_iff] at this
    exact absurd this (by decide)
  · -- S = {0}: 2 ∈ {0,2} but 2 ∉ {0}
    have : (2 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := Or.inr rfl
    rw [← hSeq] at this
    simp only [Set.mem_singleton_iff] at this
    exact absurd this (by decide)
  · -- S = univ: 1 ∈ univ but 1 ∉ {0,2}
    have : (1 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := by
      rw [← hSeq]; exact Set.mem_univ _
    rcases this with h | h <;> exact absurd h (by decide)

/-- **The three-point class has VC dimension 2** (HDP §8.3.1, Example 8.3.4:
`{0, 2}` is shattered — witnesses `010`/`001`/`100`/`111` — while the only
three-point set `{0, 1, 2}` is not, e.g. the labeling `{0, 2}` itself is not
a trace). -/
theorem vcDim_threePointClass : vcDim threePointClass = 2 := by
  classical
  have hcard2 : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  apply le_antisymm
  · rw [vcDim_le_iff]
    intro Λ hΛ
    have hnat : Λ.card ≤ 2 := by
      by_contra hcon
      push_neg at hcon
      -- In `Fin 3` a set of card ≥ 3 is all of `univ`.
      have h3 : Λ.card = 3 := by
        have hle : Λ.card ≤ 3 := by
          have := Finset.card_le_univ Λ
          simpa using this
        omega
      have hΛuniv : Λ = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [h3]; decide
      rw [hΛuniv] at hΛ
      exact not_shatters_threePointClass_univ hΛ
    exact_mod_cast hnat
  · have h := shatters_threePointClass_pair.card_le_vcDim
    rw [hcard2] at h
    exact_mod_cast h

end StatLean.ConcentrationInequalities
