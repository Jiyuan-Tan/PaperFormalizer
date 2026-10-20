module
public import StatLean.MultipleTesting.FDP.Defs
public import StatLean.MultipleTesting.PValues.Defs
public import StatLean.MultipleTesting.ForMathlib.OrderStatistics

@[expose] public section

/-!
# Holm step-down and Bonferroni FWER control

Suppose we test $N$ hypotheses and observe one p-value $p_j$ per hypothesis. Let $H_0$ be the
(unknown) set of true null hypotheses, with cardinality $N_0 = |H_0|$, and call each null marginal
*super-uniform* if $\mathbb{P}(p_j \le t) \le t$ for all $t \ge 0$ whenever $j \in H_0$. The
family-wise error rate is the probability of rejecting at least one true null,
$\mathrm{FWER} = \mathbb{P}(R \cap H_0 \ne \varnothing)$, where $R$ is the rejection set.

**Holm step-down procedure** (`holm_fwer_le`). Sort the p-values $p_{(1)} \le \cdots \le p_{(N)}$,
walk down comparing $p_{(i)}$ against the descending cutoffs $\alpha/(N-i+1)$, and reject the
longest initial run that stays at or below its cutoff. If every null marginal is super-uniform,
then this procedure controls the family-wise error rate at level $\alpha$:
$$ \mathrm{FWER} \le \alpha. $$
No independence assumption is required, and the bound holds for $0 < \alpha < 1$.

**Bonferroni correction** (`bonferroni_fwer_le`, Lu-BDA §19.2.2). Reject every hypothesis with
$p_j \le \alpha/N$. Under the same super-uniformity assumption this controls the family-wise error
rate by
$$ \mathrm{FWER} \le \tfrac{N_0}{N}\,\alpha \le \alpha. $$
The Lean statement records the sharper $\tfrac{N_0}{N}\,\alpha$ bound; the textbook $\alpha$ bound
follows since $N_0 \le N$.

**Note on the indexing.** The Lean definitions use 0-indexed sorted positions $i = 0,\dots,N-1$, so
the cutoff is written $\alpha/(N-i)$ rather than the 1-indexed $\alpha/(N-i+1)$; the two describe
the same procedure.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 19 (Multiple Hypotheses), §19.2 (Multiple Hypotheses),
§19.2.2 (Bonferroni Correction), for the Bonferroni correction.
Lu, *Big Data Analysis* states the plain Bonferroni correction but contains *no* Holm step-down
theorem; the Holm result is formalized from S. Holm, "A simple sequentially rejective multiple
test procedure", *Scand. J. Statist.* **6** (1979), 65–70, **Theorem 1** (see Bibliographic
comments). Hypotheses
sourced to Holm (1979) are tagged accordingly.

**Proof formalization notes.** The deterministic crux `holm_rejects_true_null_imp` shows that if
Holm rejects any true null then some true null has $p_j \le \alpha/N_0$; a finite union bound over
$H_0$ plus super-uniformity then yields $\mathrm{FWER} \le N_0 \cdot (\alpha/N_0) = \alpha$. The
Bonferroni proof is the same union-bound argument with the simpler membership condition
$p_j \le \alpha/N$, collapsing to $N_0 \cdot (\alpha/N) = (N_0/N)\,\alpha$.

`holmCount` is defined to be `0` when $\alpha \le 0$, making `holmRejects = ∅` in that regime. This
is faithful to the Holm procedure (intended for $\alpha \in (0,1)$), and ensures
`holm_rejects_true_null_imp` is vacuously true for non-positive $\alpha$ (where the conclusion
$p_j \le \alpha/N_0$ would otherwise fail to follow from the step-down inequality).

**Bibliographic comments.** The step-down procedure and its FWER guarantee are due to S. Holm, "A
simple sequentially rejective multiple test procedure", *Scandinavian Journal of Statistics* **6**
(1979), no. 2, 65–70; the level-$\alpha$ FWER control formalized here is Holm's Theorem 1. The
Bonferroni correction rests on Boole's inequality (the union bound), commonly attributed to C. E.
Bonferroni, "Teoria statistica delle classi e calcolo delle probabilità", *Pubblicazioni del R.
Istituto Superiore di Scienze Economiche e Commerciali di Firenze* **8** (1936), 3–62; its use as a
multiple-comparison correction was popularized by O. J. Dunn, "Multiple comparisons among means",
*Journal of the American Statistical Association* **56** (1961), no. 293, 52–64. The single-step
Bonferroni bound itself is essentially folklore (a direct union bound over the null events) and has
no single seminal origin beyond these references.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Number of hypotheses Holm rejects: the largest prefix length `k` of the sorted p-values such
that `p₍ᵢ₎ ≤ α/(N−i)` for every `0 ≤ i < k` (0-indexed step-down cutoffs). Defined to be 0
when `α ≤ 0` so that `holmRejects = ∅` outside the intended domain `α > 0`. -/
noncomputable def holmCount {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) : ℕ :=
  if 0 < α then
    ((Finset.range (N + 1)).filter
      (fun (k : ℕ) => ∀ i : Fin N, (i : ℕ) < k →
        orderStat (fun j => p j ω) i ≤ α / ((N : ℝ) - (i : ℝ)))).sup id
  else 0

/-- Holm rejection set: the `holmCount` smallest p-values, i.e. those whose rank (number of
strictly smaller p-values) is below the step-down length. -/
noncomputable def holmRejects {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) : Finset (Fin N) :=
  Finset.univ.filter
    (fun j => (Finset.univ.filter (fun j' => p j' ω < p j ω)).card < holmCount α p ω)

/-- Bonferroni rejection set (Lu-BDA §19.2.2): reject `{ j : pⱼ ≤ α/N }`. -/
noncomputable def bonferroniRejects {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) : Finset (Fin N) :=
  Finset.univ.filter (fun j => p j ω ≤ α / (N : ℝ))

/-! ### Private infrastructure -/

/-- `holmCount` is at most N. -/
private lemma holmCount_le_N {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) :
    holmCount α p ω ≤ N := by
  simp only [holmCount]
  split_ifs with hα
  · apply Finset.sup_le
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [id_eq]
    omega
  · exact Nat.zero_le _

/-- When `α > 0`, the Holm step-down condition holds at every sorted position strictly below
`holmCount`. This is the key property extracted from the sup construction. -/
private lemma holmCount_cond {N : ℕ} {α : ℝ} (hα : 0 < α) (p : Fin N → Ω → ℝ) (ω : Ω) :
    ∀ i : Fin N, (i : ℕ) < holmCount α p ω →
      orderStat (fun j => p j ω) i ≤ α / ((N : ℝ) - (i : ℝ)) := by
  simp only [holmCount, if_pos hα]
  set s := (Finset.range (N + 1)).filter
      (fun k : ℕ => ∀ i : Fin N, (i : ℕ) < k →
        orderStat (fun j => p j ω) i ≤ α / ((N : ℝ) - (i : ℝ))) with hs_def
  -- 0 ∈ s (the condition is vacuously true for k = 0)
  have hs_ne : s.Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩
  -- The sup of s is in s (since s is finite and nonempty)
  have hmem : s.sup id ∈ s := by
    have h := Finset.sup_mem_of_nonempty (f := id) hs_ne
    rwa [Set.image_id, Finset.mem_coe] at h
  exact (Finset.mem_filter.mp hmem).2

/-! ### Main theorems -/

/-- Deterministic crux (Holm 1979): if the Holm procedure rejects any true null, then some true
null has p-value `≤ α/N₀`, where `N₀ = |H₀|`. -/
theorem holm_rejects_true_null_imp {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (H₀ : Finset (Fin N))
    (ω : Ω) (hne : ((holmRejects α p ω) ∩ H₀).Nonempty) :
    ∃ j ∈ H₀, p j ω ≤ α / (H₀.card : ℝ) := by
  -- Step 0: derive α > 0, because for α ≤ 0 holmCount = 0 so holmRejects = ∅ and hne is false.
  have hα : 0 < α := by
    by_contra h; push_neg at h
    have hempty : holmRejects α p ω = ∅ := by
      simp only [holmRejects, holmCount, if_neg (not_lt.mpr h)]
      ext j; simp [Nat.not_lt_zero]
    rw [hempty, Finset.empty_inter] at hne
    exact Finset.not_nonempty_empty hne
  -- Step 1: pick j₀ ∈ holmRejects ∩ H₀ with minimum p-value.
  obtain ⟨j₀, hj₀mem, hj₀min⟩ := Finset.exists_min_image _ (fun j => p j ω) hne
  rw [Finset.mem_inter] at hj₀mem
  obtain ⟨hj₀holm, hj₀H₀⟩ := hj₀mem
  refine ⟨j₀, hj₀H₀, ?_⟩
  -- Abbreviation for the p-value tuple at ω.
  set v : Fin N → ℝ := fun j => p j ω
  -- Step 2: i₀ = rank of j₀ (number of hypotheses with strictly smaller p-value).
  set i₀ : ℕ := (Finset.univ.filter (fun j' : Fin N => v j' < v j₀)).card with hi₀_def
  -- Step 3: i₀ < holmCount (from j₀ ∈ holmRejects).
  have hi₀_lt_count : i₀ < holmCount α p ω := by
    simp only [holmRejects, Finset.mem_filter, Finset.mem_univ, true_and] at hj₀holm
    exact hj₀holm
  -- Step 4: i₀ < N (since holmCount ≤ N).
  have hi₀_lt_N : i₀ < N := Nat.lt_of_lt_of_le hi₀_lt_count (holmCount_le_N α p ω)
  -- Step 5: Holm cutoff condition at sorted position i₀.
  have hholm_at_i₀ : orderStat v ⟨i₀, hi₀_lt_N⟩ ≤ α / ((N : ℝ) - (i₀ : ℝ)) :=
    holmCount_cond hα p ω ⟨i₀, hi₀_lt_N⟩ hi₀_lt_count
  -- Step 6: H₀.card > 0 (j₀ ∈ H₀ witnesses nonemptiness).
  have hH₀_pos : 0 < H₀.card := Finset.Nonempty.card_pos ⟨j₀, hj₀H₀⟩
  have hH₀_cast_pos : (0 : ℝ) < (H₀.card : ℝ) := Nat.cast_pos.mpr hH₀_pos
  -- Step 7: every hypothesis with smaller p-value than j₀ is non-null.
  -- (If j' ∈ H₀ had smaller p-value, it would be in holmRejects ∩ H₀ below j₀, contradicting
  -- minimality of j₀.)
  have hsmaller_non_null : ∀ j' : Fin N, v j' < v j₀ → j' ∉ H₀ := by
    intro j' hlt hin
    -- The rank of j' is strictly less than i₀ (since {j''|v j''<v j'} ⊊ {j''|v j''<v j₀}).
    have h_ssub : Finset.univ.filter (fun j'' : Fin N => v j'' < v j') <
                  Finset.univ.filter (fun j'' : Fin N => v j'' < v j₀) := by
      apply lt_of_le_of_ne
      · intro j'' hj''
        rw [Finset.mem_filter] at hj'' ⊢
        exact ⟨Finset.mem_univ _, lt_trans hj''.2 hlt⟩
      · intro heq
        -- j' is in the second set but not the first, contradiction heq.
        have hj'_in : j' ∈ Finset.univ.filter (fun j'' : Fin N => v j'' < v j') := by
          rw [heq]; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlt⟩
        rw [Finset.mem_filter] at hj'_in
        exact absurd hj'_in.2 (lt_irrefl _)
    have hrank_lt : (Finset.univ.filter (fun j'' : Fin N => v j'' < v j')).card <
                    holmCount α p ω :=
      calc (Finset.univ.filter (fun j'' : Fin N => v j'' < v j')).card
          < (Finset.univ.filter (fun j'' : Fin N => v j'' < v j₀)).card :=
              Finset.card_lt_card h_ssub
        _ = i₀ := hi₀_def.symm
        _ < holmCount α p ω := hi₀_lt_count
    have hj'_holm : j' ∈ holmRejects α p ω := by
      simp only [holmRejects, Finset.mem_filter, Finset.mem_univ, true_and]; exact hrank_lt
    exact absurd (hj₀min j' (Finset.mem_inter.mpr ⟨hj'_holm, hin⟩)) (not_le.mpr hlt)
  -- Step 8: i₀ ≤ N − H₀.card (the i₀ smaller p-values are all non-null).
  have hcard_le_N : H₀.card ≤ N :=
    (Finset.card_le_univ H₀).trans (Fintype.card_fin N).le
  have hi₀_le : i₀ ≤ N - H₀.card := by
    have h_sub : Finset.univ.filter (fun j' : Fin N => v j' < v j₀) ⊆
                 Finset.univ.filter (fun j' : Fin N => j' ∉ H₀) := by
      intro j' hj'
      rw [Finset.mem_filter] at hj' ⊢
      exact ⟨Finset.mem_univ _, hsmaller_non_null j' hj'.2⟩
    have hcompl_card : (Finset.univ.filter (fun j' : Fin N => j' ∉ H₀)).card = N - H₀.card := by
      conv_lhs =>
        rw [show Finset.univ.filter (fun j' : Fin N => j' ∉ H₀) = H₀ᶜ from
              by ext j'; simp [Finset.mem_compl]]
      simp [Finset.card_compl, Fintype.card_fin]
    calc i₀ = (Finset.univ.filter (fun j' : Fin N => v j' < v j₀)).card := hi₀_def
        _ ≤ (Finset.univ.filter (fun j' : Fin N => j' ∉ H₀)).card := Finset.card_le_card h_sub
        _ = N - H₀.card := hcompl_card
  -- Step 9: v j₀ ≤ orderStat v ⟨i₀, hi₀_lt_N⟩.
  -- Proof by contradiction: if orderStat v i₀ < v j₀, then by the monotone-sort card lemma,
  -- i₀ < #{i | orderStat v i < v j₀} = #{j' | v j' < v j₀} = i₀, contradiction.
  have hpval_le_order : v j₀ ≤ orderStat v ⟨i₀, hi₀_lt_N⟩ := by
    by_contra hc; rw [not_le] at hc
    -- hc : orderStat v ⟨i₀, hi₀_lt_N⟩ < v j₀
    -- Apply Tuple.lt_card_lt_iff_apply_lt_of_monotone: ↑⟨i₀,_⟩ < #{i | orderStat v i < v j₀}
    have hlt_card := (Tuple.lt_card_lt_iff_apply_lt_of_monotone (Tuple.monotone_sort v)).mpr hc
    -- #{i | orderStat v i < v j₀} = #{j' | v j' < v j₀} = i₀ (bijection via Tuple.sort v)
    have hcard_eq : (Finset.univ.filter (fun i : Fin N => orderStat v i < v j₀)).card = i₀ := by
      rw [hi₀_def]
      exact Finset.card_equiv (Tuple.sort v) fun i => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Iff.rfl
    -- Chain: i₀ = ↑⟨i₀,_⟩ < #{...} = i₀, so i₀ < i₀, contradiction.
    have : i₀ < i₀ :=
      calc i₀ = ↑(⟨i₀, hi₀_lt_N⟩ : Fin N) := rfl
        _ < (Finset.univ.filter (fun i : Fin N => orderStat v i < v j₀)).card := hlt_card
        _ = i₀ := hcard_eq
    exact Nat.lt_irrefl i₀ this
  -- Step 10: (H₀.card : ℝ) ≤ (N : ℝ) − (i₀ : ℝ) in ℝ (from hi₀_le).
  have h_card_le_real : (H₀.card : ℝ) ≤ (N : ℝ) - (i₀ : ℝ) := by
    have h1 : H₀.card + i₀ ≤ N := by omega
    have h2 : (H₀.card : ℝ) + (i₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
    linarith
  -- Step 11: chain v j₀ ≤ α/(N−i₀) ≤ α/H₀.card.
  calc v j₀
      ≤ orderStat v ⟨i₀, hi₀_lt_N⟩ := hpval_le_order
    _ ≤ α / ((N : ℝ) - (i₀ : ℝ)) := hholm_at_i₀
    _ ≤ α / (H₀.card : ℝ) :=
        div_le_div_of_nonneg_left (le_of_lt hα) hH₀_cast_pos h_card_le_real

/-- **Holm–Bonferroni FWER control** (Holm 1979). If every null p-value is super-uniform, the
Holm step-down procedure at level `α` controls the family-wise error rate: `FWER ≤ α`. No
independence assumption is required. -/
theorem holm_fwer_le {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H₀ : Finset (Fin N)) (hH₀ : H₀.Nonempty) (p : Fin N → Ω → ℝ)
    -- LEAN-ONLY: measurability of each p-value; needed for the union bound over events
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: null marginals super-uniform; Holm (1979)
    (hnull : ∀ j ∈ H₀, SuperUniform (p j) μ) :
    FWER H₀ (holmRejects α p) μ ≤ ENNReal.ofReal α := by
  simp only [FWER]
  have hH₀_pos : 0 < H₀.card := hH₀.card_pos
  have hH₀_cast_pos : (0 : ℝ) < (H₀.card : ℝ) := Nat.cast_pos.mpr hH₀_pos
  have hcut_nonneg : 0 ≤ α / (H₀.card : ℝ) := le_of_lt (div_pos hα hH₀_cast_pos)
  have hcard_ne : (H₀.card : ℝ) ≠ 0 := hH₀_cast_pos.ne'
  -- Step 1: reduce to the union of level-α/N₀ events via holm_rejects_true_null_imp.
  -- Step 2: finite union bound (OuterMeasure).
  -- Step 3: super-uniformity of each null marginal.
  -- Step 4: sum collapses: N₀ · (α/N₀) = α.
  calc μ {ω | (holmRejects α p ω ∩ H₀).Nonempty}
      ≤ μ (⋃ j ∈ H₀, {ω | p j ω ≤ α / (H₀.card : ℝ)}) := by
          apply measure_mono
          intro ω hω
          obtain ⟨j, hjH₀, hjp⟩ := holm_rejects_true_null_imp α p H₀ ω (Set.mem_setOf.mp hω)
          exact Set.mem_biUnion hjH₀ hjp
    _ ≤ ∑ j ∈ H₀, μ {ω | p j ω ≤ α / (H₀.card : ℝ)} :=
          measure_biUnion_finset_le H₀ _
    _ ≤ ∑ j ∈ H₀, ENNReal.ofReal (α / (H₀.card : ℝ)) :=
          Finset.sum_le_sum fun j hj => hnull j hj _ hcut_nonneg
    _ = ENNReal.ofReal α := by
          rw [Finset.sum_const, ← ENNReal.ofReal_nsmul]
          congr 1
          rw [nsmul_eq_mul]
          field_simp

/-- **Bonferroni FWER control** (Lu-BDA §19.2.2). Rejecting `{ j : pⱼ ≤ α/N }` controls the
family-wise error rate: `FWER ≤ (N₀/N)·α ≤ α`. -/
theorem bonferroni_fwer_le {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H₀ : Finset (Fin N)) (p : Fin N → Ω → ℝ)
    -- LEAN-ONLY: measurability of each p-value; needed for the union bound over events
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: null marginals super-uniform; Lu-BDA §19.2.2
    (hnull : ∀ j ∈ H₀, SuperUniform (p j) μ) :
    FWER H₀ (bonferroniRejects α p) μ ≤ ENNReal.ofReal ((H₀.card : ℝ) / N * α) := by
  simp only [FWER]
  have hN_cast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hcut_nonneg : 0 ≤ α / (N : ℝ) := le_of_lt (div_pos hα hN_cast_pos)
  -- Handle H₀ = ∅ separately (FWER = 0 ≤ 0).
  rcases Finset.eq_empty_or_nonempty H₀ with rfl | hH₀_ne
  · simp [Finset.inter_empty]
  -- Main case: H₀ nonempty.
  -- Step 1: reduce to the union of level-α/N events via bonferroni membership.
  -- Step 2: finite union bound. Step 3: super-uniformity. Step 4: sum collapses.
  calc μ {ω | (bonferroniRejects α p ω ∩ H₀).Nonempty}
      ≤ μ (⋃ j ∈ H₀, {ω | p j ω ≤ α / (N : ℝ)}) := by
          apply measure_mono
          intro ω hω
          simp only [Set.mem_setOf_eq] at hω
          obtain ⟨j, hj⟩ := hω
          obtain ⟨hj_bon, hj_H₀⟩ := Finset.mem_inter.mp hj
          rw [bonferroniRejects, Finset.mem_filter] at hj_bon
          rw [Set.mem_iUnion₂]
          exact ⟨j, hj_H₀, hj_bon.2⟩
    _ ≤ ∑ j ∈ H₀, μ {ω | p j ω ≤ α / (N : ℝ)} :=
          measure_biUnion_finset_le H₀ _
    _ ≤ ∑ j ∈ H₀, ENNReal.ofReal (α / (N : ℝ)) :=
          Finset.sum_le_sum fun j hj => hnull j hj _ hcut_nonneg
    _ = ENNReal.ofReal ((H₀.card : ℝ) / N * α) := by
          rw [Finset.sum_const, ← ENNReal.ofReal_nsmul]
          congr 1
          rw [nsmul_eq_mul]
          push_cast
          ring

end StatLean.MultipleTesting
