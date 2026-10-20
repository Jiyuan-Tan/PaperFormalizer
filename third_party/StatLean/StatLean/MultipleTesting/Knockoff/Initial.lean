module
public import StatLean.MultipleTesting.Knockoff.Procedure
public import StatLean.MultipleTesting.Knockoff.Defs
public import StatLean.MultipleTesting.ForMathlib.BinomialRatio
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Knock-off initial bound: `E[V₊(0)/(1+V₋(0))] ≤ 1`

In the knock-off variable-selection procedure each hypothesis $j$ is given a score
$W_j = w_j(Z_j, \tilde Z_j)$, and at threshold $t$ one records the true-null positive and negative
counts
$$V_+(t) = \#\{\, j \in H_0 : |W_j| \ge t,\ \operatorname{sign}(W_j) = +1 \,\}, \qquad
  V_-(t) = \#\{\, j \in H_0 : |W_j| \ge t,\ \operatorname{sign}(W_j) = -1 \,\},$$
where $H_0$ is the set of true nulls and $N_0 = \#H_0$. The false-discovery-rate control proof
reduces, through an optimal-stopping / super-martingale argument, to the base inequality at
threshold $t = 0$:
$$\mathbb{E}\!\left[\frac{V_+(0)}{1 + V_-(0)}\right] \le 1.$$

`knockoff_initial_le` proves exactly this bound. At threshold $0$ the magnitude condition
$|W_j| \ge 0$ is vacuous, so every untied null is counted as either positive or negative and
$V_+(0) + V_-(0) \le N_0$. By condition 3 of the knock-off score definition — the signs
$\operatorname{sign}(W_j)$ given the magnitudes $|W_1|,\dots,|W_d|$ are i.i.d.\ $\mathrm{Ber}(1/2)$ —
the negative count obeys $V_-(0) \sim \mathrm{Binomial}(N_0, 1/2)$, so the expectation expands to
the finite binomial-ratio sum
$$\sum_{k=0}^{N_0} \binom{N_0}{k} 2^{-N_0}\, \frac{k}{1 + (N_0 - k)} \;=\; 1 - 2^{-N_0} \;\le\; 1.$$

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 21 (Knock-Off), §21.3 (Knock-Off),
Definition 21.1 (Knock-Off Score), condition 3 (i.i.d.\ fair signs); the bound
`E[V₊(0)/(1+V₋(0))] ≤ 1` is the $t = 0$ base case of the super-martingale argument in the proof
of Theorem 21.2 (Knock-Off).

**Proof formalization notes.**
*Algebraic half.* `binom_ratio_sum_le_one_local` proves
$\sum_{k=0}^{N} \binom{N}{k} 2^{-N}\, k/(1+(N-k)) = 1 - 2^{-N} \le 1$. Each term equals
$\binom{N+1}{k} 2^{-N} - \binom{N}{k} 2^{-N}$, from the identity
$\binom{N}{k}(N+1) = \binom{N+1}{k}(N+1-k)$ (`Nat.choose_mul_succ_eq`); the sum then telescopes via
the partial-sum formula $\sum_{k=0}^{N} \binom{N+1}{k} = 2^{N+1} - 1$. This is proved locally and
is deliberately independent of `BinomialRatio.binom_ratio_sum_le_one` (the imported general version
still carries a `sorry`), which is why the local copy is used.
*Probability half.* `knockoff_initial_integral_le_binom_sum` reduces the expectation to that sum:
pointwise $V_+(0)/(1+V_-(0)) \le (N_0 - V_-(0))/(1 + V_-(0))$ from $V_+(0) \le N_0 - V_-(0)$
(`vplus_add_vminus_le`); both integrands are bounded by $N_0$, hence integrable; and the law of
$V_-(0)$ is obtained from `signCell_measure` (each fixed sign configuration on $H_0$ has probability
$2^{-N_0}$, by the i.i.d.\ fair-sign field of condition 3, via
`KnockoffScore.signs_iIndep`/`signs_fair`), giving
`prob_Vminus0_eq` : $\mu\{V_-(0) = m\} = \binom{N_0}{m} 2^{-N_0}$. Integrating against this
binomial law and reindexing $k = N_0 - m$ yields the claimed sum. (Earlier drafts left this half as
a named sorry; it is now fully proved here.)

**Bibliographic comments.** The knock-off framework originates with R. F. Barber and E. J. Candès,
"Controlling the false discovery rate via knockoffs," *The Annals of Statistics* 43(5):2055–2085,
2015 (preprint arXiv:1404.5609). The structural fact used here — that, conditional on the
magnitudes $|W_1|,\dots,|W_d|$, the signs of the true-null statistics are i.i.d.\ fair coin flips —
is their i.i.d.-sign ("coin-flip") lemma (Lemma 1), and the optimal-stopping / super-martingale
argument for which `E[V₊(0)/(1+V₋(0))] ≤ 1` is the base step underlies their FDR-control results
(the knockoff and knockoff+ theorems, their Theorems 1 and 2). The closed form $1 - 2^{-N_0}$ for
the base-case binomial-ratio sum is an elementary rendering of that base step and is
standard.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

-- At t = 0 the magnitude condition `0 ≤ |Wⱼ|` is trivial; simplify to sign conditions alone.

private lemma Splus_zero (W : Fin d → Ω → ℝ) (ω : Ω) :
    Splus W 0 ω = Finset.univ.filter (fun j => 0 < W j ω) := by
  ext j
  simp only [Splus, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨abs_nonneg _, h⟩⟩

private lemma Sminus_zero (W : Fin d → Ω → ℝ) (ω : Ω) :
    Sminus W 0 ω = Finset.univ.filter (fun j => W j ω < 0) := by
  ext j
  simp only [Sminus, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨abs_nonneg _, h⟩⟩

/-- At threshold `0`, `V₊(0) + V₋(0) ≤ N₀` since they count disjoint subsets of `H₀`
(positive and negative nulls are disjoint; Lu-BDA §21.3). -/
private lemma vplus_add_vminus_le (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (ω : Ω) :
    Vplus W H₀ 0 ω + Vminus W H₀ 0 ω ≤ H₀.card := by
  unfold Vplus Vminus
  rw [Splus_zero, Sminus_zero]
  have hdisj : Disjoint
      (Finset.univ.filter (fun j => 0 < W j ω) ∩ H₀)
      (Finset.univ.filter (fun j => W j ω < 0) ∩ H₀) :=
    Finset.disjoint_left.mpr fun j hj1 hj2 => by
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
      linarith [hj1.1, hj2.1]
  have hunion_sub :
      (Finset.univ.filter (fun j => 0 < W j ω) ∩ H₀) ∪
      (Finset.univ.filter (fun j => W j ω < 0) ∩ H₀) ⊆ H₀ :=
    Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  have h4 := Finset.card_union_of_disjoint hdisj
  have h5 := Finset.card_le_card hunion_sub
  omega

/-! ## Local algebraic proof of the binomial ratio sum inequality

`∑_{k=0}^N C(N,k)/2^N · k/(1+(N−k)) ≤ 1`.

Proof: each term equals `C(N+1,k)/2^N − C(N,k)/2^N` (from `Nat.choose_mul_succ_eq`), the sum
telescopes to `(∑_{k=0}^N C(N+1,k) − ∑_{k=0}^N C(N,k)) / 2^N = (2^{N+1}−1−2^N)/2^N = 1−1/2^N ≤ 1`.
This is independent of `BinomialRatio.binom_ratio_sum_le_one` (which has a sorry). -/

/-- Per-term identity: `C(N,k)/2^N · k/(1+(N−k)) = C(N+1,k)/2^N − C(N,k)/2^N`. Follows from
`Nat.choose_mul_succ_eq N k : C(N,k)·(N+1) = C(N+1,k)·(N+1−k)`. -/
private lemma binom_ratio_term_eq (N k : ℕ) (hkN : k ≤ N) :
    (N.choose k : ℝ) / 2 ^ N * ((k : ℝ) / (1 + ((N : ℝ) - k))) =
    (N + 1).choose k / 2 ^ N - N.choose k / 2 ^ N := by
  have h2N : (2 : ℝ) ^ N ≠ 0 := by positivity
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hd_pos : (0 : ℝ) < 1 + ((N : ℝ) - k) := by linarith
  have hkN1 : k ≤ N + 1 := Nat.le_succ_of_le hkN
  -- Key: C(N,k) * (N+1) = C(N+1,k) * (1+(N−k)) in ℝ (from choose_mul_succ_eq)
  have hR : (N.choose k : ℝ) * ((N : ℝ) + 1) =
      ((N + 1).choose k : ℝ) * (1 + ((N : ℝ) - k)) :=
    calc (N.choose k : ℝ) * ((N : ℝ) + 1)
        = ((N.choose k * (N + 1) : ℕ) : ℝ) := by push_cast; ring
      _ = (((N + 1).choose k * (N + 1 - k) : ℕ) : ℝ) := by
            exact_mod_cast Nat.choose_mul_succ_eq N k
      _ = ((N + 1).choose k : ℝ) * ((N + 1 - k : ℕ) : ℝ) := by push_cast; ring
      _ = ((N + 1).choose k : ℝ) * (1 + ((N : ℝ) - k)) := by
            congr 1; rw [Nat.cast_sub hkN1]; push_cast; ring
  field_simp [h2N, hd_pos.ne']
  linear_combination hR

/-- `∑_{k=0}^N C(N,k)/2^N · k/(1+(N−k)) = 1 − 1/2^N ≤ 1`. -/
private lemma binom_ratio_sum_le_one_local (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      (N.choose k : ℝ) / 2 ^ N * ((k : ℝ) / (1 + ((N : ℝ) - k)))) ≤ 1 := by
  have h2N_pos : (0 : ℝ) < 2 ^ N := by positivity
  -- Sufficient: show the sum equals 1 − 1/2^N
  suffices h : ∑ k ∈ Finset.range (N + 1),
      (N.choose k : ℝ) / 2 ^ N * ((k : ℝ) / (1 + ((N : ℝ) - k))) = 1 - 1 / 2 ^ N by
    linarith [div_pos one_pos h2N_pos]
  -- Rewrite each term via binom_ratio_term_eq
  rw [Finset.sum_congr rfl fun k hk =>
    binom_ratio_term_eq N k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  -- Split: ∑(A − B) = ∑A − ∑B
  rw [Finset.sum_sub_distrib]
  -- Compute ∑_{k=0}^N C(N,k)/2^N = 1
  have hN : ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) / 2 ^ N = 1 := by
    rw [← Finset.sum_div]
    have : (∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ)) = 2 ^ N := by
      exact_mod_cast Nat.sum_range_choose N
    rw [this, div_self h2N_pos.ne']
  -- Compute ∑_{k=0}^N C(N+1,k)/2^N = 2 − 1/2^N
  have hN1 : ∑ k ∈ Finset.range (N + 1), ((N + 1).choose k : ℝ) / 2 ^ N = 2 - 1 / 2 ^ N := by
    rw [← Finset.sum_div]
    -- Partial sum: ∑_{k=0}^N C(N+1,k) = 2^{N+1} − 1
    have hpartial : ∑ k ∈ Finset.range (N + 1), (N + 1).choose k = 2 ^ (N + 1) - 1 := by
      have h := Nat.sum_range_choose (N + 1)
      rw [Finset.sum_range_succ, Nat.choose_self] at h
      omega
    have hcastsum : (∑ k ∈ Finset.range (N + 1), ((N + 1).choose k : ℝ)) =
        (2 : ℝ) ^ (N + 1) - 1 := by
      have h1 : 1 ≤ 2 ^ (N + 1) := Nat.one_le_two_pow
      calc (∑ k ∈ Finset.range (N + 1), ((N + 1).choose k : ℝ))
          = ((∑ k ∈ Finset.range (N + 1), (N + 1).choose k : ℕ) : ℝ) := by norm_cast
        _ = ((2 ^ (N + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hpartial
        _ = (2 : ℝ) ^ (N + 1) - 1 := by rw [Nat.cast_sub h1]; push_cast; ring
    rw [hcastsum]
    have h2N1 : (2 : ℝ) ^ (N + 1) = 2 * 2 ^ N := by ring
    rw [h2N1]
    field_simp
  linarith [hN, hN1]

/-! ## Distribution of `V₋(0)`: the i.i.d. fair-sign / Binomial(N₀,½) reduction -/

/-- `V₋(0) ω` counts the negative nulls. -/
private lemma Vminus0_eq_filter_card (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (ω : Ω) :
    Vminus W H₀ 0 ω = (H₀.filter (fun j => W j ω < 0)).card := by
  unfold Vminus
  rw [Sminus_zero]
  congr 1
  ext j
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

omit mΩ in
private lemma Vminus0_le (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (ω : Ω) :
    Vminus W H₀ 0 ω ≤ H₀.card := by
  rw [Vminus0_eq_filter_card]; exact Finset.card_filter_le _ _

/-- `sgnReal W j` is measurable. -/
private lemma measurable_sgnReal (W : Fin d → Ω → ℝ) (hW : ∀ j, Measurable (W j)) (j : Fin d) :
    Measurable (fun ω => sgnReal W j ω) :=
  Measurable.ite (measurableSet_le measurable_const (hW j)) measurable_const measurable_const

/-- `V₋(0)` is measurable. -/
private lemma measurable_Vminus0 (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hW : ∀ j, Measurable (W j)) : Measurable (fun ω => Vminus W H₀ 0 ω) := by
  have heq : (fun ω => Vminus W H₀ 0 ω) =
      fun ω => ∑ j ∈ H₀, if W j ω < 0 then 1 else 0 := by
    funext ω; rw [Vminus0_eq_filter_card, Finset.card_filter]
  rw [heq]
  exact Finset.measurable_sum _ fun j _ =>
    Measurable.ite (measurableSet_lt (hW j) measurable_const) measurable_const measurable_const

/-- `V₊(0)` is measurable. -/
private lemma measurable_Vplus0 (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hW : ∀ j, Measurable (W j)) : Measurable (fun ω => Vplus W H₀ 0 ω) := by
  have heq : (fun ω => Vplus W H₀ 0 ω) =
      fun ω => ∑ j ∈ H₀, if 0 < W j ω then 1 else 0 := by
    funext ω
    have hf : Vplus W H₀ 0 ω = (H₀.filter (fun j => 0 < W j ω)).card := by
      unfold Vplus; rw [Splus_zero]; congr 1; ext j
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    rw [hf, Finset.card_filter]
  rw [heq]
  exact Finset.measurable_sum _ fun j _ =>
    Measurable.ite (measurableSet_lt measurable_const (hW j)) measurable_const measurable_const

/-- The sign-configuration cell for a candidate negative set `T ⊆ H₀`. -/
private def signCell (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (T : Finset (Fin d)) : Set Ω :=
  ⋂ i ∈ (Finset.univ : Finset H₀),
    (fun ω => sgnReal W (i : Fin d) ω) ⁻¹' (if (i : Fin d) ∈ T then {(-1 : ℝ)} else {(1 : ℝ)})

/-- Each cell has probability `2^{-N₀}` (i.i.d. fair signs). -/
private lemma signCell_measure (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin d → Ω → ℝ)
    (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ) (T : Finset (Fin d)) :
    μ (signCell W H₀ T) = (1 / 2) ^ H₀.card := by
  rw [signCell, hW.signs_iIndep.measure_inter_preimage_eq_mul Finset.univ
      (fun i _ => by split_ifs <;> exact measurableSet_singleton _)]
  have hfac : ∀ i : H₀,
      μ ((fun ω => sgnReal W (i : Fin d) ω) ⁻¹'
        (if (i : Fin d) ∈ T then {(-1 : ℝ)} else {(1 : ℝ)})) = 1 / 2 := by
    intro i
    have hsgn1 : ∀ ω, sgnReal W (i : Fin d) ω = 1 ↔ 0 ≤ W (i : Fin d) ω := by
      intro ω; unfold sgnReal; constructor
      · intro h; by_contra hc; rw [if_neg hc] at h; norm_num at h
      · intro h; rw [if_pos h]
    have hsgnneg : ∀ ω, sgnReal W (i : Fin d) ω = -1 ↔ W (i : Fin d) ω < 0 := by
      intro ω; unfold sgnReal; constructor
      · intro h; by_contra hc; rw [if_pos (not_lt.mp hc)] at h; norm_num at h
      · intro h; rw [if_neg (not_le.mpr h)]
    have hge : {ω | (0 : ℝ) ≤ W (i : Fin d) ω} = (fun ω => sgnReal W (i : Fin d) ω) ⁻¹' {1} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact (hsgn1 ω).symm
    have hlt : {ω | W (i : Fin d) ω < 0} = (fun ω => sgnReal W (i : Fin d) ω) ⁻¹' {-1} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact (hsgnneg ω).symm
    have h12 : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 := by
      calc (1 : ℝ≥0∞) - 1 / 2 = (1 / 2 + 1 / 2) - 1 / 2 := by rw [ENNReal.add_halves]
        _ = 1 / 2 := ENNReal.add_sub_cancel_left (by simp)
    split_ifs with h
    · rw [← hlt]
      have hcompl : {ω | W (i : Fin d) ω < 0} = {ω | (0 : ℝ) ≤ W (i : Fin d) ω}ᶜ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
      rw [hcompl, prob_compl_eq_one_sub
        (measurableSet_le measurable_const (hW.meas (i : Fin d))), hW.signs_fair _ i.2, h12]
    · rw [← hge]; exact hW.signs_fair _ i.2
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const, Finset.card_univ,
    Fintype.card_coe]

/-- The negative-null count has the Binomial(N₀,½) law. -/
private lemma prob_Vminus0_eq (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin d → Ω → ℝ)
    (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ) (m : ℕ) :
    μ {ω | Vminus W H₀ 0 ω = m} = (H₀.card.choose m : ℝ≥0∞) * (1 / 2) ^ H₀.card := by
  classical
  -- membership in a cell ⟺ negative-null set equals T
  have hcell_iff : ∀ (T : Finset (Fin d)), T ⊆ H₀ → ∀ ω,
      ω ∈ signCell W H₀ T ↔ H₀.filter (fun j => W j ω < 0) = T := by
    intro T hT ω
    rw [signCell]
    simp only [Set.mem_iInter, Finset.mem_univ, forall_true_left, Set.mem_preimage,
      Subtype.forall]
    constructor
    · intro h
      ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hjH, hjlt⟩
        by_contra hjT
        have := h j hjH
        simp only [hjT, if_false, Set.mem_singleton_iff, sgnReal] at this
        rw [if_neg (not_le.mpr hjlt)] at this; norm_num at this
      · intro hjT
        have hjH := hT hjT
        refine ⟨hjH, ?_⟩
        have := h j hjH
        simp only [hjT, if_true, Set.mem_singleton_iff, sgnReal] at this
        by_contra hjnlt
        rw [if_pos (not_lt.mp hjnlt)] at this; norm_num at this
    · intro hfilt j hjH
      by_cases hjT : j ∈ T
      · have hjlt : W j ω < 0 := by
          have : j ∈ H₀.filter (fun j => W j ω < 0) := hfilt ▸ hjT
          exact (Finset.mem_filter.mp this).2
        simp only [hjT, if_true, Set.mem_singleton_iff, sgnReal, if_neg (not_le.mpr hjlt)]
      · have hjnlt : ¬ W j ω < 0 := by
          intro hlt
          exact hjT (hfilt ▸ Finset.mem_filter.mpr ⟨hjH, hlt⟩)
        simp only [hjT, if_false, Set.mem_singleton_iff, sgnReal, if_pos (not_lt.mp hjnlt)]
  -- decompose the event as a disjoint union of cells over T ∈ powersetCard m H₀
  have hdecomp : {ω | Vminus W H₀ 0 ω = m} =
      ⋃ T ∈ H₀.powersetCard m, signCell W H₀ T := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard, exists_prop]
    rw [Vminus0_eq_filter_card]
    constructor
    · intro hcard
      exact ⟨H₀.filter (fun j => W j ω < 0), ⟨Finset.filter_subset _ _, hcard⟩,
        (hcell_iff _ (Finset.filter_subset _ _) ω).mpr rfl⟩
    · rintro ⟨T, ⟨hTsub, hTcard⟩, hmem⟩
      rw [(hcell_iff T hTsub ω).mp hmem]; exact hTcard
  rw [hdecomp]
  rw [measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (fun T _ => signCell_measure μ W H₀ hW T), Finset.sum_const,
      Finset.card_powersetCard, nsmul_eq_mul]
  · -- disjointness
    intro T hT T' hT' hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω hω hω'
    apply hne
    rw [← (hcell_iff T (Finset.mem_powersetCard.mp hT).1 ω).mp hω,
      ← (hcell_iff T' (Finset.mem_powersetCard.mp hT').1 ω).mp hω']
  · -- measurability of each cell
    intro T _
    apply MeasurableSet.biInter (Finset.countable_toSet _)
    intro i _
    exact (measurable_sgnReal W hW.meas _) (by split_ifs <;> exact measurableSet_singleton _)

/-- The integral `E[V₊(0)/(1+V₋(0))]` is bounded by the binomial ratio sum (Lu-BDA §21.3).
`V₊(0) ≤ N₀ − V₋(0)` pointwise (`vplus_add_vminus_le`), and `V₋(0) ~ Bin(N₀, ½)` (the null signs
are i.i.d. fair coins, `prob_Vminus0_eq`), so the expectation expands to
`∑_m C(N₀,m)/2^{N₀} · (N₀−m)/(1+m)`, which equals the claimed sum via `k = N₀−m`. -/
lemma knockoff_initial_integral_le_binom_sum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin d → Ω → ℝ) -- USER-INPUT: knock-off score; Lu-BDA §21.3, Definition 21.1 (Knock-Off Score)
    (H₀ : Finset (Fin d)) -- USER-INPUT: true null set; Lu-BDA §21.3
    (hW : KnockoffScore W H₀ μ) : -- USER-INPUT: W satisfies Definition 21.1 (Knock-Off Score) cond. 3; Lu-BDA §21.3
    ∫ ω, (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) ∂μ ≤
    ∑ k ∈ Finset.range (H₀.card + 1),
      (H₀.card.choose k : ℝ) / 2 ^ H₀.card * ((k : ℝ) / (1 + ((H₀.card : ℝ) - k))) := by
  classical
  set N₀ := H₀.card with hN₀
  set g : ℕ → ℝ := fun m => ((N₀ : ℝ) - m) / (1 + m) with hgdef
  have hmVm : Measurable (fun ω => Vminus W H₀ 0 ω) := measurable_Vminus0 W H₀ hW.meas
  have hmVp : Measurable (fun ω => Vplus W H₀ 0 ω) := measurable_Vplus0 W H₀ hW.meas
  have hVm_le : ∀ ω, Vminus W H₀ 0 ω ≤ N₀ := fun ω => Vminus0_le W H₀ ω
  have hVp_le : ∀ ω, Vplus W H₀ 0 ω ≤ N₀ := fun ω => by
    show (Splus W 0 ω ∩ H₀).card ≤ H₀.card
    exact Finset.card_le_card Finset.inter_subset_right
  -- Step 1: pointwise `V₊/(1+V₋) ≤ g(V₋)` (since `V₊ ≤ N₀ − V₋`).
  have hpt : ∀ ω, (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) ≤ g (Vminus W H₀ 0 ω) := by
    intro ω
    have hnum : (Vplus W H₀ 0 ω : ℝ) ≤ (N₀ : ℝ) - (Vminus W H₀ 0 ω : ℝ) := by
      have hc : (Vplus W H₀ 0 ω : ℝ) + (Vminus W H₀ 0 ω : ℝ) ≤ (N₀ : ℝ) := by
        rw [hN₀]; exact_mod_cast vplus_add_vminus_le W H₀ ω
      linarith
    simp only [hgdef]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_right hnum (by positivity)
  -- Integrability of both integrands (bounded by `N₀`).
  have hInt_low : Integrable (fun ω => (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ))) μ := by
    apply Integrable.mono' (integrable_const (N₀ : ℝ))
      ((measurable_from_top.comp hmVp).div
        (measurable_const.add (measurable_from_top.comp hmVm))).aestronglyMeasurable
    filter_upwards with ω
    change ‖(Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ))‖ ≤ (N₀ : ℝ)
    have hnn : (0 : ℝ) ≤ (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) :=
      div_nonneg (Nat.cast_nonneg _) (by positivity)
    rw [Real.norm_of_nonneg hnn,
      div_le_iff₀ (by positivity : (0 : ℝ) < 1 + (Vminus W H₀ 0 ω : ℝ))]
    have hVp : (Vplus W H₀ 0 ω : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hVp_le ω
    nlinarith [hVp, (Nat.cast_nonneg (Vminus W H₀ 0 ω) : (0:ℝ) ≤ _),
      (Nat.cast_nonneg N₀ : (0:ℝ) ≤ _)]
  have hInt_up : Integrable (fun ω => g (Vminus W H₀ 0 ω)) μ := by
    apply Integrable.mono' (integrable_const (N₀ : ℝ))
    · simp only [hgdef]
      exact ((measurable_const.sub (measurable_from_top.comp hmVm)).div
        (measurable_const.add (measurable_from_top.comp hmVm))).aestronglyMeasurable
    · filter_upwards with ω
      have hVm : (Vminus W H₀ 0 ω : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hVm_le ω
      simp only [hgdef]
      have hnn : (0 : ℝ) ≤ ((N₀ : ℝ) - (Vminus W H₀ 0 ω : ℝ)) / (1 + (Vminus W H₀ 0 ω : ℝ)) :=
        div_nonneg (by linarith) (by positivity)
      rw [Real.norm_of_nonneg hnn,
        div_le_iff₀ (by positivity : (0 : ℝ) < 1 + (Vminus W H₀ 0 ω : ℝ))]
      nlinarith [hVm, (Nat.cast_nonneg (Vminus W H₀ 0 ω) : (0:ℝ) ≤ _),
        (Nat.cast_nonneg N₀ : (0:ℝ) ≤ _)]
  -- Helper: each per-value measure equals `C(N₀,m)/2^{N₀}`.
  have htoReal : ∀ m, (μ {ω | Vminus W H₀ 0 ω = m}).toReal = (N₀.choose m : ℝ) / 2 ^ N₀ := by
    intro m
    rw [prob_Vminus0_eq μ W H₀ hW m, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_pow,
      (show ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 by
        rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat]; norm_num)]
    rw [div_pow, one_pow, mul_one_div]
  -- `∫ 𝟙{V₋(0) = m} = μ{V₋(0) = m}`.
  have hint_eq : ∀ m, ∫ ω, (if Vminus W H₀ 0 ω = m then (1 : ℝ) else 0) ∂μ =
      (μ {ω | Vminus W H₀ 0 ω = m}).toReal := by
    intro m
    have h1 : (fun ω => (if Vminus W H₀ 0 ω = m then (1 : ℝ) else 0)) =
        Set.indicator {ω | Vminus W H₀ 0 ω = m} (fun _ => 1) := by
      funext ω; by_cases h : Vminus W H₀ 0 ω = m <;>
        simp [Set.indicator_apply, Set.mem_setOf_eq, h]
    have hms : MeasurableSet {ω | Vminus W H₀ 0 ω = m} := hmVm (measurableSet_singleton m)
    rw [h1, integral_indicator_const (1 : ℝ) hms, smul_eq_mul, mul_one]
    rfl
  -- Step 2: integrate monotonically, expand over the distribution, reindex `m = N₀ − k`.
  calc ∫ ω, (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) ∂μ
      ≤ ∫ ω, g (Vminus W H₀ 0 ω) ∂μ := integral_mono hInt_low hInt_up hpt
    _ = ∑ m ∈ Finset.range (N₀ + 1), g m * (μ {ω | Vminus W H₀ 0 ω = m}).toReal := by
        have hpart : (fun ω => g (Vminus W H₀ 0 ω)) =
            fun ω => ∑ m ∈ Finset.range (N₀ + 1),
              g m * (if Vminus W H₀ 0 ω = m then (1 : ℝ) else 0) := by
          funext ω
          rw [Finset.sum_eq_single (Vminus W H₀ 0 ω)
            (fun m _ hm => by rw [if_neg (fun h => hm h.symm), mul_zero])
            (fun hc => absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (hVm_le ω))) hc),
            if_pos rfl, mul_one]
        rw [hpart, integral_finset_sum _ (fun m _ => by
          apply Integrable.const_mul
          apply Integrable.mono' (integrable_const (1 : ℝ))
            (Measurable.aestronglyMeasurable (Measurable.ite (hmVm (measurableSet_singleton m))
              measurable_const measurable_const))
          filter_upwards with ω
          rw [Real.norm_of_nonneg (by split_ifs <;> norm_num)]
          split_ifs <;> norm_num)]
        exact Finset.sum_congr rfl (fun m _ => by rw [integral_const_mul, hint_eq m])
    _ = ∑ m ∈ Finset.range (N₀ + 1), g m * ((N₀.choose m : ℝ) / 2 ^ N₀) := by
        apply Finset.sum_congr rfl; intro m _; rw [htoReal m]
    _ = ∑ k ∈ Finset.range (N₀ + 1),
          (N₀.choose k : ℝ) / 2 ^ N₀ * ((k : ℝ) / (1 + ((N₀ : ℝ) - k))) := by
        rw [← Finset.sum_range_reflect (fun m => g m * ((N₀.choose m : ℝ) / 2 ^ N₀)) (N₀ + 1)]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j ≤ N₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        simp only [hgdef, Nat.add_sub_cancel]
        rw [Nat.choose_symm hj', Nat.cast_sub hj']
        ring

/-- Initial bound (Lu-BDA §21.3): `E[V₊(0)/(1+V₋(0))] ≤ 1`. At threshold `0` the null positives
`V₊(0)` are `Binomial(N₀, ½)`-distributed (the null signs are i.i.d. fair coins), and the
expectation reduces to the binomial ratio sum ≤ 1 (proved algebraically via `choose_mul_succ_eq`). -/
theorem knockoff_initial_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin d → Ω → ℝ) -- USER-INPUT: knock-off score statistic; Lu-BDA §21.3, Definition 21.1 (Knock-Off Score)
    (H₀ : Finset (Fin d)) -- USER-INPUT: true null hypothesis set; Lu-BDA §21.3
    (hW : KnockoffScore W H₀ μ) : -- USER-INPUT: W satisfies Definition 21.1 (Knock-Off Score) cond. 3; Lu-BDA §21.3
    ∫ ω, (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) ∂μ ≤ 1 :=
  le_trans (knockoff_initial_integral_le_binom_sum μ W H₀ hW)
    (binom_ratio_sum_le_one_local H₀.card)

end StatLean.MultipleTesting
