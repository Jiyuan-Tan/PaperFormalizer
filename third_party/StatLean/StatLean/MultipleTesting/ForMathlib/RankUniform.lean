module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-!
# Exchangeability and rank uniformity

For an **exchangeable**, almost-surely pairwise-distinct family of real-valued statistics
$S_0, \dots, S_{m-1}$, the rank of any single $S_i$ is uniformly distributed on $\{1, \dots, m\}$.
Define the (1-indexed) rank of the $i$-th coordinate by
$$ R_i(\omega) \;=\; \#\{\, j : S_j(\omega) \le S_i(\omega) \,\}, $$
which always satisfies $1 \le R_i \le m$ (since $S_i \le S_i$), and is a bijection of the index set
onto $\{1, \dots, m\}$ whenever the values are distinct. The result is the equality
$$ \mathbb{P}\bigl(\{\, R_i \le k \,\}\bigr) \;=\; \frac{k}{m}, \qquad k \le m, $$
i.e. $R_i$ is uniform on $\{1, \dots, m\}$. This is the precise statement of the textbook remark
that, for exchangeable statistics $T_1, \dots, T_n$, "all rankings are equally likely."

The formalization adds three regularity hypotheses beyond the bare textbook statement: each
statistic $S_i$ is measurable, the family is exchangeable in the sense that the joint law of
$(S_0, \dots, S_{m-1})$ is invariant under permuting the indices, and the values are almost surely
pairwise distinct (the textbook works with continuous scores or assumes ties broken, which forces
distinctness; here it is made explicit). The conclusion is stated for a probability measure $\mu$.

**Reference.** E. J. Candès, *STAT 300C: Theory of Statistics*, Lecture Notes, Stanford University,
2023, Lecture 9, §9.6 ("A taste of conformal inference"). The rank-uniformity remark appears at the
close of §9.6 (p. 9-7) as the engine behind the conformal-coverage result Theorem 2 (split-conformal
$1 - \alpha$ coverage).

**Proof formalization notes.** The argument is split into a purely combinatorial layer on a fixed
real tuple $t : \mathrm{Fin}\, m \to \mathbb{R}$ and a measure-theoretic layer.

* `rankOf S i ω` — the rank $\#\{\, j : S_j(\omega) \le S_i(\omega) \,\}$ of $S_i$ (1-indexed;
  $S_i \le S_i$ always, so `rankOf ≥ 1`, and with distinct values `i ↦ rankOf S i ω` is a bijection
  onto $\{1, \dots, m\}$).
* `Exchangeable S μ` — the joint law of $(S_0, \dots, S_{m-1})$ is invariant under index
  permutations, `Measure.map (fun ω i => S (σ i) ω) μ = Measure.map (fun ω i => S i ω) μ` for every
  permutation `σ` (Mathlib has **no** `Exchangeable`, so we define it).
* `measure_rankOf_le` — the headline result $\mu\{\, \mathrm{rankOf}\, S\, i \le k \,\} = k/m$ for
  $k \le m$.

Combinatorial core (`rk`, on a fixed tuple): rank is strictly monotone along values
(`rk_lt_rk`), lies in $[1, m]$ (`rk_pos`, `rk_le`), is injective for an injective tuple
(`rk_injective`), and is permutation-equivariant (`rk_comp_perm`: ranking a permuted tuple at $i$
equals ranking the original at $\sigma(i)$). Hence for an injective tuple the ranks fill
$\{1, \dots, m\}$ exactly (`rk_image_univ`), and exactly $k$ coordinates have rank $\le k$
(`card_filter_rk_le`). Measure-theoretic assembly: (1) push $\mu$ forward along the tuple map
$T(\omega) = (S_0(\omega), \dots)$; (2) exchangeability + equivariance show all $m$ rank
probabilities $\mu\{R_j \le k\}$ are equal (using the transposition $\sigma = (i\, j)$); (3) summing
the rank-event indicators pointwise gives $k$ almost surely (by `card_filter_rk_le` on the
a.s.-injective sample); (4) therefore $m \cdot \mu\{R_i \le k\} = k$, and dividing by $m$ (nonzero
since `Fin m` is inhabited) yields $k/m$.

**Bibliographic comments.** The rank-uniformity statement is classical **folklore** of exchangeable
sequences and has no single seminal origin: for exchangeable random variables with almost surely
distinct values, the induced ranking is uniform over the symmetric group, an immediate consequence
of permutation-invariance of the joint law. Its role as the foundation of distribution-free
prediction was made explicit in the conformal-prediction program of V. Vovk, A. Gammerman, and
collaborators — see V. Vovk, A. Gammerman, G. Shafer, *Algorithmic Learning in a Random World*,
Springer, 2005 (2nd ed. 2022), and, for the split/inductive variant matching the calibration setup
here, H. Papadopoulos, K. Proedrou, V. Vovk, A. Gammerman, "Inductive Confidence Machines for
Regression," *Proc. ECML 2002*, LNCS 2430, Springer, 2002, pp. 345–356 (the source of the
coverage Theorem 2 cited in Candès §9.6).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {m : ℕ}

/-- The rank of `Sᵢ` among `S₀, …, S_{m-1}`: `#{ j : Sⱼ(ω) ≤ Sᵢ(ω) }` (1-indexed). -/
noncomputable def rankOf (S : Fin m → Ω → ℝ) (i : Fin m) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun j => S j ω ≤ S i ω)).card

/-- `Exchangeable S μ`: the joint law of `(S₀,…,S_{m-1})` is invariant under index permutations —
`Measure.map (fun ω i => S (σ i) ω) μ = Measure.map (fun ω i => S i ω) μ` for every `σ`. -/
def Exchangeable (S : Fin m → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ σ : Equiv.Perm (Fin m),
    Measure.map (fun ω => (fun i => S (σ i) ω)) μ = Measure.map (fun ω => (fun i => S i ω)) μ

/-! ## Tuple-level rank and its combinatorics

We isolate the purely combinatorial content on a fixed real tuple `t : Fin m → ℝ`. Note
`rankOf S i ω = rk (fun l => S l ω) i` definitionally. -/

/-- The rank of coordinate `i` in a real tuple `t`: `#{ j : t j ≤ t i }`. -/
private noncomputable def rk (t : Fin m → ℝ) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun j => t j ≤ t i)).card

/-- `rankOf` is the tuple rank of the sample point. -/
private lemma rankOf_eq_rk (S : Fin m → Ω → ℝ) (i : Fin m) (ω : Ω) :
    rankOf S i ω = rk (fun l => S l ω) i := rfl

/-- Strict monotonicity of the rank along the values. -/
private lemma rk_lt_rk {t : Fin m → ℝ} {a b : Fin m} (h : t a < t b) : rk t a < rk t b := by
  unfold rk
  apply Finset.card_lt_card
  have hsub : Finset.univ.filter (fun j => t j ≤ t a)
      ⊆ Finset.univ.filter (fun j => t j ≤ t b) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans h.le⟩
  rw [Finset.ssubset_iff_of_subset hsub]
  refine ⟨b, ?_, ?_⟩
  · simp [Finset.mem_filter]
  · simp only [Finset.mem_filter, not_and]
    intro _
    exact not_le.mpr h

/-- The rank is at least `1` (coordinate `i` itself counts). -/
private lemma rk_pos (t : Fin m → ℝ) (i : Fin m) : 0 < rk t i := by
  unfold rk
  exact Finset.card_pos.mpr ⟨i, by simp [Finset.mem_filter]⟩

/-- The rank is at most `m`. -/
private lemma rk_le (t : Fin m → ℝ) (i : Fin m) : rk t i ≤ m := by
  unfold rk
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_univ]

/-- For an injective tuple the rank is an injective map `Fin m → ℕ`. -/
private lemma rk_injective {t : Fin m → ℝ} (ht : Function.Injective t) :
    Function.Injective (rk t) := by
  intro a b hab
  by_contra hne
  have htab : t a ≠ t b := fun h => hne (ht h)
  rcases lt_or_gt_of_ne htab with h | h
  · exact absurd hab (ne_of_lt (rk_lt_rk h))
  · exact absurd hab (ne_of_gt (rk_lt_rk h))

/-- Equivariance: ranking a permuted tuple at `i` is ranking the original tuple at `σ i`. -/
private lemma rk_comp_perm (t : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    rk (fun l => t (σ l)) i = rk t (σ i) := by
  unfold rk
  refine Finset.card_nbij' (fun j => σ j) (fun j => σ.symm j) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
    exact ha
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
    rw [Equiv.apply_symm_apply]; exact ha
  · intro a _; exact σ.symm_apply_apply a
  · intro a _; exact σ.apply_symm_apply a

/-- For an injective tuple the ranks fill `{1,…,m}` exactly. -/
private lemma rk_image_univ {t : Fin m → ℝ} (ht : Function.Injective t) :
    Finset.image (rk t) Finset.univ = Finset.Icc 1 m := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨i, _, rfl⟩ := hr
    rw [Finset.mem_Icc]
    exact ⟨rk_pos t i, rk_le t i⟩
  · rw [Finset.card_image_of_injective _ (rk_injective ht), Finset.card_univ, Fintype.card_fin,
      Nat.card_Icc]
    omega

/-- The counting heart: for an injective tuple and `k ≤ m`, exactly `k` coordinates have rank
`≤ k` (their ranks are the bijective image of `{1,…,k}`). -/
private lemma card_filter_rk_le {t : Fin m → ℝ} (ht : Function.Injective t) {k : ℕ} (hk : k ≤ m) :
    (Finset.univ.filter (fun i => rk t i ≤ k)).card = k := by
  have himg : Finset.image (rk t) (Finset.univ.filter (fun i => rk t i ≤ k)) = Finset.Icc 1 k := by
    ext r
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
    constructor
    · rintro ⟨i, hik, rfl⟩
      exact ⟨rk_pos t i, hik⟩
    · rintro ⟨h1, hk'⟩
      have hr : r ∈ Finset.image (rk t) Finset.univ := by
        rw [rk_image_univ ht, Finset.mem_Icc]; exact ⟨h1, hk'.trans hk⟩
      rw [Finset.mem_image] at hr
      obtain ⟨i, _, hi⟩ := hr
      exact ⟨i, by rw [hi]; exact hk', hi⟩
  rw [← Finset.card_image_of_injective _ (rk_injective ht), himg, Nat.card_Icc]
  omega

/-! ## Rank uniformity -/

/-- **Rank uniformity** (Candès L9 §9.6, the exchangeability core of conformal coverage). For an
exchangeable, a.s. pairwise-distinct family `S₀,…,S_{m-1}`, the rank of any `Sᵢ` is uniform:
`μ{ rankOf S i ≤ k } = k/m` for `k ≤ m`. -/
theorem measure_rankOf_le (S : Fin m → Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    -- USER-INPUT: each statistic is measurable; Candès L9 §9.6
    (hmeas : ∀ i, Measurable (S i))
    -- USER-INPUT: the family is exchangeable; Candès L9 §9.6
    (hExch : Exchangeable S μ)
    -- USER-INPUT: the statistics are a.s. pairwise distinct (continuous scores / tie-breaking);
    -- Candès L9 §9.6
    (hdistinct : ∀ᵐ ω ∂μ, Function.Injective (fun i => S i ω))
    (i : Fin m) {k : ℕ} (hk : k ≤ m) :
    μ {ω | rankOf S i ω ≤ k} = (k : ℝ≥0∞) / (m : ℝ≥0∞) := by
  -- measurability of the rank as a function of the tuple / of the sample point
  have hmeasrk : ∀ j : Fin m, Measurable (fun t : Fin m → ℝ => rk t j) := by
    intro j
    simp only [rk, Finset.card_filter]
    refine Finset.measurable_sum _ (fun l _ => ?_)
    exact Measurable.ite (measurableSet_le (measurable_pi_apply l) (measurable_pi_apply j))
      measurable_const measurable_const
  have hmeasrank : ∀ j : Fin m, Measurable (fun ω => rankOf S j ω) := by
    intro j
    simp only [rankOf, Finset.card_filter]
    refine Finset.measurable_sum _ (fun l _ => ?_)
    exact Measurable.ite (measurableSet_le (hmeas l) (hmeas j)) measurable_const measurable_const
  -- the tuple map and the rank-events
  set T : Ω → (Fin m → ℝ) := fun ω => fun l => S l ω with hTdef
  have hT : Measurable T := by
    rw [hTdef]; exact measurable_pi_lambda _ (fun l => hmeas l)
  have hA : ∀ j : Fin m, MeasurableSet {t : Fin m → ℝ | rk t j ≤ k} := by
    intro j
    have he : {t : Fin m → ℝ | rk t j ≤ k} = (fun t => rk t j) ⁻¹' Set.Iic k := rfl
    rw [he]; exact (hmeasrk j) MeasurableSet.of_discrete
  have hB : ∀ j : Fin m, MeasurableSet {ω | rankOf S j ω ≤ k} := by
    intro j
    have he : {ω | rankOf S j ω ≤ k} = (fun ω => rankOf S j ω) ⁻¹' Set.Iic k := rfl
    rw [he]; exact (hmeasrank j) MeasurableSet.of_discrete
  have hBT : ∀ j : Fin m, {ω | rankOf S j ω ≤ k} = T ⁻¹' {t : Fin m → ℝ | rk t j ≤ k} := by
    intro j; rw [hTdef]; rfl
  have hprecomp : ∀ σ : Equiv.Perm (Fin m),
      Measurable (fun t : Fin m → ℝ => (fun l => t (σ l))) :=
    fun σ => measurable_pi_lambda _ (fun l => measurable_pi_apply (σ l))
  -- Step 1+2: all rank probabilities coincide (permutation invariance of the law)
  have heq : ∀ j : Fin m, μ {ω | rankOf S j ω ≤ k} = μ {ω | rankOf S i ω ≤ k} := by
    intro j
    set σ : Equiv.Perm (Fin m) := Equiv.swap i j with hσ
    have hmap : Measure.map (fun t : Fin m → ℝ => (fun l => t (σ l))) (Measure.map T μ)
        = Measure.map T μ := by
      rw [Measure.map_map (hprecomp σ) hT]
      have hcomp : (fun t : Fin m → ℝ => (fun l => t (σ l))) ∘ T
          = fun ω => (fun l => S (σ l) ω) := by rw [hTdef]; rfl
      rw [hcomp, hTdef]
      exact hExch σ
    have e1 : μ {ω | rankOf S j ω ≤ k} = (Measure.map T μ) {t : Fin m → ℝ | rk t j ≤ k} := by
      rw [hBT j, ← Measure.map_apply hT (hA j)]
    have e2 : μ {ω | rankOf S i ω ≤ k} = (Measure.map T μ) {t : Fin m → ℝ | rk t i ≤ k} := by
      rw [hBT i, ← Measure.map_apply hT (hA i)]
    rw [e1, e2]
    conv_lhs => rw [← hmap]
    rw [Measure.map_apply (hprecomp σ) (hA j)]
    congr 1
    ext t
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [rk_comp_perm, hσ, Equiv.swap_apply_right]
  -- Step 3+4: the ranks are a.s. a bijection, so the probabilities sum to `k`
  have hsum_eq : ∑ j : Fin m, μ {ω | rankOf S j ω ≤ k} = (k : ℝ≥0∞) := by
    have hstep : ∀ j : Fin m, μ {ω | rankOf S j ω ≤ k}
        = ∫⁻ ω, ({ω | rankOf S j ω ≤ k}).indicator (1 : Ω → ℝ≥0∞) ω ∂μ :=
      fun j => (lintegral_indicator_one (hB j)).symm
    calc ∑ j : Fin m, μ {ω | rankOf S j ω ≤ k}
        = ∑ j : Fin m, ∫⁻ ω, ({ω | rankOf S j ω ≤ k}).indicator (1 : Ω → ℝ≥0∞) ω ∂μ := by
          simp_rw [hstep]
      _ = ∫⁻ ω, ∑ j : Fin m, ({ω | rankOf S j ω ≤ k}).indicator (1 : Ω → ℝ≥0∞) ω ∂μ :=
          (lintegral_finset_sum _ (fun j _ => measurable_one.indicator (hB j))).symm
      _ = ∫⁻ _ω, (k : ℝ≥0∞) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hdistinct] with ω hω
          have hsum_card : ∑ j : Fin m, ({ω | rankOf S j ω ≤ k}).indicator (1 : Ω → ℝ≥0∞) ω
              = ((Finset.univ.filter (fun j => rankOf S j ω ≤ k)).card : ℝ≥0∞) := by
            rw [Finset.card_filter, Nat.cast_sum]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Set.indicator_apply]
            by_cases h : rankOf S j ω ≤ k
            · simp [Set.mem_setOf_eq, h]
            · simp [Set.mem_setOf_eq, h]
          have hcard : (Finset.univ.filter (fun j => rankOf S j ω ≤ k)).card = k :=
            card_filter_rk_le hω hk
          rw [hsum_card, hcard]
      _ = (k : ℝ≥0∞) := by rw [lintegral_const, measure_univ, mul_one]
  -- combine: `m · μ{rankOf S i ≤ k} = k`
  have halleq : ∑ j : Fin m, μ {ω | rankOf S j ω ≤ k}
      = (m : ℝ≥0∞) * μ {ω | rankOf S i ω ≤ k} := by
    rw [Finset.sum_congr rfl (fun j _ => heq j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hmk : (m : ℝ≥0∞) * μ {ω | rankOf S i ω ≤ k} = (k : ℝ≥0∞) := halleq ▸ hsum_eq
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hmtop : (m : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top m
  rw [ENNReal.eq_div_iff hm0 hmtop]
  exact hmk

end StatLean.MultipleTesting
