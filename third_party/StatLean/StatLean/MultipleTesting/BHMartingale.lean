module
public import StatLean.MultipleTesting.BenjaminiHochberg

@[expose] public section

/-!
# Benjamini–Hochberg FDR — exact identity

Consider $N$ hypotheses tested with independent p-values $p_1, \dots, p_N$, of which the
subset $H_0$ (with $N_0 = |H_0|$) are true nulls. The Benjamini–Hochberg (BH) procedure at level
$\alpha$ rejects the hypotheses whose p-values fall at or below the adaptive threshold
$k^\ast \alpha / N$, where $k^\ast$ is the largest index $k$ for which at least $k$ p-values are
$\le k\alpha/N$. The false discovery proportion is $\mathrm{FDP} = V / (R \vee 1)$, where $V$ is the
number of true nulls rejected and $R$ the total number of rejections, and the false discovery rate
is $\mathrm{FDR} = \mathbb{E}[\mathrm{FDP}]$.

**Main result** (`benjamini_hochberg_fdr_eq`): if the p-values are jointly independent and every null
p-value is **exactly** uniform on $[0,1]$ (i.e. $\mathbb{P}(p_i \le t) = t$ for $t \in [0,1]$, not
merely the super-uniform domination $\mathbb{P}(p_i \le t) \le t$), then the BH procedure attains
FDR control with **equality**:
$$ \mathrm{FDR} = \frac{N_0}{N}\,\alpha. $$
This is the exact-identity companion to the super-uniform inequality $\mathrm{FDR} \le (N_0/N)\alpha$
formalized in `BenjaminiHochberg.lean`. We require $0 < \alpha \le 1$ and $N \ge 1$; the upper bound
$\alpha \le 1$ ensures every threshold $k\alpha/N \in [0,1]$ so that exact uniformity applies.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 20 (False Discovery Rate), §20.2 (False Discovery Rate:
Independent P-Values), Theorem 20.1; and
E. J. Candès, *STAT 300C: Theory of Statistics*, Lecture Notes, Stanford University, 2023,
Lecture 7, §7.2, Theorem 2 (BH attains $\mathrm{FDR} = (N_0/N)\,q$ under independent exactly-uniform
nulls, with the level written $q = \alpha$).

**Proof formalization notes.**

*On the proof technique.* The lecture proves this via a backwards-martingale + Doob's optional
stopping argument on `V(t)/t`. We obtain the **same identity** by the leave-one-out argument already
used for the inequality `benjamini_hochberg_fdr_le` (`BenjaminiHochberg.lean`): for each null `i`,
`E[ψᵢ/(R∨1)] = (α/N)·P(pᵢ ≤ …)`-style telescopes to `α/N` **with equality** because exact uniformity
gives `P(pᵢ ≤ kα/N) = kα/N` (the inequality version only had `≤`); summing over `H₀` gives
`(N₀/N)·α`. This avoids the continuous-time backwards-martingale machinery (absent from Mathlib)
while proving the identical theorem.

*On the re-derivation.* `BenjaminiHochberg.lean` proves the `≤` version; its leave-one-out
combinatorics, measurability, and independence helpers are all `private` to that file. We re-derive
the pieces we need in the `BHMartInternal` namespace below (verbatim where the inequality proof's
helpers transfer, strengthened where `≤` becomes `=`). The two genuinely new ingredients for the
identity are:

* `bh_loo_le_imp_mem` — the **converse** of `bh_mem_imp_le`: `pᵢ ≤ R(pᵢ→0)·α/N ⇒ i ∈ bhRejects`.
  This upgrades the pointwise domination of the `≤` proof to a pointwise **equality**
  (`bh_summand_eq_sum`).
* `numRej_loo_ge_one` — `R(pᵢ→0) ≥ 1` always (coordinate `i` is forced into the LOO rejection set
  since `pᵢ` is set to `0`), so `∑ₖ P(R(pᵢ→0)=k) = 1` exactly (not just `≤ 1`).

**Bibliographic comments.** The BH procedure and the exact independent-null identity originate with
Y. Benjamini and Y. Hochberg, "Controlling the false discovery rate: a practical and powerful
approach to multiple testing", *Journal of the Royal Statistical Society, Series B* 57(1):289–300,
1995; their Theorem 1 states $\mathrm{FDR} = (m_0/m)\,q$ for independent test statistics with the
nulls uniformly distributed (and $\mathrm{FDR} \le (m_0/m)\,q$ in general). The martingale /
optional-stopping reformulation underlying the lecture proof is due to J. D. Storey, J. E. Taylor and
D. Siegmund, "Strong control, conservative point estimation and simultaneous conservative
consistency of false discovery rates: a unified approach", *Journal of the Royal Statistical Society,
Series B* 66(1):187–205, 2004 (their empirical-process / backwards-martingale treatment of the BH
estimator $V(t)/t$). The leave-one-out argument formalized here is the discrete equivalent of that
martingale identity and gives the same exact-equality conclusion.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace BHMartInternal

/-! ## Re-derived BH count / kmax machinery (mirrors the `private` defs of `BenjaminiHochberg.lean`)

These reproduce the `private` helpers of `BenjaminiHochberg.lean` (inaccessible across modules) so
the leave-one-out identity can be assembled here. The definitions are byte-identical to the
originals, hence `bhRejects_eq_filter` / `bhNumRej_eq_pt` remain `rfl` against the public
`bhRejects`. -/

/-- The BH count: number of p-values at or below `m * α / N`. -/
private noncomputable def bhCount {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (m : ℕ) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun j => p j ω ≤ (m : ℝ) * α / (N : ℝ))).card

/-- The BH kmax: the maximum `k ≤ N` with `bhCount ≥ k`. -/
private noncomputable def bhKmax {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) : ℕ :=
  ((Finset.range (N + 1)).filter (fun m => m ≤ bhCount α p m ω)).sup id

/-- The BH rejection set expressed via `bhKmax`. -/
private lemma bhRejects_eq_filter {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) :
    bhRejects α p ω = Finset.univ.filter (fun j => p j ω ≤ (bhKmax α p ω : ℝ) * α / (N : ℝ)) :=
  rfl

/-- `bhKmax` is at most `N`. -/
private lemma bhKmax_le {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) :
    bhKmax α p ω ≤ N := by
  simp only [bhKmax]
  apply Finset.sup_le
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range, id] at hm ⊢
  omega

/-- If `K = bhKmax α p ω` and `K ≥ 1`, then `K ≤ bhCount α p K ω`. -/
private lemma bhKmax_le_count {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω)
    (hK : 0 < bhKmax α p ω) :
    bhKmax α p ω ≤ bhCount α p (bhKmax α p ω) ω := by
  set S := (Finset.range (N + 1)).filter (fun m => m ≤ bhCount α p m ω)
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    simp [S, bhKmax, h, Finset.sup_empty] at hK
  have hmem_S : bhKmax α p ω ∈ S := by
    have h := Finset.sup_mem_of_nonempty (f := id) hne
    simp only [Set.image_id, Finset.mem_coe] at h
    exact h
  exact (Finset.mem_filter.mp hmem_S).2

/-- For `m > bhKmax α p ω` with `m ≤ N`, `bhCount α p m ω < m`. -/
private lemma bhCount_lt_of_gt_kmax {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω)
    (m : ℕ) (hm : bhKmax α p ω < m) (hm' : m ≤ N) :
    bhCount α p m ω < m := by
  by_contra h
  push_neg at h
  have hmem : m ∈ (Finset.range (N + 1)).filter (fun k => k ≤ bhCount α p k ω) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hm', h⟩
  have hle : m ≤ ((Finset.range (N + 1)).filter (fun k => k ≤ bhCount α p k ω)).sup id :=
    Finset.le_sup (f := id) hmem
  simp only [bhKmax] at hm
  omega

/-- The BH count is monotone in the threshold index `m` (larger index ⇒ larger threshold ⇒ more
p-values pass). New helper, used by the converse leave-one-out lemma `bh_loo_le_imp_mem`. -/
-- LEAN-ONLY: `0 ≤ α` makes the threshold `m·α/N` monotone in `m`; pure combinatorial fact.
private lemma bhCount_mono {N : ℕ} (α : ℝ) (hα : 0 ≤ α) (p : Fin N → Ω → ℝ) (ω : Ω)
    {m m' : ℕ} (hmm : m ≤ m') : bhCount α p m ω ≤ bhCount α p m' ω := by
  simp only [bhCount]
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  refine le_trans hj ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hmm) hα)
    (inv_nonneg.mpr (Nat.cast_nonneg N))

/-! ## Leave-one-out combinatorial lemmas -/

/-- For LOO at `i`: `bhCount` with `p i` replaced by `0` equals `bhCount` of original when
`m * α / N ≥ p i ω` and `m * α / N ≥ 0`. -/
private lemma bhCount_loo_eq_of_ge {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (i : Fin N)
    (m : ℕ) (ω : Ω) (hm : p i ω ≤ (m : ℝ) * α / (N : ℝ))
    (hpos : 0 ≤ (m : ℝ) * α / (N : ℝ)) :
    bhCount α (Function.update p i (0 : Ω → ℝ)) m ω = bhCount α p m ω := by
  simp only [bhCount]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hji : j = i
  · subst hji
    simp only [Function.update_self]
    exact ⟨fun _ => hm, fun _ => hpos⟩
  · simp [Function.update_of_ne hji]

/-- **Converse leave-one-out crux** (the equality upgrade): if `pᵢ ≤ R(pᵢ→0)·α/N` then `i` is
rejected, where `R(pᵢ→0)` is the BH rejection count with `pᵢ` set to `0`. Together with the
forward `bh_mem_imp_le` this gives the pointwise identity `bh_summand_eq_sum`. -/
-- LEAN-ONLY: positivity of `N`, `α` for the threshold algebra; deterministic combinatorics.
private lemma bh_loo_le_imp_mem {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α)
    (p : Fin N → Ω → ℝ) (i : Fin N) (ω : Ω)
    (hle : p i ω ≤ (numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω : ℝ) * α / N) :
    i ∈ bhRejects α p ω := by
  classical
  set q := Function.update p i (0 : Ω → ℝ) with hq
  set r := numRejections (bhRejects α q) ω with hr
  -- r = bhCount α q (bhKmax α q ω) ω (the rejection count is the count at the threshold index).
  have hrK : r = bhCount α q (bhKmax α q ω) ω := by
    rw [hr]
    show (bhRejects α q ω).card = bhCount α q (bhKmax α q ω) ω
    rw [bhRejects_eq_filter]; rfl
  -- bhKmax ≤ r.
  have hKr : bhKmax α q ω ≤ r := by
    rcases Nat.eq_zero_or_pos (bhKmax α q ω) with hK0 | hKpos
    · rw [hK0]; exact Nat.zero_le _
    · rw [hrK]; exact bhKmax_le_count α q ω hKpos
  -- r ≤ N (rejection count ≤ number of hypotheses).
  have hrN : r ≤ N := by
    rw [hr]
    change (bhRejects α q ω).card ≤ N
    exact (Finset.card_le_univ _).trans_eq (by simp [Fintype.card_fin])
  -- bhCount α q r ω ≥ r, by monotonicity from K ≤ r.
  have hcount_qr : r ≤ bhCount α q r ω := by
    calc r = bhCount α q (bhKmax α q ω) ω := hrK
      _ ≤ bhCount α q r ω := bhCount_mono α hα.le q ω hKr
  -- pᵢ ≤ rα/N, so coordinate i is counted in both p and q at threshold r ⇒ counts agree.
  have hpos_r : (0 : ℝ) ≤ (r : ℝ) * α / N :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg r) hα.le) (Nat.cast_nonneg N)
  have hqr_eq : bhCount α q r ω = bhCount α p r ω := bhCount_loo_eq_of_ge α p i r ω hle hpos_r
  have hp_count : r ≤ bhCount α p r ω := hqr_eq ▸ hcount_qr
  -- r is a valid BH index for p, hence bhKmax α p ω ≥ r.
  have hrmem : r ∈ (Finset.range (N + 1)).filter (fun m => m ≤ bhCount α p m ω) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hrN, hp_count⟩
  have hKp_ge : r ≤ bhKmax α p ω := by
    have h := Finset.le_sup (f := id) hrmem
    simpa only [bhKmax, id_eq] using h
  -- pᵢ ≤ rα/N ≤ (bhKmax α p ω)·α/N, so i is rejected.
  have hthr : (r : ℝ) * α / N ≤ (bhKmax α p ω : ℝ) * α / N := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hKp_ge) hα.le)
      (inv_nonneg.mpr (Nat.cast_nonneg N))
  rw [bhRejects_eq_filter]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact le_trans hle hthr

/-- `R(pᵢ→0) ≥ 1`: setting `pᵢ := 0` forces coordinate `i` into the LOO rejection set (it passes
every threshold `K·α/N ≥ 0`), so the LOO rejection count is at least one. New helper; this is why
`∑ₖ P(R(pᵢ→0)=k) = 1` holds with equality. -/
-- LEAN-ONLY: positivity of the threshold; deterministic.
private lemma numRej_loo_ge_one {N : ℕ} (α : ℝ) (hα : 0 < α) (p : Fin N → Ω → ℝ) (i : Fin N)
    (ω : Ω) :
    1 ≤ numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω := by
  have hmem : i ∈ bhRejects α (Function.update p i (0 : Ω → ℝ)) ω := by
    rw [bhRejects_eq_filter, Finset.mem_filter]
    refine ⟨Finset.mem_univ i, ?_⟩
    simp only [Function.update_self, Pi.zero_apply]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hα.le) (Nat.cast_nonneg N)
  exact Finset.Nonempty.card_pos ⟨i, hmem⟩

/-! ## Measurability helpers (mirrors `BenjaminiHochberg.lean`) -/

/-- The BH count function is measurable in ω. -/
private lemma measurable_bhCount {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ)
    (hmeas : ∀ j, Measurable (p j)) (m : ℕ) :
    Measurable (fun ω => bhCount α p m ω) := by
  simp only [bhCount]
  have heq : (fun ω => (Finset.univ.filter (fun j : Fin N =>
          p j ω ≤ (m : ℝ) * α / (N : ℝ))).card) =
      fun ω => ∑ j : Fin N, if p j ω ≤ (m : ℝ) * α / (N : ℝ) then 1 else 0 := by
    ext ω
    simp only [Finset.sum_boole, Nat.cast_id]
  rw [heq]
  exact Finset.measurable_sum Finset.univ fun j _ =>
    Measurable.ite (measurableSet_le (hmeas j) measurable_const)
      measurable_const measurable_const

/-- `bhKmax α p ω ≤ k` iff every BH count strictly above `k` is below threshold. -/
private lemma bhKmax_le_iff {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) {k : ℕ} :
    bhKmax α p ω ≤ k ↔ ∀ m ∈ Finset.Ioc k N, bhCount α p m ω < m := by
  constructor
  · intro hle m hm
    rw [Finset.mem_Ioc] at hm
    exact bhCount_lt_of_gt_kmax α p ω m (Nat.lt_of_le_of_lt hle hm.1) hm.2
  · intro h
    simp only [bhKmax]
    apply Finset.sup_le
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_range, id] at hm ⊢
    by_contra hgt
    push_neg at hgt
    have hlt := h m (Finset.mem_Ioc.mpr ⟨hgt, Nat.lt_succ_iff.mp hm.1⟩)
    omega

/-- The `bhKmax` function is measurable. -/
private lemma measurable_bhKmax {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ)
    (hmeas : ∀ j, Measurable (p j)) :
    Measurable (fun ω => bhKmax α p ω) := by
  have hmeas_le : ∀ k : ℕ, MeasurableSet {ω | bhKmax α p ω ≤ k} := fun k => by
    have heq : {ω | bhKmax α p ω ≤ k} =
        ⋂ m ∈ (Finset.Ioc k N : Set ℕ), {ω | bhCount α p m ω < m} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter₂, Finset.mem_coe]
      exact bhKmax_le_iff α p ω
    rw [heq]
    exact MeasurableSet.biInter (Finset.countable_toSet _) fun m _ =>
      measurableSet_lt (measurable_bhCount α p hmeas m) measurable_const
  apply measurable_to_countable'
  intro k
  change MeasurableSet {ω | bhKmax α p ω = k}
  rw [show {ω | bhKmax α p ω = k} =
      {ω | bhKmax α p ω ≤ k} ∩ {ω | k ≤ bhKmax α p ω} from by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; exact le_antisymm_iff]
  apply MeasurableSet.inter (hmeas_le k)
  cases k with
  | zero => simp
  | succ k =>
    rw [show {ω | k + 1 ≤ bhKmax α p ω} = ({ω | bhKmax α p ω ≤ k})ᶜ from by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]; omega]
    exact (hmeas_le k).compl

/-- Measurability of the set `{ω | i ∈ bhRejects α p ω}`. -/
private lemma measurableSet_bhRejects_mem {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ)
    (hmeas : ∀ j, Measurable (p j)) (i : Fin N) :
    MeasurableSet {ω | i ∈ bhRejects α p ω} := by
  simp only [bhRejects_eq_filter, Finset.mem_filter, Finset.mem_univ, true_and]
  have h_cast : Measurable (fun ω => (bhKmax α p ω : ℝ)) :=
    measurable_from_top.comp (measurable_bhKmax α p hmeas)
  have h_mul : Measurable (fun ω => (bhKmax α p ω : ℝ) * α) := h_cast.mul_const α
  have h_div : Measurable (fun ω => (bhKmax α p ω : ℝ) * α / (N : ℝ)) := h_mul.div_const N
  exact measurableSet_le (hmeas i) h_div

/-- Measurability of `numRejections (bhRejects α p)` as a function of ω. -/
private lemma measurable_numRejections_bhRejects {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ)
    (hmeas : ∀ j, Measurable (p j)) :
    Measurable (fun ω => numRejections (bhRejects α p) ω) := by
  simp only [numRejections]
  have heq : (fun ω => (bhRejects α p ω).card) =
      fun ω => ∑ j : Fin N, if j ∈ bhRejects α p ω then 1 else 0 := by
    ext ω
    have hfilt : Finset.univ.filter (fun j : Fin N => j ∈ bhRejects α p ω) =
        bhRejects α p ω := by ext j; simp
    simp only [Finset.sum_boole, Nat.cast_id, hfilt]
  rw [heq]
  exact Finset.measurable_sum Finset.univ fun j _ =>
    Measurable.ite (measurableSet_bhRejects_mem α p hmeas j)
      measurable_const measurable_const

/-- The BH per-null summand is measurable. -/
private lemma measurable_bh_summand {N : ℕ} (α : ℝ) (hα : 0 < α)
    (p : Fin N → Ω → ℝ) (hmeas : ∀ j, Measurable (p j)) (i : Fin N) :
    Measurable (fun ω => (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
        max (numRejections (bhRejects α p) ω : ℝ) 1) := by
  apply Measurable.div
  · exact Measurable.ite (measurableSet_bhRejects_mem α p hmeas i)
      measurable_const measurable_const
  · have h_cast : Measurable (fun ω => (numRejections (bhRejects α p) ω : ℝ)) :=
      measurable_from_top.comp (measurable_numRejections_bhRejects α p hmeas)
    exact Measurable.max h_cast measurable_const

/-- The BH per-null summand is pointwise bounded by 1. -/
private lemma bh_summand_le_one {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (i : Fin N) (ω : Ω) :
    ‖(if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
        max (numRejections (bhRejects α p) ω : ℝ) 1‖ ≤ ‖(1 : ℝ)‖ := by
  simp only [norm_one]
  have hd_pos : 0 < max (numRejections (bhRejects α p) ω : ℝ) 1 :=
    lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [Real.norm_of_nonneg (div_nonneg (by split_ifs <;> simp) (le_of_lt hd_pos))]
  apply div_le_one_of_le₀
  · split_ifs <;> simp
  · exact le_of_lt hd_pos

/-- Integrability of the BH per-null summand `ψᵢ / (R ∨ 1)`. -/
private lemma integrable_bh_summand {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Fin N → Ω → ℝ) (hmeas : ∀ j, Measurable (p j)) (i : Fin N) :
    Integrable (fun ω => (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
        max (numRejections (bhRejects α p) ω : ℝ) 1) μ := by
  apply Integrable.mono (integrable_const (1 : ℝ))
  · exact (measurable_bh_summand α hα p hmeas i).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (bh_summand_le_one α p i)

/-! ## Independence helper (mirrors `BenjaminiHochberg.lean`) -/

/-- Point version of `numRejections ∘ bhRejects`: the number of BH rejections as a deterministic
function of a realized p-value vector `x : Fin N → ℝ`. -/
private noncomputable def bhNumRejPt {N : ℕ} (α : ℝ) (x : Fin N → ℝ) : ℕ :=
  let kmax : ℕ := ((Finset.range (N + 1)).filter
    (fun (m : ℕ) => m ≤ (Finset.univ.filter
      (fun j => x j ≤ (m : ℝ) * α / (N : ℝ))).card)).sup id
  (Finset.univ.filter (fun j => x j ≤ (kmax : ℝ) * α / (N : ℝ))).card

/-- The random BH rejection count factors through the realized p-value vector. -/
private lemma bhNumRej_eq_pt {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) :
    numRejections (bhRejects α p) ω = bhNumRejPt α (fun j => p j ω) := rfl

/-- `bhNumRejPt α` is Borel-measurable on `Fin N → ℝ`. -/
private lemma measurable_bhNumRejPt {N : ℕ} (α : ℝ) :
    Measurable (bhNumRejPt α : (Fin N → ℝ) → ℕ) := by
  have h := measurable_numRejections_bhRejects (Ω := Fin N → ℝ) α
    (fun (j : Fin N) (x : Fin N → ℝ) => x j) (fun j => measurable_pi_apply j)
  have heq : (fun x : Fin N → ℝ =>
      numRejections (bhRejects α (fun (j : Fin N) (x : Fin N → ℝ) => x j)) x)
      = bhNumRejPt α := by
    funext x; exact (bhNumRej_eq_pt α (fun (j : Fin N) (x : Fin N → ℝ) => x j) x)
  rwa [heq] at h

/-- The LOO rejection count is independent of `p i` when the p-values are jointly independent. -/
private lemma bh_loo_indep_mul {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Fin N → Ω → ℝ)
    (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p μ)
    (i : Fin N) (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    μ ({ω | p i ω ≤ t} ∩
        {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k}) =
    μ {ω | p i ω ≤ t} *
        μ {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k} := by
  classical
  set Z : Ω → ℕ :=
    fun ω => numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω with hZdef
  have hXY : IndepFun (fun ω (j : ↥({i} : Finset (Fin N))) => p ↑j ω)
                      (fun ω (j : ↥(({i} : Finset (Fin N))ᶜ)) => p ↑j ω) μ :=
    hindep.indepFun_finset {i} (({i} : Finset (Fin N))ᶜ) disjoint_compl_right hmeas
  let recon : (↥(({i} : Finset (Fin N))ᶜ) → ℝ) → (Fin N → ℝ) :=
    fun y j => if h : j ∈ (({i} : Finset (Fin N))ᶜ) then y ⟨j, h⟩ else 0
  have hrecon_meas : Measurable recon :=
    measurable_pi_lambda _ (fun j => by
      by_cases h : j ∈ (({i} : Finset (Fin N))ᶜ)
      · simp only [recon, dif_pos h]; exact measurable_pi_apply _
      · simp only [recon, dif_neg h]; exact measurable_const)
  have hpi_eq : (fun ω => p i ω) =
      (fun v : ↥({i} : Finset (Fin N)) → ℝ => v ⟨i, Finset.mem_singleton_self i⟩) ∘
        (fun ω (j : ↥({i} : Finset (Fin N))) => p ↑j ω) := rfl
  have hZ_eq : Z =
      (fun y => bhNumRejPt α (recon y)) ∘
        (fun ω (j : ↥(({i} : Finset (Fin N))ᶜ)) => p ↑j ω) := by
    funext ω
    simp only [hZdef, Function.comp_apply]
    rw [bhNumRej_eq_pt]
    congr 1
    funext j
    by_cases h : j = i
    · subst h; simp [recon, Function.update_self]
    · have hjc : j ∈ (({i} : Finset (Fin N))ᶜ) := by
        simp only [Finset.mem_compl, Finset.mem_singleton]; exact h
      simp only [Function.update_of_ne h, recon, dif_pos hjc]
  have hpiZ : IndepFun (fun ω => p i ω) Z μ := by
    rw [hpi_eq, hZ_eq]
    exact hXY.comp (measurable_pi_apply _) ((measurable_bhNumRejPt α).comp hrecon_meas)
  have e1 : {ω | p i ω ≤ t} = (fun ω => p i ω) ⁻¹' Set.Iic t := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
  have e2 : {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k} =
      Z ⁻¹' {k} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, hZdef]
  rw [e1, e2]
  exact hpiZ.measure_inter_preimage_eq_mul (Set.Iic t) {k} measurableSet_Iic
    (measurableSet_singleton k)

/-! ## Per-null forward crux (mirrors `BenjaminiHochberg.lean`) -/

/-- `bhKmax α p ω ≤ numRejections (bhRejects α p) ω`. -/
private lemma bhKmax_le_numRej {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) :
    bhKmax α p ω ≤ numRejections (bhRejects α p) ω := by
  rcases Nat.eq_zero_or_pos (bhKmax α p ω) with h | h
  · rw [h]; exact Nat.zero_le _
  · have hcnt : numRejections (bhRejects α p) ω = bhCount α p (bhKmax α p ω) ω := by
      change (bhRejects α p ω).card = bhCount α p (bhKmax α p ω) ω
      rw [bhRejects_eq_filter]; simp only [bhCount]
    rw [hcnt]; exact bhKmax_le_count α p ω h

/-- Forward crux: a rejected null has `pᵢ ≤ R·α/N`. -/
private lemma bh_mem_imp_le {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α) (p : Fin N → Ω → ℝ)
    (i : Fin N) (ω : Ω) (hi : i ∈ bhRejects α p ω) :
    p i ω ≤ (numRejections (bhRejects α p) ω : ℝ) * α / N := by
  rw [bhRejects_eq_filter] at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have hk' : (bhKmax α p ω : ℝ) ≤ (numRejections (bhRejects α p) ω : ℝ) := by
    exact_mod_cast bhKmax_le_numRej α p ω
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hstep : (bhKmax α p ω : ℝ) * α / N ≤ (numRejections (bhRejects α p) ω : ℝ) * α / N := by
    rw [div_le_div_iff₀ hN0 hN0]
    nlinarith [mul_le_mul_of_nonneg_right hk' hα.le, hN0.le]
  linarith [hi, hstep]

/-! ## Pointwise identity (equality upgrade of `bh_summand_le_sum`) -/

/-- Pointwise **identity** (the equality upgrade): the per-null summand `ψᵢ/(R∨1)` equals the
leave-one-out sum `∑_{k=1}^N (1/k)·𝟙(pᵢ ≤ kα/N)·𝟙(R(pᵢ→0) = k)`. The `≤` proof
(`bh_summand_le_sum`) used only the forward `bh_mem_imp_le`; equality additionally needs the
converse `bh_loo_le_imp_mem` (in the not-rejected case, every summand vanishes). -/
private lemma bh_summand_eq_sum {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α)
    (p : Fin N → Ω → ℝ) (i : Fin N) (ω : Ω) :
    (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) / max (numRejections (bhRejects α p) ω : ℝ) 1 =
      ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) *
        ((if p i ω ≤ (k : ℝ) * α / N then (1 : ℝ) else 0) *
         (if numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k then (1 : ℝ)
            else 0)) := by
  by_cases hi : i ∈ bhRejects α p ω
  · -- Rejected: LHS = 1/R, RHS collapses to the single k = R term.
    have hRpos : 0 < numRejections (bhRejects α p) ω := Finset.Nonempty.card_pos ⟨i, hi⟩
    have hR1 : 1 ≤ numRejections (bhRejects α p) ω := hRpos
    have hRN : numRejections (bhRejects α p) ω ≤ N := by
      change (bhRejects α p ω).card ≤ N
      exact (Finset.card_le_univ _).trans_eq (by simp [Fintype.card_fin])
    have h1leR : (1 : ℝ) ≤ (numRejections (bhRejects α p) ω : ℝ) := by exact_mod_cast hR1
    have hpi : p i ω ≤ (numRejections (bhRejects α p) ω : ℝ) * α / N := bh_mem_imp_le hN α hα p i ω hi
    have hRloo : numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω =
        numRejections (bhRejects α p) ω :=
      bh_count_eq_leaveOneOut hN α hα p i (numRejections (bhRejects α p) ω) ω hi rfl
    rw [if_pos hi, max_eq_left h1leR,
      Finset.sum_eq_single (numRejections (bhRejects α p) ω)]
    · rw [if_pos hpi, if_pos hRloo, mul_one, mul_one]
    · intro k _ hk_ne
      have hz : (if numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k
          then (1 : ℝ) else 0) = 0 := by
        rw [hRloo]; exact if_neg (fun h => hk_ne h.symm)
      rw [hz, mul_zero, mul_zero]
    · intro h_not
      exact absurd (Finset.mem_Icc.mpr ⟨hR1, hRN⟩) h_not
  · -- Not rejected: LHS = 0, and every summand vanishes by the converse crux.
    rw [if_neg hi, zero_div]
    refine (Finset.sum_eq_zero ?_).symm
    intro k _
    by_cases hpik : p i ω ≤ (k : ℝ) * α / N
    · by_cases hRk : numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k
      · exact absurd (bh_loo_le_imp_mem hN α hα p i ω (by rw [hRk]; exact hpik)) hi
      · rw [if_neg hRk, mul_zero, mul_zero]
    · rw [if_neg hpik, zero_mul, mul_zero]

/-! ## Per-null contribution identity -/

/-- Per-null contribution **identity** (Candès L7 §7.2, the claim `E[ψᵢ/(R∨1)] = α/N`, equality
form): for a null index `i` with **exactly uniform** p-value, `E[ψᵢ/(R∨1)] = α/N`. The `≤` version
is `bh_claim`; the only change is using the exact-uniform equality `P(pᵢ ≤ kα/N) = kα/N` (and the
pointwise identity / `R(pᵢ→0) ≥ 1`) in place of super-uniformity's inequalities. -/
private theorem bh_claim_eq {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Fin N → Ω → ℝ)
    -- LEAN-ONLY: measurability of each p-value; needed for independence / integration
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: p-values independent; Candès L7 §7.2
    (hindep : iIndepFun p μ)
    (i : Fin N)
    -- USER-INPUT: null marginal exactly uniform on [0,1]; Candès L7 §7.2
    (hi : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p i ω ≤ t} = ENNReal.ofReal t) :
    ∫ ω, (if i ∈ bhRejects α p ω then (1 : ℝ) else 0)
          / max (numRejections (bhRejects α p) ω : ℝ) 1 ∂μ = α / N := by
  classical
  have hmeas' : ∀ j, Measurable ((Function.update p i (0 : Ω → ℝ)) j) := by
    intro j; by_cases h : j = i
    · subst h; rw [Function.update_self]; exact measurable_const
    · rw [Function.update_of_ne h]; exact hmeas j
  have hLOO_meas : Measurable
      (fun ω => numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω) :=
    measurable_numRejections_bhRejects α (Function.update p i (0 : Ω → ℝ)) hmeas'
  -- integrability of each summand (bounded by 1/k ≤ 1).
  have hgint : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => (1 / (k : ℝ)) *
      ((if p i ω ≤ (k : ℝ) * α / N then (1 : ℝ) else 0) *
       (if numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k then (1 : ℝ)
          else 0))) μ := by
    intro k _
    refine Integrable.const_mul ?_ (1 / (k : ℝ))
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · refine (Measurable.mul ?_ ?_).aestronglyMeasurable
      · exact Measurable.ite (measurableSet_le (hmeas i) measurable_const)
          measurable_const measurable_const
      · exact Measurable.ite (hLOO_meas (measurableSet_singleton k))
          measurable_const measurable_const
    · rw [Real.norm_of_nonneg (by apply mul_nonneg <;> (split_ifs <;> norm_num))]
      split_ifs <;> norm_num
  -- per-term identity: ∫ (1/k)·𝟙·𝟙 = (α/N)·μ{R(LOO)=k}.
  have eq_each : ∀ k ∈ Finset.Icc 1 N,
      ∫ ω, (1 / (k : ℝ)) *
        ((if p i ω ≤ (k : ℝ) * α / N then (1 : ℝ) else 0) *
         (if numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k then (1 : ℝ)
            else 0)) ∂μ =
      (α / N) *
        (μ {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k}).toReal := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
    have hNne : (N : ℝ) ≠ 0 := by positivity
    have htk : (0 : ℝ) ≤ (k : ℝ) * α / N :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg k) hα.le) (Nat.cast_nonneg N)
    have hk_le1 : (k : ℝ) * α / N ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hN : (0 : ℝ) < N)]
      have hkNr : (k : ℝ) ≤ N := by exact_mod_cast hkN
      nlinarith [mul_nonneg (sub_nonneg.mpr hkNr) hα.le,
                 mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hα1)]
    have hAmeas : MeasurableSet {ω | p i ω ≤ (k : ℝ) * α / N} :=
      measurableSet_le (hmeas i) measurable_const
    have hBmeas : MeasurableSet
        {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k} :=
      hLOO_meas (measurableSet_singleton k)
    have hprod_eq : (fun ω => (if p i ω ≤ (k : ℝ) * α / N then (1 : ℝ) else 0) *
          (if numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k then (1 : ℝ)
            else 0)) =
        ({ω | p i ω ≤ (k : ℝ) * α / N} ∩
          {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k}).indicator 1 := by
      funext ω
      by_cases hA : p i ω ≤ (k : ℝ) * α / N <;>
        by_cases hB : numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k <;>
        simp [Set.mem_inter_iff, Set.mem_setOf_eq, hA, hB]
    rw [integral_const_mul, hprod_eq, integral_indicator_one (hAmeas.inter hBmeas)]
    have hAeq : (μ {ω | p i ω ≤ (k : ℝ) * α / N}).toReal = (k : ℝ) * α / N := by
      rw [hi ((k : ℝ) * α / N) htk hk_le1, ENNReal.toReal_ofReal htk]
    have hmul : μ.real ({ω | p i ω ≤ (k : ℝ) * α / N} ∩
        {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k}) =
        (μ {ω | p i ω ≤ (k : ℝ) * α / N}).toReal *
        (μ {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k}).toReal := by
      rw [MeasureTheory.measureReal_def,
        bh_loo_indep_mul hN α hα μ p hmeas hindep i ((k : ℝ) * α / N) htk k, ENNReal.toReal_mul]
    rw [hmul, hAeq, ← mul_assoc]
    congr 1
    rw [one_div, show (k : ℝ)⁻¹ * ((k : ℝ) * α / N) = ((k : ℝ)⁻¹ * (k : ℝ)) * (α / N) from by ring,
      inv_mul_cancel₀ hkne, one_mul]
  -- the LOO-count events over k ∈ [1,N] partition the sample space (since 1 ≤ R(LOO) ≤ N).
  have sum1 : ∑ k ∈ Finset.Icc 1 N,
      (μ {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k}).toReal = 1 := by
    have hdisj : (↑(Finset.Icc 1 N) : Set ℕ).PairwiseDisjoint
        (fun k => {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k}) := by
      intro a _ b _ hab
      apply Set.disjoint_left.mpr
      intro ω ha hb
      simp only [Set.mem_setOf_eq] at ha hb
      exact hab (ha.symm.trans hb)
    rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top μ _),
      ← measure_biUnion_finset hdisj (fun k _ => hLOO_meas (measurableSet_singleton k))]
    have hcover : (⋃ k ∈ Finset.Icc 1 N,
        {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k}) = Set.univ := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      refine ⟨numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω, ?_, rfl⟩
      rw [Finset.mem_Icc]
      refine ⟨numRej_loo_ge_one α hα p i ω, ?_⟩
      change (bhRejects α (Function.update p i (0 : Ω → ℝ)) ω).card ≤ N
      exact (Finset.card_le_univ _).trans_eq (by simp [Fintype.card_fin])
    rw [hcover, measure_univ, ENNReal.toReal_one]
  -- assemble.
  calc ∫ ω, (if i ∈ bhRejects α p ω then (1 : ℝ) else 0)
          / max (numRejections (bhRejects α p) ω : ℝ) 1 ∂μ
      = ∫ ω, ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) *
          ((if p i ω ≤ (k : ℝ) * α / N then (1 : ℝ) else 0) *
           (if numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k then (1 : ℝ)
              else 0)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall (fun ω => bh_summand_eq_sum hN α hα p i ω))
    _ = ∑ k ∈ Finset.Icc 1 N, ∫ ω, (1 / (k : ℝ)) *
          ((if p i ω ≤ (k : ℝ) * α / N then (1 : ℝ) else 0) *
           (if numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k then (1 : ℝ)
              else 0)) ∂μ :=
        integral_finset_sum _ hgint
    _ = ∑ k ∈ Finset.Icc 1 N, (α / N) *
          (μ {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k}).toReal :=
        Finset.sum_congr rfl eq_each
    _ = (α / N) * ∑ k ∈ Finset.Icc 1 N,
          (μ {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k}).toReal := by
        rw [Finset.mul_sum]
    _ = (α / N) * 1 := by rw [sum1]
    _ = α / N := mul_one _

/-! ## FDP decomposition (mirrors `BenjaminiHochberg.lean`) -/

/-- Decompose `numFalseRejections` as a sum of indicators over `H₀`. -/
private lemma numFalseRejections_eq_sum {N : ℕ} (α : ℝ) (H₀ : Finset (Fin N))
    (p : Fin N → Ω → ℝ) (ω : Ω) :
    (numFalseRejections H₀ (bhRejects α p) ω : ℝ) =
    ∑ i ∈ H₀, if i ∈ bhRejects α p ω then (1 : ℝ) else 0 := by
  simp only [numFalseRejections]
  have hset : (bhRejects α p ω ∩ H₀) = H₀.filter (fun i => i ∈ bhRejects α p ω) := by
    ext j; simp [Finset.mem_inter, Finset.mem_filter, and_comm]
  rw [hset]
  exact Finset.natCast_card_filter _ H₀

/-- Rewrite `FDP` as a sum of per-null indicators divided by `R ∨ 1`. -/
private lemma fdp_eq_sum_div {N : ℕ} (α : ℝ) (H₀ : Finset (Fin N)) (p : Fin N → Ω → ℝ)
    (ω : Ω) :
    FDP H₀ (bhRejects α p) ω =
    ∑ i ∈ H₀, ((if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
        max (numRejections (bhRejects α p) ω : ℝ) 1) := by
  simp only [FDP]
  rw [numFalseRejections_eq_sum, Finset.sum_div]

end BHMartInternal

/-- **Benjamini–Hochberg FDR exact identity** (Candès, Lecture 7, §7.2, Theorem 2, STAT 300C). With
independent p-values and every null **exactly** uniform, the BH procedure at level `α` has
`FDR = (N₀/N)·α` (`N₀ = |H₀|`). -/
theorem benjamini_hochberg_fdr_eq {N : ℕ} (hN : 0 < N) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin N)) (p : Fin N → Ω → ℝ)
    -- USER-INPUT: each p-value is measurable; Candès L7 §7.2
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: the p-values are jointly independent; Candès L7 §7.2
    (hindep : iIndepFun p μ)
    -- USER-INPUT: every null p-value is exactly uniform on [0,1]; Candès L7 §7.2 (the martingale
    -- proof's equality needs exact uniformity, not just super-uniformity)
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    FDR H₀ (bhRejects α p) μ = (H₀.card : ℝ) / N * α := by
  -- Step 1: Unfold FDR and rewrite FDP as sum of per-null indicators.
  simp only [FDR]
  have hfdp_sum : ∀ ω, FDP H₀ (bhRejects α p) ω =
      ∑ i ∈ H₀, ((if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
          max (numRejections (bhRejects α p) ω : ℝ) 1) :=
    fun ω => BHMartInternal.fdp_eq_sum_div α H₀ p ω
  simp_rw [hfdp_sum]
  -- Step 2: Swap integral and sum.
  rw [integral_finset_sum H₀ (fun i _ => BHMartInternal.integrable_bh_summand hN α hα0 μ p hmeas i)]
  -- Step 3: Each summand equals α/N exactly (bh_claim_eq), then sum.
  have hsum : ∀ i ∈ H₀, ∫ ω, (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
          max (numRejections (bhRejects α p) ω : ℝ) 1 ∂μ = α / N :=
    fun i hi => BHMartInternal.bh_claim_eq hN α hα0 hα1 μ p hmeas hindep i (hnull i hi)
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, nsmul_eq_mul]
  ring

end StatLean.MultipleTesting
