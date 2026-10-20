module
public import StatLean.MultipleTesting.BenjaminiHochberg
public import Mathlib.NumberTheory.Harmonic.Defs

@[expose] public section

/-!
# Benjamini–Hochberg FDR control under arbitrary dependence

The Benjamini–Hochberg procedure (reject the hypotheses indexed by
$\{\, j : p_j \le \hat k\,\alpha/N \,\}$, where
$\hat k = \max\{\, k : \#\{\, j : p_j \le k\alpha/N \,\} \ge k \,\}$) controls the false discovery
rate **without any independence assumption** on the $p$-values, at the cost of a harmonic-number
factor.

**Informal statement.** Let $p_1,\dots,p_N$ be $p$-values with null index set $H_0$ of size
$N_0 = |H_0|$, and suppose every null $p$-value is super-uniform, i.e.
$\mathbb{P}(p_i \le t) \le t$ for all $t \ge 0$ and $i \in H_0$. Assume the $p$-values are otherwise
**arbitrarily dependent** (no independence or PRDS condition). Then the Benjamini–Hochberg procedure
run at level $\alpha$ satisfies
$$\mathrm{FDR} \;\le\; \frac{N_0}{N}\,\alpha\,H_N, \qquad H_N = \sum_{k=1}^{N} \frac1k,$$
where $H_N$ is the $N$-th harmonic number. Consequently, running BH at the deflated level
$\alpha/H_N$ controls FDR at $(N_0/N)\,\alpha \le \alpha$ under arbitrary dependence — the
Benjamini–Yekutieli correction.

The Lean statement (`benjamini_hochberg_dependent_fdr_le`) matches this exactly, with two routine
additions: each $p$-value is assumed measurable (needed to integrate the false-discovery proportion),
and super-uniformity is the explicit hypothesis `SuperUniform (p j) μ` on every null index. The
constant $N_0/N \cdot \alpha \cdot H_N$ is the book constant with no deviation.

**Reference.** E. J. Candès, *STAT 300C: Theory of Statistics*, Lecture Notes, Stanford University,
2023, Lecture 5 §5.5 and Lecture 6 §6.6, Theorem 3 (Benjamini–Yekutieli bound under arbitrary
dependence); cross-referenced with Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland,
2025 (ISBN 978-3-032-03160-0), Chapter 21 (Knock-Off), §21.1 (False Discovery Rate: Dependent
P-Values).

**Proof formalization notes.** *(Benjamini–Yekutieli layer-cake.)* Write
$\mathrm{FDP} = \sum_{i\in H_0} \psi_i/(R\vee 1)$, where $\psi_i$ indicates that null $i$ is rejected
and $R$ is the total number of rejections. For each null $i$, expand
$\psi_i/(R\vee 1) = \sum_{k=1}^{N} (1/k)\,\mathbf{1}(R=k)\,\psi_i$ and use that on $\{R=k\}$ a rejected
$i$ satisfies $p_i \le k\alpha/N$. Reorganizing the double sum into bands
$C_j = \{(j-1)\alpha/N < p_i \le j\alpha/N\}$ and applying Abel summation shows each null contributes
at most $(\alpha/N)\,H_N$, using only super-uniformity $\mathbb{P}(p_i \le k\alpha/N) \le k\alpha/N$.
No factorization is used, hence no independence is needed. Summing over $H_0$ gives
$(N_0/N)\,\alpha\,H_N$.

The combinatorial / measurability infrastructure for the BH rejection set is re-derived `private`ly
here because the corresponding lemmas in `BenjaminiHochberg.lean` are `private` to that module.

**Bibliographic comments.** The arbitrary-dependence bound is due to Y. Benjamini and D. Yekutieli,
"The control of the false discovery rate in multiple testing under dependency," *Annals of
Statistics* **29**(4) (2001), 1165–1188. Their Theorem 1.3 establishes
$\mathrm{FDR} \le (m_0/m)\,q\,\sum_{i=1}^{m} 1/i$ for the linear step-up (BH) procedure under any
joint distribution of the test statistics, and Theorem 1.4 gives the corresponding deflated-level
correction; this is exactly the harmonic-factor result formalized here. The underlying BH procedure
itself originates with Y. Benjamini and Y. Hochberg, "Controlling the false discovery rate: a
practical and powerful approach to multiple testing," *Journal of the Royal Statistical Society,
Series B* **57**(1) (1995), 289–300, where it was proved to control FDR at $(m_0/m)\,q$ under
independence (later extended to PRDS positive dependence by Benjamini–Yekutieli, Theorem 1.2).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## Re-derived `bhRejects` infrastructure (private; mirrors `BenjaminiHochberg.lean`) -/

/-- The BH count: number of p-values at or below `m * α / N`. -/
private noncomputable def bhCountD {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (m : ℕ) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun j => p j ω ≤ (m : ℝ) * α / (N : ℝ))).card

/-- The BH kmax: the maximum `k ≤ N` with `bhCountD ≥ k`. Definitionally the inline `kmax` of
`bhRejects`, so `bhRejects α p ω = filter (· ≤ bhKmaxD·α/N)` holds by `rfl`. -/
private noncomputable def bhKmaxD {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) : ℕ :=
  ((Finset.range (N + 1)).filter (fun m => m ≤ bhCountD α p m ω)).sup id

/-- The BH rejection set expressed via `bhKmaxD`. -/
private lemma bhRejects_eq_filterD {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) :
    bhRejects α p ω = Finset.univ.filter (fun j => p j ω ≤ (bhKmaxD α p ω : ℝ) * α / (N : ℝ)) :=
  rfl

/-- `bhKmaxD` is at most `N`. -/
private lemma bhKmaxD_le {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) :
    bhKmaxD α p ω ≤ N := by
  simp only [bhKmaxD]
  apply Finset.sup_le
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range, id] at hm ⊢
  omega

/-- For `m > bhKmaxD α p ω` with `m ≤ N`, `bhCountD α p m ω < m`. -/
private lemma bhCountD_lt_of_gt_kmax {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω)
    (m : ℕ) (hm : bhKmaxD α p ω < m) (hm' : m ≤ N) :
    bhCountD α p m ω < m := by
  by_contra h
  push_neg at h
  have hmem : m ∈ (Finset.range (N + 1)).filter (fun k => k ≤ bhCountD α p k ω) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hm', h⟩
  have hle : m ≤ ((Finset.range (N + 1)).filter (fun k => k ≤ bhCountD α p k ω)).sup id :=
    Finset.le_sup (f := id) hmem
  simp only [bhKmaxD] at hm
  omega

/-- If `K = bhKmaxD α p ω` and `K ≥ 1`, then `K ≤ bhCountD α p K ω`. -/
private lemma bhKmaxD_le_count {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω)
    (hK : 0 < bhKmaxD α p ω) :
    bhKmaxD α p ω ≤ bhCountD α p (bhKmaxD α p ω) ω := by
  set S := (Finset.range (N + 1)).filter (fun m => m ≤ bhCountD α p m ω)
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    simp [S, bhKmaxD, h, Finset.sup_empty] at hK
  have hmem_S : bhKmaxD α p ω ∈ S := by
    have h := Finset.sup_mem_of_nonempty (f := id) hne
    simp only [Set.image_id, Finset.mem_coe] at h
    exact h
  exact (Finset.mem_filter.mp hmem_S).2

/-- `bhKmaxD α p ω ≤ numRejections (bhRejects α p) ω`. -/
private lemma bhKmaxD_le_numRej {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) :
    bhKmaxD α p ω ≤ numRejections (bhRejects α p) ω := by
  rcases Nat.eq_zero_or_pos (bhKmaxD α p ω) with h | h
  · rw [h]; exact Nat.zero_le _
  · have hcnt : numRejections (bhRejects α p) ω = bhCountD α p (bhKmaxD α p ω) ω := by
      change (bhRejects α p ω).card = bhCountD α p (bhKmaxD α p ω) ω
      rw [bhRejects_eq_filterD]; simp only [bhCountD]
    rw [hcnt]; exact bhKmaxD_le_count α p ω h

/-- Forward (easy) half of the BH crux: a rejected null has `pᵢ ≤ R·α/N`, where `R` is the
rejection count. -/
private lemma bh_mem_imp_leD {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α) (p : Fin N → Ω → ℝ)
    (i : Fin N) (ω : Ω) (hi : i ∈ bhRejects α p ω) :
    p i ω ≤ (numRejections (bhRejects α p) ω : ℝ) * α / N := by
  rw [bhRejects_eq_filterD] at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have hk' : (bhKmaxD α p ω : ℝ) ≤ (numRejections (bhRejects α p) ω : ℝ) := by
    exact_mod_cast bhKmaxD_le_numRej α p ω
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hstep : (bhKmaxD α p ω : ℝ) * α / N ≤ (numRejections (bhRejects α p) ω : ℝ) * α / N := by
    rw [div_le_div_iff₀ hN0 hN0]
    nlinarith [mul_le_mul_of_nonneg_right hk' hα.le, hN0.le]
  linarith [hi, hstep]

/-- The BH count function is measurable in ω. -/
private lemma measurable_bhCountD {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ)
    (hmeas : ∀ j, Measurable (p j)) (m : ℕ) :
    Measurable (fun ω => bhCountD α p m ω) := by
  simp only [bhCountD]
  have heq : (fun ω => (Finset.univ.filter (fun j : Fin N =>
          p j ω ≤ (m : ℝ) * α / (N : ℝ))).card) =
      fun ω => ∑ j : Fin N, if p j ω ≤ (m : ℝ) * α / (N : ℝ) then 1 else 0 := by
    ext ω
    simp only [Finset.sum_boole, Nat.cast_id]
  rw [heq]
  exact Finset.measurable_sum Finset.univ fun j _ =>
    Measurable.ite (measurableSet_le (hmeas j) measurable_const)
      measurable_const measurable_const

/-- `bhKmaxD α p ω ≤ k` iff every BH count strictly above `k` is below threshold. -/
private lemma bhKmaxD_le_iff {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) {k : ℕ} :
    bhKmaxD α p ω ≤ k ↔ ∀ m ∈ Finset.Ioc k N, bhCountD α p m ω < m := by
  constructor
  · intro hle m hm
    rw [Finset.mem_Ioc] at hm
    exact bhCountD_lt_of_gt_kmax α p ω m (Nat.lt_of_le_of_lt hle hm.1) hm.2
  · intro h
    simp only [bhKmaxD]
    apply Finset.sup_le
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_range, id] at hm ⊢
    by_contra hgt
    push_neg at hgt
    have hlt := h m (Finset.mem_Ioc.mpr ⟨hgt, Nat.lt_succ_iff.mp hm.1⟩)
    omega

/-- The `bhKmaxD` function is measurable. -/
private lemma measurable_bhKmaxD {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ)
    (hmeas : ∀ j, Measurable (p j)) :
    Measurable (fun ω => bhKmaxD α p ω) := by
  have hmeas_le : ∀ k : ℕ, MeasurableSet {ω | bhKmaxD α p ω ≤ k} := fun k => by
    have heq : {ω | bhKmaxD α p ω ≤ k} =
        ⋂ m ∈ (Finset.Ioc k N : Set ℕ), {ω | bhCountD α p m ω < m} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter₂, Finset.mem_coe]
      exact bhKmaxD_le_iff α p ω
    rw [heq]
    exact MeasurableSet.biInter (Finset.countable_toSet _) fun m _ =>
      measurableSet_lt (measurable_bhCountD α p hmeas m) measurable_const
  apply measurable_to_countable'
  intro k
  change MeasurableSet {ω | bhKmaxD α p ω = k}
  rw [show {ω | bhKmaxD α p ω = k} =
      {ω | bhKmaxD α p ω ≤ k} ∩ {ω | k ≤ bhKmaxD α p ω} from by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; exact le_antisymm_iff]
  apply MeasurableSet.inter (hmeas_le k)
  cases k with
  | zero => simp
  | succ k =>
    rw [show {ω | k + 1 ≤ bhKmaxD α p ω} = ({ω | bhKmaxD α p ω ≤ k})ᶜ from by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]; omega]
    exact (hmeas_le k).compl

/-- Measurability of the set `{ω | i ∈ bhRejects α p ω}`. -/
private lemma measurableSet_bhRejects_memD {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ)
    (hmeas : ∀ j, Measurable (p j)) (i : Fin N) :
    MeasurableSet {ω | i ∈ bhRejects α p ω} := by
  simp only [bhRejects_eq_filterD, Finset.mem_filter, Finset.mem_univ, true_and]
  have h_cast : Measurable (fun ω => (bhKmaxD α p ω : ℝ)) :=
    measurable_from_top.comp (measurable_bhKmaxD α p hmeas)
  have h_div : Measurable (fun ω => (bhKmaxD α p ω : ℝ) * α / (N : ℝ)) :=
    (h_cast.mul_const α).div_const N
  exact measurableSet_le (hmeas i) h_div

/-- Measurability of `numRejections (bhRejects α p)` as a function of ω. -/
private lemma measurable_numRejections_bhRejectsD {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ)
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
    Measurable.ite (measurableSet_bhRejects_memD α p hmeas j)
      measurable_const measurable_const

/-! ## Abel summation core (the harmonic-number bound) -/

/-- Abel summation / summation-by-parts bound (Candès L5/L6 Thm 3, the step where `Hₙ` appears).
For a "CDF" `F` with `F 0 = 0` and `F j ≤ c·j` (super-uniformity, `c = α/N ≥ 0`),
`∑_{j=1}^N (1/j)(F j − F (j−1)) ≤ c·Hₙ`. Proved by a strengthened induction carrying the boundary
term `F n / n`. -/
private lemma abel_harmonic_bound (c : ℝ) (_hc : 0 ≤ c) (F : ℕ → ℝ)
    (hF0 : F 0 = 0) (hFle : ∀ j, F j ≤ c * j) {N : ℕ} (hN : 0 < N) :
    ∑ j ∈ Finset.Icc 1 N, (1 / (j : ℝ)) * (F j - F (j - 1)) ≤ c * (harmonic N : ℝ) := by
  -- Strengthened claim: ∀ n ≥ 1, gₙ ≤ c·Hₙ − c + F n / n.
  suffices h : ∀ n : ℕ, 1 ≤ n →
      ∑ j ∈ Finset.Icc 1 n, (1 / (j : ℝ)) * (F j - F (j - 1))
        ≤ c * (harmonic n : ℝ) - c + F n / n by
    have hmain := h N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hFN : F N / N ≤ c := by
      rw [div_le_iff₀ hNr]; have := hFle N; linarith [this]
    linarith
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      have hH1 : (harmonic 1 : ℝ) = 1 := by norm_num [harmonic_succ, harmonic_zero]
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, hH1, Nat.sub_self]
      rw [hF0]
      ring_nf
      linarith
  | succ n hn ih =>
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn
      have hn1r : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hFn : F n ≤ c * n := hFle n
      -- expand the top term of the Icc-sum
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hidx : (n + 1) - 1 = n := by omega
      rw [hidx]
      -- harmonic recurrence
      have hrec : (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
        rw [harmonic_succ]; push_cast; ring
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast, hrec]
      -- key per-step inequality: F n / n − F n / (n+1) ≤ c / (n+1)
      have step : F n / (n : ℝ) - F n / ((n : ℝ) + 1) ≤ c / ((n : ℝ) + 1) := by
        have hcollapse : F n / (n : ℝ) - F n / ((n : ℝ) + 1)
            = F n / ((n : ℝ) * ((n : ℝ) + 1)) := by
          field_simp; ring
        rw [hcollapse, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hFn, hnr, hn1r]
      -- split the new term to expose atoms for linarith
      have hsplit : (1 / ((n : ℝ) + 1)) * (F (n + 1) - F n)
          = F (n + 1) / ((n : ℝ) + 1) - F n / ((n : ℝ) + 1) := by ring
      rw [hsplit]
      have hdist : c * ((harmonic n : ℝ) + 1 / ((n : ℝ) + 1))
          = c * (harmonic n : ℝ) + c / ((n : ℝ) + 1) := by ring
      rw [hdist]
      linarith [ih, step]

/-! ## Per-null contribution bound (bands + Abel) -/

/-- A measurable function bounded in absolute value by a constant is integrable on a probability
space. -/
private lemma integrable_of_bdd {C : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {g : Ω → ℝ} (hg : Measurable g) (hC : ∀ ω, |g ω| ≤ C) : Integrable g μ :=
  Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)

/-- Reindex a sum over `Icc 1 N` to a sum over `range N` (`j = m + 1`). -/
private lemma sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, g j = ∑ m ∈ Finset.range N, g (m + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl; intro m _; rw [Nat.add_comm]

/-- Per-null contribution bound under arbitrary dependence (Candès L5/L6 Thm 3): for a null index
`i` with super-uniform p-value, `E[ψᵢ/(R∨1)] ≤ (α/N)·Hₙ`. No independence is used; the harmonic
factor comes from the layer-cake (bands) reorganization and Abel summation. -/
private theorem bh_claim_dependent {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin N → Ω → ℝ)
    -- LEAN-ONLY: measurability of each p-value; needed for integration; no scope change
    (hmeas : ∀ j, Measurable (p j)) (i : Fin N)
    -- USER-INPUT: null marginal super-uniform; Candès L5/L6 Thm 3
    (hi : SuperUniform (p i) μ) :
    ∫ ω, (if i ∈ bhRejects α p ω then (1 : ℝ) else 0)
          / max (numRejections (bhRejects α p) ω : ℝ) 1 ∂μ
      ≤ α / N * (harmonic N : ℝ) := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- abbreviations
  set R : Ω → ℕ := fun ω => numRejections (bhRejects α p) ω with hRdef
  have hRmeas : Measurable R := measurable_numRejections_bhRejectsD α p hmeas
  -- the threshold indicator `a k ω` and the slice indicator `b k ω`
  let a : ℕ → Ω → ℝ := fun k ω => if p i ω ≤ (k : ℝ) * α / N then (1 : ℝ) else 0
  let b : ℕ → Ω → ℝ := fun k ω => if R ω = k then (1 : ℝ) else 0
  -- the "CDF" of the null p-value at the BH thresholds
  set F : ℕ → ℝ := fun k => (μ {ω | p i ω ≤ (k : ℝ) * α / N}).toReal with hFdef
  -- measurability
  have ham : ∀ k, Measurable (a k) := fun k =>
    Measurable.ite (measurableSet_le (hmeas i) measurable_const) measurable_const measurable_const
  have hbm : ∀ k, Measurable (b k) := fun k =>
    Measurable.ite (hRmeas (measurableSet_singleton k)) measurable_const measurable_const
  -- pointwise ranges of a, b ∈ {0,1}
  have ha01 : ∀ k ω, a k ω = 0 ∨ a k ω = 1 := fun k ω => by
    simp only [a]; split_ifs <;> [right; left] <;> rfl
  have hb01 : ∀ k ω, b k ω = 0 ∨ b k ω = 1 := fun k ω => by
    simp only [b]; split_ifs <;> [right; left] <;> rfl
  have ha_nonneg : ∀ k ω, 0 ≤ a k ω := fun k ω => by rcases ha01 k ω with h | h <;> simp [h]
  have hb_nonneg : ∀ k ω, 0 ≤ b k ω := fun k ω => by rcases hb01 k ω with h | h <;> simp [h]
  have ha_le1 : ∀ k ω, a k ω ≤ 1 := fun k ω => by rcases ha01 k ω with h | h <;> simp [h]
  -- monotone in the index: threshold grows with k
  have ha_mono : ∀ m ω, a m ω ≤ a (m + 1) ω := fun m ω => by
    simp only [a]
    by_cases h : p i ω ≤ (m : ℝ) * α / N
    · have hthr : (m : ℝ) * α / N ≤ ((m + 1 : ℕ) : ℝ) * α / N := by
        rw [mul_div_assoc, mul_div_assoc]
        apply mul_le_mul_of_nonneg_right _ (div_nonneg hα.le (Nat.cast_nonneg N))
        push_cast; linarith
      have hthis : p i ω ≤ ((m + 1 : ℕ) : ℝ) * α / N := le_trans h hthr
      rw [if_pos h, if_pos hthis]
    · simp only [if_neg h]; split_ifs <;> norm_num
  -- ∫ a k = F k
  have hintegral_a : ∀ k, ∫ ω, a k ω ∂μ = F k := by
    intro k
    rw [hFdef]
    have hset : (fun ω => a k ω) = Set.indicator {ω | p i ω ≤ (k : ℝ) * α / N} 1 := by
      funext ω; simp only [a, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    rw [hset, integral_indicator_one (measurableSet_le (hmeas i) measurable_const)]
    rfl
  -- integrability building blocks
  have hint_a : ∀ k, Integrable (a k) μ := fun k =>
    integrable_of_bdd (C := 1) (ham k) (fun ω => by rcases ha01 k ω with h | h <;> simp [h])
  have hint_amb : ∀ m k, Integrable (fun ω => a m ω * b k ω) μ := fun m k =>
    integrable_of_bdd (C := 1) ((ham m).mul (hbm k)) (fun ω => by
      rcases ha01 m ω with h | h <;> rcases hb01 k ω with h' | h' <;> simp [h, h'])
  have hdiff01 : ∀ m ω, a (m + 1) ω - a m ω = 0 ∨ a (m + 1) ω - a m ω = 1 := fun m ω => by
    have hmono := ha_mono m ω
    rcases ha01 (m + 1) ω with h | h <;> rcases ha01 m ω with h' | h'
    · left; rw [h, h']; ring
    · rw [h, h'] at hmono; norm_num at hmono
    · right; rw [h, h']; ring
    · left; rw [h, h']; ring
  have hdiff_nonneg : ∀ m ω, 0 ≤ a (m + 1) ω - a m ω := fun m ω => by linarith [ha_mono m ω]
  have hint_diff_b : ∀ m k, Integrable (fun ω => (a (m + 1) ω - a m ω) * b k ω) μ := fun m k =>
    integrable_of_bdd (C := 1) (((ham (m + 1)).sub (ham m)).mul (hbm k)) (fun ω => by
      rcases hdiff01 m ω with h | h <;> rcases hb01 k ω with h' | h' <;> simp [h, h'])
  -- the slice indicators sum to ≤ 1 over any index set
  have hsum_b_le : ∀ (ω : Ω) (s : Finset ℕ), ∑ k ∈ s, b k ω ≤ 1 := by
    intro ω s
    simp only [b]
    rw [Finset.sum_ite_eq s (R ω) (fun _ => (1 : ℝ))]
    split_ifs <;> norm_num
  -- F is a valid CDF for the Abel lemma
  have hF0 : F 0 = 0 := by
    have hμ : μ {ω | p i ω ≤ ((0 : ℕ) : ℝ) * α / N} = 0 := by
      have hle : μ {ω | p i ω ≤ ((0 : ℕ) : ℝ) * α / N}
          ≤ ENNReal.ofReal (((0 : ℕ) : ℝ) * α / N) := hi _ (by positivity)
      have h0 : ENNReal.ofReal (((0 : ℕ) : ℝ) * α / N) = 0 := by
        rw [show (((0 : ℕ) : ℝ) * α / N) = 0 from by norm_num, ENNReal.ofReal_zero]
      rw [h0] at hle
      exact le_antisymm hle (zero_le)
    simp only [hFdef, hμ, ENNReal.toReal_zero]
  have hFle : ∀ k, F k ≤ (α / N) * k := by
    intro k
    have htk : (0 : ℝ) ≤ (k : ℝ) * α / N :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg k) hα.le) (Nat.cast_nonneg N)
    have hsu := hi ((k : ℝ) * α / N) htk
    have hb : F k ≤ (k : ℝ) * α / N := by
      simp only [hFdef]
      calc (μ {ω | p i ω ≤ (k : ℝ) * α / N}).toReal
          ≤ (ENNReal.ofReal ((k : ℝ) * α / N)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hsu
        _ = (k : ℝ) * α / N := ENNReal.toReal_ofReal htk
    have heq : (α / N) * (k : ℝ) = (k : ℝ) * α / N := by ring
    rw [heq]; exact hb
  -- ===== Step A: pointwise domination =====
  have stepA : ∀ ω, (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) / max (R ω : ℝ) 1
      ≤ ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) * (a k ω * b k ω) := by
    intro ω
    have hnn : ∀ k ∈ Finset.Icc 1 N, (0 : ℝ) ≤ (1 / (k : ℝ)) * (a k ω * b k ω) := by
      intro k _
      exact mul_nonneg (by positivity) (mul_nonneg (ha_nonneg k ω) (hb_nonneg k ω))
    by_cases hi' : i ∈ bhRejects α p ω
    · have hRpos : 0 < R ω := Finset.Nonempty.card_pos ⟨i, hi'⟩
      have hR1 : 1 ≤ R ω := hRpos
      have hRN : R ω ≤ N := by
        change (bhRejects α p ω).card ≤ N
        exact (Finset.card_le_univ _).trans_eq (by simp [Fintype.card_fin])
      have h1leR : (1 : ℝ) ≤ (R ω : ℝ) := by exact_mod_cast hR1
      rw [if_pos hi', max_eq_left h1leR]
      have hpi : p i ω ≤ (R ω : ℝ) * α / N := bh_mem_imp_leD hN α hα p i ω hi'
      have hterm : (1 / (R ω : ℝ)) * (a (R ω) ω * b (R ω) ω) = 1 / (R ω : ℝ) := by
        simp only [a, b, if_pos hpi, if_pos rfl, mul_one]
      rw [← hterm]
      exact Finset.single_le_sum hnn (Finset.mem_Icc.mpr ⟨hR1, hRN⟩)
    · rw [if_neg hi', zero_div]
      exact Finset.sum_nonneg hnn
  -- ===== Step B: integrate Step A =====
  have hintegrable_sum : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 N,
      (1 / (k : ℝ)) * (a k ω * b k ω)) μ :=
    integrable_finset_sum _ (fun k _ => (hint_amb k k).const_mul _)
  have hLHS_int : Integrable (fun ω => (if i ∈ bhRejects α p ω then (1 : ℝ) else 0)
      / max (R ω : ℝ) 1) μ := by
    apply integrable_of_bdd (C := 1)
    · exact (Measurable.ite (measurableSet_bhRejects_memD α p hmeas i)
        measurable_const measurable_const).div
          ((measurable_from_top.comp hRmeas).max measurable_const)
    · intro ω
      have hden : (1 : ℝ) ≤ max (R ω : ℝ) 1 := le_max_right _ _
      have hnum0 : 0 ≤ (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      have hnum1 : (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      rw [abs_of_nonneg (div_nonneg hnum0 (by linarith)), div_le_one (by linarith)]
      linarith
  have stepB : ∫ ω, (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) / max (R ω : ℝ) 1 ∂μ
      ≤ ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) * ∫ ω, a k ω * b k ω ∂μ := by
    calc ∫ ω, (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) / max (R ω : ℝ) 1 ∂μ
        ≤ ∫ ω, ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) * (a k ω * b k ω) ∂μ :=
          integral_mono hLHS_int hintegrable_sum stepA
      _ = ∑ k ∈ Finset.Icc 1 N, ∫ ω, (1 / (k : ℝ)) * (a k ω * b k ω) ∂μ :=
          integral_finset_sum _ (fun k _ => (hint_amb k k).const_mul _)
      _ = ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) * ∫ ω, a k ω * b k ω ∂μ := by
          apply Finset.sum_congr rfl; intro k _; rw [integral_const_mul]
  -- ===== Step C: bands swap =====
  set e : ℕ → ℕ → ℝ := fun m k => ∫ ω, (a (m + 1) ω - a m ω) * b k ω ∂μ with he_def
  have he_nonneg : ∀ m k, 0 ≤ e m k := fun m k =>
    integral_nonneg (fun ω => mul_nonneg (hdiff_nonneg m ω) (hb_nonneg k ω))
  -- telescoping decomposition of g k, with the j = 0 band of zero measure dropped
  have hg_telescope : ∀ k, ∫ ω, a k ω * b k ω ∂μ
      = (∫ ω, a 0 ω * b k ω ∂μ) + ∑ m ∈ Finset.range k, e m k := by
    intro k
    have hpt : (fun ω => a k ω * b k ω)
        = fun ω => a 0 ω * b k ω + ∑ m ∈ Finset.range k, (a (m + 1) ω - a m ω) * b k ω := by
      funext ω
      have htel : a k ω = a 0 ω + ∑ m ∈ Finset.range k, (a (m + 1) ω - a m ω) := by
        have := Finset.sum_range_sub (fun m => a m ω) k; linarith [this]
      rw [htel, add_mul, Finset.sum_mul]
    rw [hpt, integral_add (hint_amb 0 k)
        (integrable_finset_sum _ (fun m _ => hint_diff_b m k)),
      integral_finset_sum _ (fun m _ => hint_diff_b m k)]
  -- the j = 0 band has zero measure (F 0 = 0)
  have hz : ∀ k, ∫ ω, a 0 ω * b k ω ∂μ = 0 := by
    intro k
    have hle : ∫ ω, a 0 ω * b k ω ∂μ ≤ ∫ ω, a 0 ω ∂μ := by
      apply integral_mono (hint_amb 0 k) (hint_a 0)
      intro ω; rcases hb01 k ω with h | h <;> simp [h, ha_nonneg 0 ω]
    have hge : 0 ≤ ∫ ω, a 0 ω * b k ω ∂μ :=
      integral_nonneg (fun ω => mul_nonneg (ha_nonneg 0 ω) (hb_nonneg k ω))
    rw [hintegral_a 0, hF0] at hle; linarith
  -- inner bound: ∑_{k ≥ m+1} e m k ≤ F (m+1) − F m
  have he_inner : ∀ m, ∑ k ∈ Finset.Icc (m + 1) N, e m k ≤ F (m + 1) - F m := by
    intro m
    have hrw : ∑ k ∈ Finset.Icc (m + 1) N, e m k
        = ∫ ω, (a (m + 1) ω - a m ω) * ∑ k ∈ Finset.Icc (m + 1) N, b k ω ∂μ := by
      rw [he_def]
      rw [← integral_finset_sum _ (fun k _ => hint_diff_b m k)]
      apply integral_congr_ae; filter_upwards with ω; rw [Finset.mul_sum]
    rw [hrw]
    have hbound_int : Integrable
        (fun ω => (a (m + 1) ω - a m ω) * ∑ k ∈ Finset.Icc (m + 1) N, b k ω) μ := by
      refine integrable_of_bdd (C := 1)
        (((ham (m + 1)).sub (ham m)).mul
          (Finset.measurable_sum _ (fun k _ => hbm k))) (fun ω => ?_)
      have hsbnn : 0 ≤ ∑ k ∈ Finset.Icc (m + 1) N, b k ω :=
        Finset.sum_nonneg (fun k _ => hb_nonneg k ω)
      rw [abs_mul]
      have h1 : |a (m + 1) ω - a m ω| ≤ 1 := by rcases hdiff01 m ω with h | h <;> simp [h]
      have h2 : |∑ k ∈ Finset.Icc (m + 1) N, b k ω| ≤ 1 := by
        rw [abs_of_nonneg hsbnn]; exact hsum_b_le ω _
      calc |a (m + 1) ω - a m ω| * |∑ k ∈ Finset.Icc (m + 1) N, b k ω|
          ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hptbound : ∀ ω, (a (m + 1) ω - a m ω) * ∑ k ∈ Finset.Icc (m + 1) N, b k ω
        ≤ a (m + 1) ω - a m ω := fun ω =>
      mul_le_of_le_one_right (hdiff_nonneg m ω) (hsum_b_le ω _)
    calc ∫ ω, (a (m + 1) ω - a m ω) * ∑ k ∈ Finset.Icc (m + 1) N, b k ω ∂μ
        ≤ ∫ ω, (a (m + 1) ω - a m ω) ∂μ :=
          integral_mono hbound_int ((hint_a (m + 1)).sub (hint_a m)) hptbound
      _ = F (m + 1) - F m := by
          rw [integral_sub (hint_a (m + 1)) (hint_a m), hintegral_a, hintegral_a]
  -- assemble Step C: reorder the double sum and apply the inner bound
  have stepC : ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) * ∫ ω, a k ω * b k ω ∂μ
      ≤ ∑ j ∈ Finset.Icc 1 N, (1 / (j : ℝ)) * (F j - F (j - 1)) := by
    have hrw : ∀ k : ℕ, (1 / (k : ℝ)) * ∫ ω, a k ω * b k ω ∂μ
        = ∑ m ∈ Finset.range k, (1 / (k : ℝ)) * e m k := by
      intro k; rw [hg_telescope k, hz k, zero_add, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun k _ => hrw k),
      Finset.sum_comm' (s' := fun m => Finset.Icc (m + 1) N) (t' := Finset.range N)
        (by intro k m; simp only [Finset.mem_Icc, Finset.mem_range]; omega)]
    calc ∑ m ∈ Finset.range N, ∑ k ∈ Finset.Icc (m + 1) N, (1 / (k : ℝ)) * e m k
        ≤ ∑ m ∈ Finset.range N, (1 / ((m : ℝ) + 1)) * (F (m + 1) - F m) := by
          apply Finset.sum_le_sum; intro m _
          calc ∑ k ∈ Finset.Icc (m + 1) N, (1 / (k : ℝ)) * e m k
              ≤ ∑ k ∈ Finset.Icc (m + 1) N, (1 / ((m : ℝ) + 1)) * e m k := by
                apply Finset.sum_le_sum; intro k hk
                rw [Finset.mem_Icc] at hk
                apply mul_le_mul_of_nonneg_right _ (he_nonneg m k)
                apply one_div_le_one_div_of_le (by positivity)
                have : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk.1
                linarith
            _ = (1 / ((m : ℝ) + 1)) * ∑ k ∈ Finset.Icc (m + 1) N, e m k := by rw [Finset.mul_sum]
            _ ≤ (1 / ((m : ℝ) + 1)) * (F (m + 1) - F m) :=
                mul_le_mul_of_nonneg_left (he_inner m) (by positivity)
      _ = ∑ j ∈ Finset.Icc 1 N, (1 / (j : ℝ)) * (F j - F (j - 1)) := by
          rw [sum_Icc_one_eq_range (fun j => (1 / (j : ℝ)) * (F j - F (j - 1))) N]
          apply Finset.sum_congr rfl; intro m _
          have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
          simp only [Nat.add_sub_cancel, hc]
  -- ===== Step D: Abel summation =====
  have hcnn : (0 : ℝ) ≤ α / N := div_nonneg hα.le (Nat.cast_nonneg N)
  calc ∫ ω, (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) / max (R ω : ℝ) 1 ∂μ
      ≤ ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) * ∫ ω, a k ω * b k ω ∂μ := stepB
    _ ≤ ∑ j ∈ Finset.Icc 1 N, (1 / (j : ℝ)) * (F j - F (j - 1)) := stepC
    _ ≤ α / N * (harmonic N : ℝ) := abel_harmonic_bound (α / N) hcnn F hF0 hFle hN

/-! ## FDP decomposition (re-derived; mirrors `BenjaminiHochberg.lean`) -/

/-- Integrability of the BH per-null summand `ψᵢ / (R ∨ 1)` (bounded by `1`). -/
private lemma integrable_summand_dep {N : ℕ} (α : ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Fin N → Ω → ℝ) (hmeas : ∀ j, Measurable (p j)) (i : Fin N) :
    Integrable (fun ω => (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
        max (numRejections (bhRejects α p) ω : ℝ) 1) μ := by
  apply integrable_of_bdd (C := 1)
  · exact (Measurable.ite (measurableSet_bhRejects_memD α p hmeas i)
      measurable_const measurable_const).div
        ((measurable_from_top.comp (measurable_numRejections_bhRejectsD α p hmeas)).max
          measurable_const)
  · intro ω
    have hden : (1 : ℝ) ≤ max (numRejections (bhRejects α p) ω : ℝ) 1 := le_max_right _ _
    have hnum0 : 0 ≤ (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have hnum1 : (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    rw [abs_of_nonneg (div_nonneg hnum0 (by linarith)), div_le_one (by linarith)]
    linarith

/-- Rewrite `FDP` as a sum of per-null indicators divided by `R ∨ 1`. -/
private lemma fdp_eq_sum_div_dep {N : ℕ} (α : ℝ) (H₀ : Finset (Fin N)) (p : Fin N → Ω → ℝ)
    (ω : Ω) :
    FDP H₀ (bhRejects α p) ω =
    ∑ i ∈ H₀, ((if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
        max (numRejections (bhRejects α p) ω : ℝ) 1) := by
  simp only [FDP, numFalseRejections]
  have hset : (bhRejects α p ω ∩ H₀) = H₀.filter (fun i => i ∈ bhRejects α p ω) := by
    ext j; simp [Finset.mem_inter, Finset.mem_filter, and_comm]
  rw [hset, ← Finset.sum_div, Finset.natCast_card_filter]

/-- **Benjamini–Hochberg FDR control under arbitrary dependence** (Candès, Lecture 5 §5.5 /
Lecture 6 §6.6, Theorem 3, STAT 300C — Benjamini–Yekutieli). With every null p-value super-uniform
and **no independence assumption**, the BH procedure at level `α` has
`FDR ≤ (N₀/N)·α·Hₙ`, `Hₙ` the `N`-th harmonic number, `N₀ = |H₀|`. -/
theorem benjamini_hochberg_dependent_fdr_le {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin N)) (p : Fin N → Ω → ℝ)
    -- USER-INPUT: each p-value is measurable; Candès L5/L6
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: every null p-value is super-uniform; Candès L5/L6 Thm 3.
    -- NOTE: no independence hypothesis — this is the arbitrary-dependence theorem.
    (hnull : ∀ j ∈ H₀, SuperUniform (p j) μ) :
    FDR H₀ (bhRejects α p) μ ≤ (H₀.card : ℝ) / N * α * (harmonic N : ℝ) := by
  simp only [FDR]
  simp_rw [fun ω => fdp_eq_sum_div_dep α H₀ p ω]
  rw [integral_finset_sum H₀ (fun i _ => integrable_summand_dep α μ p hmeas i)]
  calc ∑ i ∈ H₀, ∫ ω, (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
          max (numRejections (bhRejects α p) ω : ℝ) 1 ∂μ
      ≤ ∑ _i ∈ H₀, α / N * (harmonic N : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact bh_claim_dependent hN α hα μ p hmeas i (hnull i hi)
    _ = H₀.card * (α / N * (harmonic N : ℝ)) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = (H₀.card : ℝ) / N * α * (harmonic N : ℝ) := by ring

end StatLean.MultipleTesting
