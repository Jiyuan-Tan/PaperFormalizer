module
public import StatLean.MultipleTesting.Knockoff.Procedure
public import StatLean.MultipleTesting.Knockoff.Defs
public import StatLean.MultipleTesting.Knockoff.Initial
public import StatLean.MultipleTesting.ForMathlib.OptionalStopping
public import StatLean.MultipleTesting.ForMathlib.OrderStatistics
public import StatLean.MultipleTesting.ForMathlib.BinomialRatio
public import StatLean.MultipleTesting.ForMathlib.SymmetricCondExp
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section

/-!
# Knock-off master inequality — the supermartingale core

**Informal statement.** Consider the knock-off filter applied to a design with feature-importance
statistics $W_1, \dots, W_d$, each carrying the anti-symmetry (sign-flip) property of a valid
knock-off score, and let $H_0 \subseteq \{1, \dots, d\}$ be the set of true null coordinates. For a
magnitude threshold $t \ge 0$ write
$$ V_{+}(t) = \#\{ j \in H_0 : W_j \ge t \}, \qquad V_{-}(t) = \#\{ j \in H_0 : W_j \le -t \} $$
for the numbers of nulls above $+t$ and below $-t$. Let $t^{\*}$ be the data-driven threshold chosen
by the procedure (the smallest realised magnitude at which the estimated false discovery proportion
$\widehat{\mathrm{FDP}}$ first drops to or below the target level $\alpha$). Then the ratio of nulls
mistakenly selected to a regularised count of "knock-off decoys" satisfies, in expectation,
$$ \mathbb{E}\!\left[ \frac{V_{+}(t^{\*})}{1 + V_{-}(t^{\*})} \right] \le 1. $$
This is the master inequality at the heart of knock-off false-discovery-rate control: multiplying
through by the target level recovers the FDR bound for the knock-off and knock-off$^{+}$ filters.

In Lean this is `knockoff_ratio_stopped_le_one`. The bound is obtained by exhibiting the ratio,
indexed by the increasing magnitudes of all $d$ coordinates, as a forward supermartingale with
respect to a "count filtration" and applying optional stopping at the bounded stopping time
$t^{\*}$. The constant on the right is exactly $1$ as in the book; no constants are weakened.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 21 (Knock-Off), §21.3, Theorem 21.2 (Knock-Off) — false
discovery rate control via knock-offs. Dual reference: E. J. Candès, *STAT 300C: Theory of
Statistics*, Lecture Notes, Stanford University, 2023, Lecture 11, §11.5 (the sequential
supermartingale argument for FDR control of the knock-off filter).

**Proof formalization notes.**
Strategy (maximizing Mathlib reuse — this file is where the martingale construction lives, so the
process/filtration definitions co-evolve with their proofs):

* Reveal the coordinates in **increasing `|W|`** order over **all `d` magnitudes**; the forward
  process `Yproc n = V₊/(1+V₋)` indexed by the order statistics of `{|W j| : j : Fin d}` is a
  forward supermartingale, with `Yproc 0` = the all-nulls ratio (`knockoff_initial_le`,
  via `Yproc_zero_eq`) and `Yproc d = 0`. Indexing over **all `d`** magnitudes (Candès STAT 300C
  Lecture 11 §11.5) is what aligns the hitting time `tauStar` over `θ` with the procedure's
  threshold `tStar = min{ t ∈ {|W_j|} : FDPhat ≤ α }`, which ranges over *all* magnitudes.
* `𝒢rev = Filtration.natural` of `(magnitudes, revealed non-null signs, null split-counts)`; the
  null counts `V₊, V₋` still count only `H₀`, so at a step crossing a *non-null* coordinate the
  counts are unchanged (trivial step) and at a *null* step the removed null's sign is uniform among
  the remaining (`KnockoffScore.signs_*`), so the ratio decreases in expectation.
* `supermartingale_nat` reduces the supermartingale to the one-step inequality `step_condExp_le`
  (the single high-risk lemma); `tauStar` is a bounded `IsStoppingTime`; the proven
  `supermartingale_integral_stoppedValue_le` gives `E[Y_{t*}] ≤ E[Y₀] ≤ 1`.

The construction (`Yproc`, `𝒢rev`, `tauStar`) and the one-step lemma `step_condExp_le` are authored
here by the prover session, alongside this theorem.

**Bibliographic comments.**
The knock-off filter and this supermartingale-based proof of false-discovery-rate control originate
with R. F. Barber and E. J. Candès, "Controlling the false discovery rate via knockoffs," *The
Annals of Statistics* **43**(5):2055–2085, 2015. The master inequality `E[V₊/(1+V₋)] ≤ 1` is the
engine behind their FDR guarantees (Theorem 1 for the knock-off filter and Theorem 2 for the
knock-off$^{+}$ filter): in that paper it appears as the key supermartingale step bounding the
expected null count at the data-driven threshold, established in the Appendix proof of those
theorems. The pairwise sign-exchangeability of the null statistics $W_j$ under the anti-symmetry
property is what makes the indexed ratio a supermartingale. The reformulation as a forward process
over all $d$ ordered magnitudes, used here, follows Candès's STAT 300C Lecture 11 presentation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

/-! ## 1. Process construction -/

/-- The n-th smallest magnitude among ALL `d` coordinates `{|W j ω| : j : Fin d}`, via `orderStat`
on the absolute-value tuple (0-indexed: `θ W ⟨0,h⟩ ω` = minimum magnitude over all coordinates).
- **USER-INPUT**: `W` determines all `d` magnitudes; Lu-BDA §21.3 (Candès STATS-300C §11.5). -/
noncomputable def θ (W : Fin d → Ω → ℝ) (n : Fin d) (ω : Ω) : ℝ :=
  orderStat (fun (i : Fin d) => |W i ω|) n

/-- `Yproc n ω = V₊(θ_n ω)/(1 + V₋(θ_n ω))`, the V₊/V₋ ratio at the n-th magnitude threshold over
all `d` coordinates. For n = 0, `θ_0 ω` is the smallest magnitude (over **all** coordinates), so
every coordinate — in particular every null — is above threshold and `Yproc 0 = V₊(0)/(1+V₋(0))`
(the initial ratio). For n ≥ d, `Yproc n = 0`.
- **USER-INPUT**: `W`, `H₀` supply the knock-off scores and null set; Lu-BDA §21.3.
- **LEAN-ONLY**: the ℕ-indexed extension with `Yproc n = 0` for n ≥ d pads the process for
  `supermartingale_nat`; the supermartingale property holds on the non-trivial range. -/
noncomputable def Yproc (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ) (ω : Ω) : ℝ :=
  if h : n < d
  then (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) / (1 + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))
  else 0

/-! ## 2. Elementary bounds -/

omit mΩ in
/-- `Yproc n ω ≥ 0`: V₊ ≥ 0 and denominator 1 + V₋ ≥ 1. -/
lemma Yproc_nonneg (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ) (ω : Ω) :
    0 ≤ Yproc W H₀ n ω := by
  unfold Yproc
  split_ifs with h
  · apply div_nonneg
    · exact_mod_cast Nat.zero_le _
    · have : (0 : ℝ) ≤ (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) := by exact_mod_cast Nat.zero_le _
      linarith
  · exact le_refl _

omit mΩ in
/-- `Yproc 0 ω = V₊(0)/(1+V₋(0))`: the threshold `θ 0 ω` = the global minimum magnitude is ≤ |W j ω|
for **all** j (since it is the minimum over all `d` coordinates), so in particular ≤ |W j ω| for
every null j ∈ H₀, and hence V₊/V₋ at threshold θ₀ equals V₊/V₋ at threshold 0.
- **USER-INPUT**: equality of counts at threshold θ₀ vs 0; Lu-BDA §21.3. -/
lemma Yproc_zero_eq (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (ω : Ω) :
    Yproc W H₀ 0 ω = (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) := by
  unfold Yproc
  by_cases h : 0 < d
  · simp only [h, ↓reduceDIte]
    -- Key: θ₀ = global min magnitude ≤ |W j ω| for all j, so Vplus/Vminus agree at θ₀ and 0.
    haveI hNZ : NeZero d := ⟨h.ne'⟩
    have hmin : ∀ j : Fin d, θ W ⟨0, h⟩ ω ≤ |W j ω| := by
      intro j
      let v := fun i : Fin d => |W i ω|
      change orderStat v ⟨0, h⟩ ≤ v j
      calc orderStat v ⟨0, h⟩
          ≤ orderStat v ((Tuple.sort v).symm j) := orderStat_monotone v (Fin.zero_le _)
        _ = v ((Tuple.sort v) ((Tuple.sort v).symm j)) := rfl
        _ = v j := by simp [Equiv.apply_symm_apply]
    have hH₀ : ∀ j ∈ H₀, θ W ⟨0, h⟩ ω ≤ |W j ω| := fun j _ => hmin j
    have hSplus : (Splus W (θ W ⟨0, h⟩ ω) ω) ∩ H₀ = (Splus W 0 ω) ∩ H₀ := by
      ext j
      simp only [Finset.mem_inter, Splus, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨⟨_, hpos⟩, hmem⟩ => ⟨⟨abs_nonneg _, hpos⟩, hmem⟩,
             fun ⟨⟨_, hpos⟩, hmem⟩ => ⟨⟨hH₀ j hmem, hpos⟩, hmem⟩⟩
    have hSminus : (Sminus W (θ W ⟨0, h⟩ ω) ω) ∩ H₀ = (Sminus W 0 ω) ∩ H₀ := by
      ext j
      simp only [Finset.mem_inter, Sminus, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨⟨_, hneg⟩, hmem⟩ => ⟨⟨abs_nonneg _, hneg⟩, hmem⟩,
             fun ⟨⟨_, hneg⟩, hmem⟩ => ⟨⟨hH₀ j hmem, hneg⟩, hmem⟩⟩
    simp only [Vplus, Vminus, hSplus, hSminus]
  · -- d = 0: `Fin d` is empty, so H₀ = ∅ and both sides vanish.
    have hcard : H₀.card ≤ d := by
      calc H₀.card ≤ Finset.univ.card := Finset.card_le_univ H₀
        _ = d := by rw [Finset.card_univ, Fintype.card_fin]
    have hH₀ : H₀ = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hH₀
    simp only [h, ↓reduceDIte]
    simp [Vplus, Vminus]

/-! ## 3. Filtration (𝒢rev) -/

/-- Rank condition: `orderStat v n ≤ a` iff the count of entries of `v` that are `≤ a` is `> n`.
Uses `Tuple.lt_card_le_iff_apply_le_of_monotone` (the sorted-tuple characterization) plus
bijectivity of the sorting permutation `Tuple.sort v`.
- **LEAN-ONLY**: bridges the order-statistic definition to a measurable count formula. -/
private lemma orderStat_le_iff_card_lt {m : ℕ} (v : Fin m → ℝ) (n : Fin m) (a : ℝ) :
    orderStat v n ≤ a ↔ n.val < (Finset.univ.filter (fun k => v k ≤ a)).card := by
  have h_card : (Finset.univ.filter (fun i : Fin m => orderStat v i ≤ a)).card =
                (Finset.univ.filter (fun k : Fin m => v k ≤ a)).card :=
    Finset.card_bij' (fun i _ => Tuple.sort v i) (fun k _ => (Tuple.sort v).symm k)
      (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi)
      (fun k hk => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        simp only [orderStat, Equiv.apply_symm_apply]; exact hk)
      (fun i _ => by simp [Equiv.symm_apply_apply])
      (fun k _ => by simp [Equiv.apply_symm_apply])
  rw [show orderStat v n ≤ a ↔ n < (Finset.univ.filter (fun i => orderStat v i ≤ a)).card from
    (Tuple.lt_card_le_iff_apply_le_of_monotone (Tuple.monotone_sort v)).symm, h_card]

/-- Inner count `j ↦ #{ k : Fin d | |W k| ≤ |W j| }` is measurable. -/
private lemma measurable_innerCount (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (j : Fin d) :
    Measurable (fun ω => ((Finset.univ : Finset (Fin d)).filter
      (fun k => |W k ω| ≤ |W j ω|)).card) := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.measurable_sum _ fun k _ =>
    Measurable.ite (measurableSet_le ((hWmeas _).abs) ((hWmeas j).abs))
      measurable_const measurable_const

/-- `V₊(θ_n)` (the null-positive count at the n-th magnitude threshold) is measurable. -/
private lemma measurable_Vplus_theta (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) (h : n < d) :
    Measurable (fun ω => (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ)) := by
  have hRk : ∀ (j : Fin d) (ω : Ω), θ W ⟨n, h⟩ ω ≤ |W j ω| ↔
      n < ((Finset.univ : Finset (Fin d)).filter
        (fun k => |W k ω| ≤ |W j ω|)).card :=
    fun j ω => orderStat_le_iff_card_lt _ ⟨n, h⟩ _
  have heq : ∀ ω, (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ) =
      ∑ j ∈ H₀, if (n < ((Finset.univ : Finset (Fin d)).filter
            (fun k => |W k ω| ≤ |W j ω|)).card ∧ 0 < W j ω)
          then (1 : ℕ) else 0 := fun ω => by
    have hstep : Vplus W H₀ (θ W ⟨n, h⟩ ω) ω =
        (H₀.filter (fun j => n < ((Finset.univ : Finset (Fin d)).filter
            (fun k => |W k ω| ≤ |W j ω|)).card ∧ 0 < W j ω)).card := by
      unfold Vplus Splus; congr 1; ext j
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨⟨hle, hpos⟩, hmem⟩ => ⟨hmem, (hRk j ω).mp hle, hpos⟩,
             fun ⟨hmem, hrk, hpos⟩ => ⟨⟨(hRk j ω).mpr hrk, hpos⟩, hmem⟩⟩
    rw [hstep]; nth_rw 1 [Finset.card_eq_sum_ones]; rw [Finset.sum_filter]
  simp_rw [heq]
  exact Finset.measurable_sum _ fun j _ =>
    Measurable.ite (MeasurableSet.inter
      (measurableSet_lt measurable_const (measurable_innerCount W H₀ hWmeas j))
      (measurableSet_lt measurable_const (hWmeas j)))
      measurable_const measurable_const

/-- `V₋(θ_n)` (the null-negative count at the n-th magnitude threshold) is measurable. -/
private lemma measurable_Vminus_theta (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) (h : n < d) :
    Measurable (fun ω => (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ)) := by
  have hRk : ∀ (j : Fin d) (ω : Ω), θ W ⟨n, h⟩ ω ≤ |W j ω| ↔
      n < ((Finset.univ : Finset (Fin d)).filter
        (fun k => |W k ω| ≤ |W j ω|)).card :=
    fun j ω => orderStat_le_iff_card_lt _ ⟨n, h⟩ _
  have heq : ∀ ω, (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ) =
      ∑ j ∈ H₀, if (n < ((Finset.univ : Finset (Fin d)).filter
            (fun k => |W k ω| ≤ |W j ω|)).card ∧ W j ω < 0)
          then (1 : ℕ) else 0 := fun ω => by
    have hstep : Vminus W H₀ (θ W ⟨n, h⟩ ω) ω =
        (H₀.filter (fun j => n < ((Finset.univ : Finset (Fin d)).filter
            (fun k => |W k ω| ≤ |W j ω|)).card ∧ W j ω < 0)).card := by
      unfold Vminus Sminus; congr 1; ext j
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨⟨hle, hneg⟩, hmem⟩ => ⟨hmem, (hRk j ω).mp hle, hneg⟩,
             fun ⟨hmem, hrk, hneg⟩ => ⟨⟨(hRk j ω).mpr hrk, hneg⟩, hmem⟩⟩
    rw [hstep]; nth_rw 1 [Finset.card_eq_sum_ones]; rw [Finset.sum_filter]
  simp_rw [heq]
  exact Finset.measurable_sum _ fun j _ =>
    Measurable.ite (MeasurableSet.inter
      (measurableSet_lt measurable_const (measurable_innerCount W H₀ hWmeas j))
      (measurableSet_lt (hWmeas j) measurable_const))
      measurable_const measurable_const

/-- Strong measurability of `Yproc W H₀ n` w.r.t. the ambient sigma-algebra `mΩ`. Proved via
the order-statistic rank condition: `θ_n ≤ |W j|` iff the magnitude rank of `|W j|` among all `d`
coordinates is `> n`, which rewrites `Vplus`/`Vminus` as finite sums of measurable indicators.
- **LEAN-ONLY**: measurability adapter; requires `hWmeas : ∀ j, Measurable (W j)`. -/
private lemma Yproc_stronglyMeasurable (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) :
    StronglyMeasurable (Yproc W H₀ n) := by
  apply Measurable.stronglyMeasurable
  unfold Yproc
  by_cases h : n < d
  · simp only [h, ↓reduceDIte]
    -- Inner count measurability: j ↦ #{k : Fin d | |W k ω| ≤ |W j ω|}
    -- Use simp_rw (rewrites under binders) to convert .card to a sum of indicators,
    -- avoiding universe-polymorphic `cfs` helper that leaks universe variables.
    have hCL : ∀ j : Fin d, Measurable (fun ω =>
        ((Finset.univ : Finset (Fin d)).filter
          (fun k => |W k ω| ≤ |W j ω|)).card) := fun j => by
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.measurable_sum _ fun k _ =>
        Measurable.ite (measurableSet_le ((hWmeas _).abs) ((hWmeas j).abs))
          measurable_const measurable_const
    -- Rank condition: θ_n ω ≤ |W j ω| ↔ n < (inner count for j at ω)
    have hRk : ∀ (j : Fin d) (ω : Ω),
        θ W ⟨n, h⟩ ω ≤ |W j ω| ↔
        n < ((Finset.univ : Finset (Fin d)).filter
          (fun k => |W k ω| ≤ |W j ω|)).card :=
      fun j ω => orderStat_le_iff_card_lt
        (fun k : Fin d => |W k ω|) ⟨n, h⟩ _
    -- Rewrite Vplus/Vminus via rank condition, then prove measurability as outer sum of indicators.
    -- heq converts Vplus/Vminus directly to sum form while preserving the inner count as .card,
    -- so that hCL j (which has .card type) unifies correctly in the final Measurable.ite call.
    -- simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter] would also rewrite inner .card to sum
    -- form, breaking the type match with hCL j — so we bake the conversion into heq instead.
    have hVpMeas : Measurable (fun ω => (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ)) := by
      have heq : ∀ ω, (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ) =
          ∑ j ∈ H₀, if (n < ((Finset.univ : Finset (Fin d)).filter
                (fun k => |W k ω| ≤ |W j ω|)).card ∧
              0 < W j ω) then (1 : ℕ) else 0 := fun ω => by
        have hstep : Vplus W H₀ (θ W ⟨n, h⟩ ω) ω =
            (H₀.filter (fun j => n <
              ((Finset.univ : Finset (Fin d)).filter
                (fun k => |W k ω| ≤ |W j ω|)).card ∧
              0 < W j ω)).card := by
          unfold Vplus Splus; congr 1; ext j
          simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun ⟨⟨hle, hpos⟩, hmem⟩ => ⟨hmem, (hRk j ω).mp hle, hpos⟩,
                 fun ⟨hmem, hrk, hpos⟩ => ⟨⟨(hRk j ω).mpr hrk, hpos⟩, hmem⟩⟩
        -- Convert outer .card to sum; nth_rw 1 avoids rewriting the inner .card in the predicate
        rw [hstep]; nth_rw 1 [Finset.card_eq_sum_ones]; rw [Finset.sum_filter]
      simp_rw [heq]
      exact Finset.measurable_sum _ fun j _ =>
        Measurable.ite (MeasurableSet.inter
          (measurableSet_lt measurable_const (hCL j))
          (measurableSet_lt measurable_const (hWmeas j)))
          measurable_const measurable_const
    have hVmMeas : Measurable (fun ω => (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ)) := by
      have heq : ∀ ω, (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ) =
          ∑ j ∈ H₀, if (n < ((Finset.univ : Finset (Fin d)).filter
                (fun k => |W k ω| ≤ |W j ω|)).card ∧
              W j ω < 0) then (1 : ℕ) else 0 := fun ω => by
        have hstep : Vminus W H₀ (θ W ⟨n, h⟩ ω) ω =
            (H₀.filter (fun j => n <
              ((Finset.univ : Finset (Fin d)).filter
                (fun k => |W k ω| ≤ |W j ω|)).card ∧
              W j ω < 0)).card := by
          unfold Vminus Sminus; congr 1; ext j
          simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun ⟨⟨hle, hneg⟩, hmem⟩ => ⟨hmem, (hRk j ω).mp hle, hneg⟩,
                 fun ⟨hmem, hrk, hneg⟩ => ⟨⟨(hRk j ω).mpr hrk, hneg⟩, hmem⟩⟩
        rw [hstep]; nth_rw 1 [Finset.card_eq_sum_ones]; rw [Finset.sum_filter]
      simp_rw [heq]
      exact Finset.measurable_sum _ fun j _ =>
        Measurable.ite (MeasurableSet.inter
          (measurableSet_lt measurable_const (hCL j))
          (measurableSet_lt (hWmeas j) measurable_const))
          measurable_const measurable_const
    exact (measurable_from_nat.comp hVpMeas).div
      (measurable_const.add (measurable_from_nat.comp hVmMeas))
  · simp only [h, ↓reduceDIte]; exact measurable_const

/-- The data revealed by step `n` of the knock-off filter (the **count filtration** generators,
Lu-BDA §21.3): all magnitudes `|W|`, the non-null signs (`0` padded on nulls), and the null
split-counts `(V₊(θ_n), V₋(θ_n))`. Its natural filtration `𝒢rev` exposes `Yproc n` and `FDPhat(θ_n)`
(both functions of these) while keeping the individual null-sign *assignment* above `θ_n` hidden —
the exchangeability that makes `Yproc` a supermartingale. See `notes/.../construction_audit.md`.
- **USER-INPUT**: `W`, `H₀` determine the revealed data; Lu-BDA §21.3 (Definition 21.1 (Knock-Off Score), condition 3). -/
noncomputable def cproc (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ) (ω : Ω) :
    (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ :=
  (fun j => |W j ω|,
   fun j => if j ∈ H₀ then 0 else sgnReal W j ω,
   (if h : n < d then (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) else 0),
   (if h : n < d then (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) else 0))

lemma measurable_cproc (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) : Measurable (cproc W H₀ n) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_))
  · exact measurable_pi_iff.mpr fun j => (hWmeas j).abs
  · refine measurable_pi_iff.mpr fun j => ?_
    by_cases hj : j ∈ H₀
    · simp only [hj, if_true]; exact measurable_const
    · simp only [hj, if_false]
      exact Measurable.ite (measurableSet_le measurable_const (hWmeas j))
        measurable_const measurable_const
  · by_cases h : n < d
    · simp only [h, ↓reduceDIte]
      exact measurable_from_top.comp (measurable_Vplus_theta W H₀ hWmeas n h)
    · simp only [h, ↓reduceDIte]; exact measurable_const
  · by_cases h : n < d
    · simp only [h, ↓reduceDIte]
      exact measurable_from_top.comp (measurable_Vminus_theta W H₀ hWmeas n h)
    · simp only [h, ↓reduceDIte]; exact measurable_const

/-- The count filtration: the natural filtration of `cproc`. -/
noncomputable def 𝒢rev (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) : Filtration ℕ mΩ :=
  Filtration.natural (cproc W H₀) (fun n => (measurable_cproc W H₀ hWmeas n).stronglyMeasurable)

/-- `Yproc W H₀` is strongly adapted to the count filtration `𝒢rev`: `Yproc n = V₊(θ_n)/(1+V₋(θ_n))`
is a Borel function of `cproc n` (its count components), which is `𝒢rev n`-measurable. -/
lemma Yproc_adapted (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) :
    StronglyAdapted (𝒢rev W H₀ hWmeas) (Yproc W H₀) := by
  intro n
  have hcproc : StronglyMeasurable[𝒢rev W H₀ hWmeas n] (cproc W H₀ n) :=
    Filtration.stronglyAdapted_natural
      (fun n => (measurable_cproc W H₀ hWmeas n).stronglyMeasurable) n
  have hg : Measurable (fun x : (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ =>
      if n < d then x.2.2.1 / (1 + x.2.2.2) else 0) := by
    by_cases h : n < d
    · simp only [h, if_true]
      exact (measurable_fst.comp (measurable_snd.comp measurable_snd)).div
        (measurable_const.add (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    · simp only [h, if_false]; exact measurable_const
  have heq : Yproc W H₀ n = (fun x : (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ =>
      if n < d then x.2.2.1 / (1 + x.2.2.2) else 0) ∘ (cproc W H₀ n) := by
    funext ω
    simp only [Function.comp_apply, Yproc, cproc]
    by_cases h : n < d <;> simp [h]
  rw [heq]
  exact (hg.comp hcproc.measurable).stronglyMeasurable

/-- `Yproc W H₀ n` is μ-integrable: it is bounded in `[0, H₀.card]` and μ is a probability
measure (hence finite), so integrability follows from `integrable_const` + `Integrable.mono'`.
- **LEAN-ONLY**: integrability from the finiteness of μ and the bound H₀.card on Yproc. -/
lemma Yproc_integrable (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    Integrable (Yproc W H₀ n) μ := by
  apply Integrable.mono' (integrable_const (H₀.card : ℝ))
    (Yproc_stronglyMeasurable W H₀ hWmeas n).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_of_nonneg (Yproc_nonneg W H₀ n ω)]
  unfold Yproc
  split_ifs with h
  · have h_vm : (0 : ℝ) ≤ Vminus W H₀ (θ W ⟨n, h⟩ ω) ω := Nat.cast_nonneg _
    rw [div_le_iff₀ (by linarith)]
    have h_vp : (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) ≤ H₀.card := by
      simp only [Vplus]
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    calc (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
        ≤ H₀.card := h_vp
      _ ≤ H₀.card * (1 + Vminus W H₀ (θ W ⟨n, h⟩ ω) ω) :=
            le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
  · exact Nat.cast_nonneg _

/-! ## 4. One-step supermartingale inequality -/

/-- The additive form of the exchangeable-step inequality (`step_ratio_le` rearranged): writing the
post-step ratio as `A/(1+B)` plus the positive/negative sign corrections weighted by the conditional
sign probabilities `A/(A+B)`, `B/(A+B)`, the result does not exceed `A/(1+B)`. Pure ℝ, reduces to
`step_ratio_le`.
- **LEAN-ONLY**: algebraic repackaging of `step_ratio_le` for the conditional-expectation assembly. -/
private lemma step_ratio_le' (a b : ℕ) :
    (a : ℝ) / (1 + b)
      + (a : ℝ) / (a + b) * (((a : ℝ) - 1) / (1 + b) - (a : ℝ) / (1 + b))
      + (b : ℝ) / (a + b) * ((a : ℝ) / b - (a : ℝ) / (1 + b)) ≤ (a : ℝ) / (1 + b) := by
  rcases Nat.eq_zero_or_pos (a + b) with hk | hk
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb; norm_num
  · have hk0 : (a : ℝ) + b ≠ 0 := by
      have : (0 : ℝ) < (a : ℝ) + b := by exact_mod_cast hk
      linarith
    have hsum : (a : ℝ) / (a + b) + (b : ℝ) / (a + b) = 1 := by
      rw [← add_div, div_self hk0]
    have hrw : (a : ℝ) / (1 + b)
        + (a : ℝ) / (a + b) * (((a : ℝ) - 1) / (1 + b) - (a : ℝ) / (1 + b))
        + (b : ℝ) / (a + b) * ((a : ℝ) / b - (a : ℝ) / (1 + b))
        = (a : ℝ) / (a + b) * (((a : ℝ) - 1) / (1 + b)) + (b : ℝ) / (a + b) * ((a : ℝ) / b)
          + (a : ℝ) / (1 + b) * (1 - ((a : ℝ) / (a + b) + (b : ℝ) / (a + b))) := by ring
    rw [hrw, hsum]
    have h0 : (a : ℝ) / (1 + b) * (1 - 1) = 0 := by ring
    rw [h0, add_zero]
    exact step_ratio_le a b

/-- The post-condExp inequality in **coefficient-first** product order (matching the form produced
by pulling the `𝒢rev n`-measurable coefficients out of `μ[·|𝒢rev n]`): same content as
`step_ratio_le'`, with each product written `coeff * prob` instead of `prob * coeff`.
- **LEAN-ONLY**: `mul_comm` repackaging of `step_ratio_le'` for the conditional-expectation assembly. -/
private lemma step_ratio_le'' (a b : ℕ) :
    (a : ℝ) / (1 + b)
      + (((a : ℝ) - 1) / (1 + b) - (a : ℝ) / (1 + b)) * ((a : ℝ) / (a + b))
      + ((a : ℝ) / b - (a : ℝ) / (1 + b)) * ((b : ℝ) / (a + b)) ≤ (a : ℝ) / (1 + b) := by
  have h := step_ratio_le' a b
  have e : (a : ℝ) / (1 + b)
      + (((a : ℝ) - 1) / (1 + b) - (a : ℝ) / (1 + b)) * ((a : ℝ) / (a + b))
      + ((a : ℝ) / b - (a : ℝ) / (1 + b)) * ((b : ℝ) / (a + b))
      = (a : ℝ) / (1 + b)
        + (a : ℝ) / (a + b) * (((a : ℝ) - 1) / (1 + b) - (a : ℝ) / (1 + b))
        + (b : ℝ) / (a + b) * ((a : ℝ) / b - (a : ℝ) / (1 + b)) := by ring
  rw [e]; exact h

/-- The "rank-`n` coordinate": the index achieving the `n`-th magnitude order statistic
`θ_n ω = |W (cIdx ω) ω|` (the coordinate crossed when the threshold rises `θ_n → θ_{n+1}`). -/
private noncomputable def cIdx (W : Fin d → Ω → ℝ) (n : ℕ) (h : n < d) (ω : Ω) : Fin d :=
  Tuple.sort (fun i => |W i ω|) ⟨n, h⟩

omit mΩ in
/-- `θ_n ω` is the magnitude of the rank-`n` coordinate. -/
private lemma cIdx_spec (W : Fin d → Ω → ℝ) (n : ℕ) (h : n < d) (ω : Ω) :
    θ W ⟨n, h⟩ ω = |W (cIdx W n h ω) ω| := rfl

omit mΩ in
/-- An injective tuple has strictly monotone order statistics. -/
private lemma orderStat_strictMono_of_injective {m : ℕ} (v : Fin m → ℝ)
    (hv : Function.Injective v) : StrictMono (orderStat v) :=
  (orderStat_monotone v).strictMono_of_injective (fun a b hab => by
    have hvv : v (Tuple.sort v a) = v (Tuple.sort v b) := hab
    exact (Tuple.sort v).injective (hv hvv))

omit mΩ in
/-- **Threshold step (positives).** Under a.s.-distinct magnitudes, raising the threshold from `θ_n`
to `θ_{n+1}` deletes exactly the rank-`n` coordinate from `S⁺`. -/
private lemma Splus_theta_succ (W : Fin d → Ω → ℝ) (n : ℕ) (h : n < d) (h1 : n + 1 < d)
    (ω : Ω) (hmagω : ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) :
    Splus W (θ W ⟨n + 1, h1⟩ ω) ω = (Splus W (θ W ⟨n, h⟩ ω) ω).erase (cIdx W n h ω) := by
  have hinj : Function.Injective (fun i => |W i ω|) := by
    intro i j hij
    by_contra hne
    exact hmagω i j hne hij
  have hSM : StrictMono (orderStat (fun i => |W i ω|)) :=
    orderStat_strictMono_of_injective _ hinj
  have key : ∀ j : Fin d, θ W ⟨n + 1, h1⟩ ω ≤ |W j ω| ↔
      (θ W ⟨n, h⟩ ω ≤ |W j ω| ∧ j ≠ cIdx W n h ω) := by
    intro j
    have hvj : |W j ω| =
        orderStat (fun i => |W i ω|) ((Tuple.sort (fun i => |W i ω|)).symm j) := by
      simp only [orderStat, Equiv.apply_symm_apply]
    have e1 : θ W ⟨n + 1, h1⟩ ω = orderStat (fun i => |W i ω|) ⟨n + 1, h1⟩ := rfl
    have e2 : θ W ⟨n, h⟩ ω = orderStat (fun i => |W i ω|) ⟨n, h⟩ := rfl
    rw [e1, e2, hvj, hSM.le_iff_le, hSM.le_iff_le]
    have hcn : (j ≠ cIdx W n h ω) ↔
        ((Tuple.sort (fun i => |W i ω|)).symm j ≠ (⟨n, h⟩ : Fin d)) := by
      rw [ne_eq, ne_eq, not_iff_not]
      constructor
      · intro hj; rw [hj]; simp only [cIdx, Equiv.symm_apply_apply]
      · intro hr
        have hcong := congrArg (Tuple.sort (fun i => |W i ω|)) hr
        rw [Equiv.apply_symm_apply] at hcong
        exact hcong
    rw [hcn, Fin.le_def, Fin.le_def, ne_eq, Fin.ext_iff]
    have en1 : (⟨n + 1, h1⟩ : Fin d).val = n + 1 := rfl
    have en : (⟨n, h⟩ : Fin d).val = n := rfl
    rw [en1, en]
    omega
  ext j
  simp only [Splus, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨hle, hpos⟩
    obtain ⟨hle', hne⟩ := (key j).mp hle
    exact ⟨hne, hle', hpos⟩
  · rintro ⟨hne, hle', hpos⟩
    exact ⟨(key j).mpr ⟨hle', hne⟩, hpos⟩

omit mΩ in
/-- **Threshold step (negatives).** Under a.s.-distinct magnitudes, raising the threshold from `θ_n`
to `θ_{n+1}` deletes exactly the rank-`n` coordinate from `S⁻`. -/
private lemma Sminus_theta_succ (W : Fin d → Ω → ℝ) (n : ℕ) (h : n < d) (h1 : n + 1 < d)
    (ω : Ω) (hmagω : ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) :
    Sminus W (θ W ⟨n + 1, h1⟩ ω) ω = (Sminus W (θ W ⟨n, h⟩ ω) ω).erase (cIdx W n h ω) := by
  have hinj : Function.Injective (fun i => |W i ω|) := by
    intro i j hij
    by_contra hne
    exact hmagω i j hne hij
  have hSM : StrictMono (orderStat (fun i => |W i ω|)) :=
    orderStat_strictMono_of_injective _ hinj
  have key : ∀ j : Fin d, θ W ⟨n + 1, h1⟩ ω ≤ |W j ω| ↔
      (θ W ⟨n, h⟩ ω ≤ |W j ω| ∧ j ≠ cIdx W n h ω) := by
    intro j
    have hvj : |W j ω| =
        orderStat (fun i => |W i ω|) ((Tuple.sort (fun i => |W i ω|)).symm j) := by
      simp only [orderStat, Equiv.apply_symm_apply]
    have e1 : θ W ⟨n + 1, h1⟩ ω = orderStat (fun i => |W i ω|) ⟨n + 1, h1⟩ := rfl
    have e2 : θ W ⟨n, h⟩ ω = orderStat (fun i => |W i ω|) ⟨n, h⟩ := rfl
    rw [e1, e2, hvj, hSM.le_iff_le, hSM.le_iff_le]
    have hcn : (j ≠ cIdx W n h ω) ↔
        ((Tuple.sort (fun i => |W i ω|)).symm j ≠ (⟨n, h⟩ : Fin d)) := by
      rw [ne_eq, ne_eq, not_iff_not]
      constructor
      · intro hj; rw [hj]; simp only [cIdx, Equiv.symm_apply_apply]
      · intro hr
        have hcong := congrArg (Tuple.sort (fun i => |W i ω|)) hr
        rw [Equiv.apply_symm_apply] at hcong
        exact hcong
    rw [hcn, Fin.le_def, Fin.le_def, ne_eq, Fin.ext_iff]
    have en1 : (⟨n + 1, h1⟩ : Fin d).val = n + 1 := rfl
    have en : (⟨n, h⟩ : Fin d).val = n := rfl
    rw [en1, en]
    omega
  ext j
  simp only [Sminus, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨hle, hneg⟩
    obtain ⟨hle', hne⟩ := (key j).mp hle
    exact ⟨hne, hle', hneg⟩
  · rintro ⟨hne, hle', hneg⟩
    exact ⟨(key j).mpr ⟨hle', hne⟩, hneg⟩

omit mΩ in
/-- **Deterministic step (counting).** Under a.s.-distinct magnitudes, raising the threshold
`θ_n → θ_{n+1}` deletes exactly the rank-`n` coordinate `cn`. Writing `A = V₊(θ_n)`, `B = V₋(θ_n)`,
`A' = V₊(θ_{n+1})`, `B' = V₋(θ_{n+1})`, the post-step ratio `Yproc (n+1) = A'/(1+B')` equals
`Yproc n = A/(1+B)` plus the positive correction `((A-1)/(1+B) - A/(1+B))·(A-A')` and the negative
correction `(A/B - A/(1+B))·(B-B')`. (`A-A'` and `B-B'` are the `{0,1}` indicators of "`cn` is a
positive/negative null"; the `cn ∉ H₀` and degenerate `W cn = 0` cases give `A'=A`, `B'=B`.) -/
private lemma step_removal_eq (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ)
    (h : n < d) (h1 : n + 1 < d) (ω : Ω)
    (hmagω : ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) :
    Yproc W H₀ (n + 1) ω =
      (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) / (1 + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))
      + (((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) - 1) / (1 + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))
          - (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) / (1 + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)))
        * ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) - (Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ))
      + ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) / (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
          - (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) / (1 + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)))
        * ((Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) - (Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ)) := by
  have hSp : Splus W (θ W ⟨n + 1, h1⟩ ω) ω = (Splus W (θ W ⟨n, h⟩ ω) ω).erase (cIdx W n h ω) :=
    Splus_theta_succ W n h h1 ω hmagω
  have hSm : Sminus W (θ W ⟨n + 1, h1⟩ ω) ω = (Sminus W (θ W ⟨n, h⟩ ω) ω).erase (cIdx W n h ω) :=
    Sminus_theta_succ W n h h1 ω hmagω
  have hVp' : Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω =
      ((Splus W (θ W ⟨n, h⟩ ω) ω ∩ H₀).erase (cIdx W n h ω)).card := by
    unfold Vplus; rw [hSp, Finset.erase_inter]
  have hVm' : Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω =
      ((Sminus W (θ W ⟨n, h⟩ ω) ω ∩ H₀).erase (cIdx W n h ω)).card := by
    unfold Vminus; rw [hSm, Finset.erase_inter]
  have hcn_mag : θ W ⟨n, h⟩ ω = |W (cIdx W n h ω) ω| := cIdx_spec W n h ω
  have hmemSp : cIdx W n h ω ∈ Splus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ ↔
      (cIdx W n h ω ∈ H₀ ∧ 0 < W (cIdx W n h ω) ω) := by
    simp only [Finset.mem_inter, Splus, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hpos⟩, hmem⟩; exact ⟨hmem, hpos⟩
    · rintro ⟨hmem, hpos⟩; exact ⟨⟨le_of_eq hcn_mag, hpos⟩, hmem⟩
  have hmemSm : cIdx W n h ω ∈ Sminus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ ↔
      (cIdx W n h ω ∈ H₀ ∧ W (cIdx W n h ω) ω < 0) := by
    simp only [Finset.mem_inter, Sminus, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hneg⟩, hmem⟩; exact ⟨hmem, hneg⟩
    · rintro ⟨hmem, hneg⟩; exact ⟨⟨le_of_eq hcn_mag, hneg⟩, hmem⟩
  by_cases hP : cIdx W n h ω ∈ H₀ ∧ 0 < W (cIdx W n h ω) ω
  · -- positive null: A' = A - 1, B' = B
    have hmemP : cIdx W n h ω ∈ Splus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ := hmemSp.mpr hP
    have hnotSm : cIdx W n h ω ∉ Sminus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ := by
      rw [hmemSm]; rintro ⟨_, hneg⟩; linarith [hP.2]
    have hA1 : 1 ≤ Vplus W H₀ (θ W ⟨n, h⟩ ω) ω := by
      unfold Vplus; exact Finset.card_pos.mpr ⟨cIdx W n h ω, hmemP⟩
    have hA' : Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω = Vplus W H₀ (θ W ⟨n, h⟩ ω) ω - 1 := by
      rw [hVp']; unfold Vplus; rw [Finset.card_erase_of_mem hmemP]
    have hB' : Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω = Vminus W H₀ (θ W ⟨n, h⟩ ω) ω := by
      rw [hVm']; unfold Vminus; rw [Finset.erase_eq_of_notMem hnotSm]
    unfold Yproc; rw [dif_pos h1, hA', hB', Nat.cast_sub hA1]; push_cast; ring
  · by_cases hM : cIdx W n h ω ∈ H₀ ∧ W (cIdx W n h ω) ω < 0
    · -- negative null: A' = A, B' = B - 1
      have hmemM : cIdx W n h ω ∈ Sminus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ := hmemSm.mpr hM
      have hnotSp : cIdx W n h ω ∉ Splus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ := by
        rw [hmemSp]; rintro ⟨_, hpos⟩; linarith [hM.2]
      have hB1 : 1 ≤ Vminus W H₀ (θ W ⟨n, h⟩ ω) ω := by
        unfold Vminus; exact Finset.card_pos.mpr ⟨cIdx W n h ω, hmemM⟩
      have hA' : Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω = Vplus W H₀ (θ W ⟨n, h⟩ ω) ω := by
        rw [hVp']; unfold Vplus; rw [Finset.erase_eq_of_notMem hnotSp]
      have hB' : Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω = Vminus W H₀ (θ W ⟨n, h⟩ ω) ω - 1 := by
        rw [hVm']; unfold Vminus; rw [Finset.card_erase_of_mem hmemM]
      unfold Yproc; rw [dif_pos h1, hA', hB', Nat.cast_sub hB1]; push_cast; ring
    · -- cn ∉ H₀ or W cn = 0: counts unchanged
      have hnotSp : cIdx W n h ω ∉ Splus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ := by rw [hmemSp]; exact hP
      have hnotSm : cIdx W n h ω ∉ Sminus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ := by rw [hmemSm]; exact hM
      have hA' : Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω = Vplus W H₀ (θ W ⟨n, h⟩ ω) ω := by
        rw [hVp']; unfold Vplus; rw [Finset.erase_eq_of_notMem hnotSp]
      have hB' : Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω = Vminus W H₀ (θ W ⟨n, h⟩ ω) ω := by
        rw [hVm']; unfold Vminus; rw [Finset.erase_eq_of_notMem hnotSm]
      unfold Yproc; rw [dif_pos h1, hA', hB']; ring

/-! ### Helpers for the exchangeable disintegration (`count_condExp`) -/

omit mΩ in
/-- Under a.s.-distinct magnitudes, the rank-`n` coordinate equals `j` iff `j` realises the `n`-th
order statistic, i.e. `θ_n = |W j|`. (`→` always; `←` uses injectivity of `|W·ω|`.)
- **LEAN-ONLY**: order-statistic identification of the crossed coordinate. -/
private lemma cIdx_eq_iff (W : Fin d → Ω → ℝ) (n : ℕ) (h : n < d) (ω : Ω)
    (hmagω : ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) (j : Fin d) :
    cIdx W n h ω = j ↔ θ W ⟨n, h⟩ ω = |W j ω| := by
  constructor
  · rintro rfl; exact cIdx_spec W n h ω
  · intro hj
    have hinj : Function.Injective (fun i => |W i ω|) := fun a b hab => by
      by_contra hne; exact hmagω a b hne hab
    exact hinj (show |W (cIdx W n h ω) ω| = |W j ω| by rw [← cIdx_spec W n h ω, hj])

/-- `m ↦ orderStat m ⟨n,h⟩` is measurable: each sub-level set is a count condition. -/
private lemma measurable_orderStat_eval (n : ℕ) (h : n < d) :
    Measurable (fun m : Fin d → ℝ => orderStat m ⟨n, h⟩) := by
  apply measurable_of_Iic
  intro a
  have hset : (fun m : Fin d → ℝ => orderStat m ⟨n, h⟩) ⁻¹' Set.Iic a
      = {m | n < ((Finset.univ : Finset (Fin d)).filter (fun k => m k ≤ a)).card} := by
    ext m
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    exact orderStat_le_iff_card_lt m ⟨n, h⟩ a
  rw [hset]
  apply measurableSet_lt measurable_const
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.measurable_sum _ fun k _ =>
    Measurable.ite (measurableSet_le (measurable_pi_apply k) measurable_const)
      measurable_const measurable_const

/-- Ambient a.e.-strong-measurability of the rank-`n` selector `𝟙(cIdx = j)`, via the genuinely
measurable magnitude proxy `𝟙(θ_n = |W j|)` (a.e. equal under distinct magnitudes). -/
private lemma aesm_cIdx_indicator (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) (hWmeas : ∀ j, Measurable (W j))
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|)
    (n : ℕ) (h : n < d) (j : Fin d) :
    AEStronglyMeasurable (fun ω => if cIdx W n h ω = j then (1 : ℝ) else 0) μ := by
  have hθmeas : Measurable (fun ω => θ W ⟨n, h⟩ ω) := by
    unfold θ
    exact (measurable_orderStat_eval n h).comp (measurable_pi_iff.mpr fun i => (hWmeas i).abs)
  have hpmeas : Measurable (fun ω => if θ W ⟨n, h⟩ ω = |W j ω| then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq_fun hθmeas (hWmeas j).abs) measurable_const measurable_const
  refine ⟨_, hpmeas.stronglyMeasurable, ?_⟩
  filter_upwards [hmag] with ω hω
  have hiff := cIdx_eq_iff W n h ω hω j
  by_cases hc : cIdx W n h ω = j
  · rw [if_pos hc, if_pos (hiff.mp hc)]
  · rw [if_neg hc, if_neg (fun hh => hc (hiff.mpr hh))]

/-- `𝒢rev n`-a.e.-strong-measurability of `𝟙(cIdx = j)`: the proxy `𝟙(θ_n = |W j|)` factors through
the magnitude component of `cproc n`, hence is `𝒢rev n`-measurable. -/
private lemma aesm'_cIdx_indicator (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) (hW : KnockoffScore W H₀ μ)
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|)
    (n : ℕ) (h : n < d) (j : Fin d) :
    AEStronglyMeasurable[𝒢rev W H₀ hW.meas n]
      (fun ω => if cIdx W n h ω = j then (1 : ℝ) else 0) μ := by
  have hGmeas : Measurable (fun x : (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ =>
      if orderStat x.1 ⟨n, h⟩ = x.1 j then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq_fun ((measurable_orderStat_eval n h).comp measurable_fst)
      ((measurable_pi_apply j).comp measurable_fst)) measurable_const measurable_const
  have hcproc : StronglyMeasurable[𝒢rev W H₀ hW.meas n] (cproc W H₀ n) :=
    Filtration.stronglyAdapted_natural
      (fun k => (measurable_cproc W H₀ hW.meas k).stronglyMeasurable) n
  refine ⟨_, (hGmeas.comp hcproc.measurable).stronglyMeasurable, ?_⟩
  filter_upwards [hmag] with ω hω
  have hiff := cIdx_eq_iff W n h ω hω j
  simp only [Function.comp_apply]
  by_cases hc : cIdx W n h ω = j
  · rw [if_pos hc]; exact (if_pos (hiff.mp hc)).symm
  · rw [if_neg hc]; exact (if_neg (fun hh => hc (hiff.mpr hh))).symm

/-- **Null coordinates are a.s. nonzero.** Derived from the constitutive knock-off fields: the sign
`sgnReal W j` is independent of the magnitude `|W j|` (`signs_indep_outer`) and fair
(`signs_fair`), so `μ{W j = 0} = μ{0 ≤ W j} · μ{W j = 0} = ½ · μ{W j = 0}`, forcing `μ{W j = 0} = 0`.
- **USER-INPUT**: nulls have no atom at `0`; Lu-BDA §21.3 (consequence of Definition 21.1 (Knock-Off Score), condition 3). -/
private lemma null_ne_zero (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ)
    (j : Fin d) (hj : j ∈ H₀) : ∀ᵐ ω ∂μ, W j ω ≠ 0 := by
  have hindep : IndepFun (fun ω => sgnReal W j ω) (fun ω => |W j ω|) μ :=
    hW.signs_indep_outer.comp (measurable_pi_apply (⟨j, hj⟩ : H₀))
      ((measurable_pi_apply j).comp measurable_fst)
  have hkey := hindep.measure_inter_preimage_eq_mul {1} {0}
    (measurableSet_singleton 1) (measurableSet_singleton 0)
  have hpre1 : (fun ω => sgnReal W j ω) ⁻¹' {1} = {ω | 0 ≤ W j ω} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro hs; by_contra hh; rw [sgnReal, if_neg hh] at hs; norm_num at hs
    · intro hh; rw [sgnReal, if_pos hh]
  have hpre0 : (fun ω => |W j ω|) ⁻¹' {0} = {ω | W j ω = 0} := by
    ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, abs_eq_zero]
  have hinter : (fun ω => sgnReal W j ω) ⁻¹' {1} ∩ (fun ω => |W j ω|) ⁻¹' {0}
      = {ω | W j ω = 0} := by
    rw [hpre1, hpre0]; ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun hpair => hpair.2, fun h0 => ⟨le_of_eq h0.symm, h0⟩⟩
  rw [hinter, hpre1, hpre0, hW.signs_fair j hj] at hkey
  have hfin : μ {ω | W j ω = 0} ≠ ⊤ := measure_ne_top μ _
  have htr : (μ {ω | W j ω = 0}).toReal = 0 := by
    have h2 := congrArg ENNReal.toReal hkey
    rw [ENNReal.toReal_mul] at h2
    have hhalf : ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 := by
      rw [ENNReal.toReal_div]; norm_num
    rw [hhalf] at h2
    nlinarith [ENNReal.toReal_nonneg (a := μ {ω | W j ω = 0})]
  have hzero : μ {ω | W j ω = 0} = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp htr |>.resolve_right hfin
  rw [ae_iff]; simp only [not_not]; exact hzero

omit mΩ in
/-- **Positive increment is a sign indicator.** Under a.s.-distinct magnitudes,
`V₊(θ_n) − V₊(θ_{n+1})` is the `{0,1}`-indicator that the crossed coordinate `cIdx` is a positive
null. (`Splus_theta_succ` + `card_erase`.) -/
private lemma dPlus_eq_indicator (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ)
    (h : n < d) (h1 : n + 1 < d) (ω : Ω)
    (hmagω : ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) :
    (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) - (Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ)
      = if (cIdx W n h ω ∈ H₀ ∧ 0 < W (cIdx W n h ω) ω) then (1 : ℝ) else 0 := by
  have hVp' : Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω
      = ((Splus W (θ W ⟨n, h⟩ ω) ω ∩ H₀).erase (cIdx W n h ω)).card := by
    unfold Vplus; rw [Splus_theta_succ W n h h1 ω hmagω, Finset.erase_inter]
  have hcn_mag : θ W ⟨n, h⟩ ω = |W (cIdx W n h ω) ω| := cIdx_spec W n h ω
  have hmemSp : cIdx W n h ω ∈ Splus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ ↔
      (cIdx W n h ω ∈ H₀ ∧ 0 < W (cIdx W n h ω) ω) := by
    simp only [Finset.mem_inter, Splus, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨⟨_, hpos⟩, hmem⟩ => ⟨hmem, hpos⟩,
           fun ⟨hmem, hpos⟩ => ⟨⟨le_of_eq hcn_mag, hpos⟩, hmem⟩⟩
  by_cases hP : cIdx W n h ω ∈ H₀ ∧ 0 < W (cIdx W n h ω) ω
  · have hmemP : cIdx W n h ω ∈ Splus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ := hmemSp.mpr hP
    have hA1 : 1 ≤ Vplus W H₀ (θ W ⟨n, h⟩ ω) ω := by
      unfold Vplus; exact Finset.card_pos.mpr ⟨_, hmemP⟩
    have hA' : Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω = Vplus W H₀ (θ W ⟨n, h⟩ ω) ω - 1 := by
      rw [hVp']; unfold Vplus; rw [Finset.card_erase_of_mem hmemP]
    rw [if_pos hP, hA', Nat.cast_sub hA1]; push_cast; ring
  · have hnotSp : cIdx W n h ω ∉ Splus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ := by rw [hmemSp]; exact hP
    have hA' : Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω = Vplus W H₀ (θ W ⟨n, h⟩ ω) ω := by
      rw [hVp']; unfold Vplus; rw [Finset.erase_eq_of_notMem hnotSp]
    rw [if_neg hP, hA']; ring

omit mΩ in
/-- **Negative increment is a sign indicator.** The `V₋` mirror of `dPlus_eq_indicator`. -/
private lemma dMinus_eq_indicator (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ)
    (h : n < d) (h1 : n + 1 < d) (ω : Ω)
    (hmagω : ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) :
    (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) - (Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ)
      = if (cIdx W n h ω ∈ H₀ ∧ W (cIdx W n h ω) ω < 0) then (1 : ℝ) else 0 := by
  have hVm' : Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω
      = ((Sminus W (θ W ⟨n, h⟩ ω) ω ∩ H₀).erase (cIdx W n h ω)).card := by
    unfold Vminus; rw [Sminus_theta_succ W n h h1 ω hmagω, Finset.erase_inter]
  have hcn_mag : θ W ⟨n, h⟩ ω = |W (cIdx W n h ω) ω| := cIdx_spec W n h ω
  have hmemSm : cIdx W n h ω ∈ Sminus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ ↔
      (cIdx W n h ω ∈ H₀ ∧ W (cIdx W n h ω) ω < 0) := by
    simp only [Finset.mem_inter, Sminus, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨⟨_, hneg⟩, hmem⟩ => ⟨hmem, hneg⟩,
           fun ⟨hmem, hneg⟩ => ⟨⟨le_of_eq hcn_mag, hneg⟩, hmem⟩⟩
  by_cases hM : cIdx W n h ω ∈ H₀ ∧ W (cIdx W n h ω) ω < 0
  · have hmemM : cIdx W n h ω ∈ Sminus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ := hmemSm.mpr hM
    have hB1 : 1 ≤ Vminus W H₀ (θ W ⟨n, h⟩ ω) ω := by
      unfold Vminus; exact Finset.card_pos.mpr ⟨_, hmemM⟩
    have hB' : Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω = Vminus W H₀ (θ W ⟨n, h⟩ ω) ω - 1 := by
      rw [hVm']; unfold Vminus; rw [Finset.card_erase_of_mem hmemM]
    rw [if_pos hM, hB', Nat.cast_sub hB1]; push_cast; ring
  · have hnotSm : cIdx W n h ω ∉ Sminus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ := by rw [hmemSm]; exact hM
    have hB' : Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω = Vminus W H₀ (θ W ⟨n, h⟩ ω) ω := by
      rw [hVm']; unfold Vminus; rw [Finset.erase_eq_of_notMem hnotSm]
    rw [if_neg hM, hB']; ring

/-- Integrability of the `{0,1}`-bounded selector products used in the disintegration. -/
private lemma integrable_sel_mul (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hWmeas : ∀ j, Measurable (W j))
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|)
    (n : ℕ) (h : n < d) (j : Fin d) (g : Ω → ℝ) (hg : Measurable g) (hgb : ∀ ω, |g ω| ≤ 1) :
    Integrable (fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0) * g ω) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    ((aesm_cIdx_indicator W H₀ μ hWmeas hmag n h j).mul hg.aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |if cIdx W n h ω = j then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
  calc |if cIdx W n h ω = j then (1 : ℝ) else 0| * |g ω|
      ≤ 1 * 1 := mul_le_mul h1 (hgb ω) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Integrability of the bare selector `𝟙(cIdx = j)`. -/
private lemma integrable_sel (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hWmeas : ∀ j, Measurable (W j))
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|)
    (n : ℕ) (h : n < d) (j : Fin d) :
    Integrable (fun ω => if cIdx W n h ω = j then (1 : ℝ) else 0) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (aesm_cIdx_indicator W H₀ μ hWmeas hmag n h j) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]; split_ifs <;> norm_num

/-! ### The above-`θ_n` null set `S_n` and the disintegration wiring -/

/-- `S_n = {l ∈ H₀ : θ_n ≤ |W l|}`, the above-`θ_n` null set (a `𝒢rev n`-measurable, magnitude-only
function of `ω`). On `{cIdx = j}` we have `j ∈ S_n`; `A = V₊(θ_n)` is the positive-sign subcount of
`S_n`, and `A + B = |S_n|` a.e. (nulls are nonzero). -/
private noncomputable def aboveNulls (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ)
    (h : n < d) (ω : Ω) : Finset (Fin d) :=
  H₀.filter (fun l => θ W ⟨n, h⟩ ω ≤ |W l ω|)

omit mΩ in
private lemma mem_aboveNulls (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ) (h : n < d)
    (ω : Ω) (l : Fin d) :
    l ∈ aboveNulls W H₀ n h ω ↔ (l ∈ H₀ ∧ θ W ⟨n, h⟩ ω ≤ |W l ω|) := by
  simp [aboveNulls]

omit mΩ in
private lemma aboveNulls_subset (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ) (h : n < d)
    (ω : Ω) : aboveNulls W H₀ n h ω ⊆ H₀ := Finset.filter_subset _ _

omit mΩ in
/-- `V₊(θ_n)` is the positive-sign subcount of `S_n`. -/
private lemma Vplus_eq_aboveNulls_filter (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ)
    (h : n < d) (ω : Ω) :
    Vplus W H₀ (θ W ⟨n, h⟩ ω) ω
      = ((aboveNulls W H₀ n h ω).filter (fun l => 0 < W l ω)).card := by
  unfold Vplus aboveNulls
  congr 1
  ext l
  simp only [Finset.mem_inter, Splus, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

omit mΩ in
/-- `V₋(θ_n)` is the negative-sign subcount of `S_n`. -/
private lemma Vminus_eq_aboveNulls_filter (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ)
    (h : n < d) (ω : Ω) :
    Vminus W H₀ (θ W ⟨n, h⟩ ω) ω
      = ((aboveNulls W H₀ n h ω).filter (fun l => W l ω < 0)).card := by
  unfold Vminus aboveNulls
  congr 1
  ext l
  simp only [Finset.mem_inter, Sminus, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

omit mΩ in
/-- `A + B = |S_n|` whenever every null is nonzero at `ω` (a.e.). -/
private lemma Vplus_add_Vminus_eq_card (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ)
    (h : n < d) (ω : Ω) (hnz : ∀ l ∈ H₀, W l ω ≠ 0) :
    Vplus W H₀ (θ W ⟨n, h⟩ ω) ω + Vminus W H₀ (θ W ⟨n, h⟩ ω) ω
      = (aboveNulls W H₀ n h ω).card := by
  rw [Vplus_eq_aboveNulls_filter, Vminus_eq_aboveNulls_filter]
  have hneg : (aboveNulls W H₀ n h ω).filter (fun l => W l ω < 0)
      = (aboveNulls W H₀ n h ω).filter (fun l => ¬ 0 < W l ω) := by
    apply Finset.filter_congr
    intro l hl
    have hlH : l ∈ H₀ := (mem_aboveNulls W H₀ n h ω l).mp hl |>.1
    have : W l ω ≠ 0 := hnz l hlH
    constructor
    · intro hlt; linarith
    · intro hnlt; exact lt_of_le_of_ne (not_lt.mp hnlt) this
  rw [hneg, Finset.card_filter_add_card_filter_not]

/-! 𝒢rev-measurability of magnitude-only quantities. -/

private lemma gmeas_cproc_fst (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) :
    Measurable[𝒢rev W H₀ hWmeas n] (fun ω => (cproc W H₀ n ω).1) :=
  measurable_fst.comp (Filtration.stronglyAdapted_natural
    (fun k => (measurable_cproc W H₀ hWmeas k).stronglyMeasurable) n).measurable

private lemma gmeas_abs (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) (l : Fin d) :
    Measurable[𝒢rev W H₀ hWmeas n] (fun ω => |W l ω|) := by
  have := (measurable_pi_apply l).comp (gmeas_cproc_fst W H₀ hWmeas n)
  simpa [cproc] using! this

private lemma gmeas_theta (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) (h : n < d) :
    Measurable[𝒢rev W H₀ hWmeas n] (fun ω => θ W ⟨n, h⟩ ω) := by
  have := (measurable_orderStat_eval n h).comp (gmeas_cproc_fst W H₀ hWmeas n)
  simpa [cproc, θ] using! this

private lemma measurableSet'_theta_le (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) (h : n < d) (l : Fin d) :
    MeasurableSet[𝒢rev W H₀ hWmeas n] {ω | θ W ⟨n, h⟩ ω ≤ |W l ω|} :=
  measurableSet_le (gmeas_theta W H₀ hWmeas n h) (gmeas_abs W H₀ hWmeas n l)

private lemma measurableSet'_cev (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) (h : n < d) (j : Fin d) :
    MeasurableSet[𝒢rev W H₀ hWmeas n] {ω | θ W ⟨n, h⟩ ω = |W j ω|} :=
  measurableSet_eq_fun (gmeas_theta W H₀ hWmeas n h) (gmeas_abs W H₀ hWmeas n j)

private lemma measurableSet'_mem_aboveNulls (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) (h : n < d) (l : Fin d) :
    MeasurableSet[𝒢rev W H₀ hWmeas n] {ω | l ∈ aboveNulls W H₀ n h ω} := by
  by_cases hl : l ∈ H₀
  · have hset : {ω | l ∈ aboveNulls W H₀ n h ω} = {ω | θ W ⟨n, h⟩ ω ≤ |W l ω|} := by
      ext ω; rw [Set.mem_setOf_eq, mem_aboveNulls]; simp [hl]
    rw [hset]; exact measurableSet'_theta_le W H₀ hWmeas n h l
  · have hset : {ω | l ∈ aboveNulls W H₀ n h ω} = (∅ : Set Ω) := by
      ext ω; rw [Set.mem_setOf_eq, mem_aboveNulls]; simp [hl]
    rw [hset]; exact @MeasurableSet.empty Ω (𝒢rev W H₀ hWmeas n)

private lemma measurableSet'_aboveNulls_eq (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) (h : n < d) (T : Finset (Fin d)) :
    MeasurableSet[𝒢rev W H₀ hWmeas n] {ω | aboveNulls W H₀ n h ω = T} := by
  have hset : {ω | aboveNulls W H₀ n h ω = T}
      = ⋂ l, {ω | (l ∈ aboveNulls W H₀ n h ω) ↔ (l ∈ T)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff]
  rw [hset]
  apply MeasurableSet.iInter
  intro l
  by_cases hlT : l ∈ T
  · have : {ω | (l ∈ aboveNulls W H₀ n h ω) ↔ (l ∈ T)}
        = {ω | l ∈ aboveNulls W H₀ n h ω} := by
      ext ω; simp [hlT]
    rw [this]; exact measurableSet'_mem_aboveNulls W H₀ hWmeas n h l
  · have : {ω | (l ∈ aboveNulls W H₀ n h ω) ↔ (l ∈ T)}
        = {ω | l ∈ aboveNulls W H₀ n h ω}ᶜ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, hlT, iff_false]
    rw [this]; exact (measurableSet'_mem_aboveNulls W H₀ hWmeas n h l).compl

/-! ### Null-sign Bool vector and outer data (for the exchangeable swap) -/

/-- The `Bool`-valued sign of the null coordinate `m ∈ H₀`: `true ↔ 0 ≤ W m`. The i.i.d.-fair
exchangeable family that the swap acts on. -/
private noncomputable def nsign (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (m : {x // x ∈ H₀}) (ω : Ω) : Bool := if 0 ≤ W (m : Fin d) ω then true else false

omit mΩ in
private lemma nsign_true_iff (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (m : {x // x ∈ H₀}) (ω : Ω) : nsign W H₀ m ω = true ↔ 0 ≤ W (m : Fin d) ω := by
  unfold nsign; split_ifs with h <;> simp [h]

private lemma measurable_nsign (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (m : {x // x ∈ H₀}) : Measurable (nsign W H₀ m) :=
  Measurable.ite (measurableSet_le measurable_const (hWmeas m.val)) measurable_const measurable_const

omit mΩ in
/-- `nsign` factors through `sgnReal`: `nsign m = (· ≥ 1) ∘ sgnReal m`, the bridge that transports
`signs_iIndep`/`signs_indep_outer` (stated for `sgnReal`) to the `Bool` family. -/
private lemma nsign_eq_comp (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (m : {x // x ∈ H₀}) (ω : Ω) :
    nsign W H₀ m ω = (if (1 : ℝ) ≤ sgnReal W (m : Fin d) ω then true else false) := by
  unfold nsign sgnReal
  by_cases h : 0 ≤ W (m : Fin d) ω
  · simp [h]
  · simp only [h, if_false]; norm_num

/-- The outer data the count filtration conditions on: magnitudes together with non-null signs
(padded `0` on the nulls). This is exactly `(cproc · ).1` × `(cproc ·).2.1` and the right component
of `signs_indep_outer`. -/
private noncomputable def outerData (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (ω : Ω) :
    (Fin d → ℝ) × (Fin d → ℝ) :=
  (fun i => |W i ω|, fun i => if i ∈ H₀ then (0 : ℝ) else sgnReal W i ω)

private lemma measurable_outerData (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) : Measurable (outerData W H₀) := by
  refine Measurable.prodMk (measurable_pi_iff.mpr fun i => (hWmeas i).abs)
    (measurable_pi_iff.mpr fun i => ?_)
  by_cases hi : i ∈ H₀
  · simp only [hi, if_true]; exact measurable_const
  · simp only [hi, if_false]
    exact Measurable.ite (measurableSet_le measurable_const (hWmeas i))
      measurable_const measurable_const

private lemma iIndepFun_nsign (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ) :
    iIndepFun (fun (m : {x // x ∈ H₀}) ω => nsign W H₀ m ω) μ := by
  have hcomp := hW.signs_iIndep.comp
    (fun (_ : {x // x ∈ H₀}) (r : ℝ) => if (1 : ℝ) ≤ r then true else false)
    (fun _ => Measurable.ite (measurableSet_le measurable_const measurable_id)
      measurable_const measurable_const)
  have heq : (fun (m : {x // x ∈ H₀}) => (fun r : ℝ => if (1 : ℝ) ≤ r then true else false)
      ∘ (fun ω => sgnReal W (m : Fin d) ω)) = (fun m ω => nsign W H₀ m ω) := by
    funext m ω; simp only [Function.comp_apply]; exact (nsign_eq_comp W H₀ m ω).symm
  rwa [heq] at hcomp

private lemma fair_nsign (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ)
    (m : {x // x ∈ H₀}) : μ {ω | nsign W H₀ m ω = true} = 1 / 2 := by
  have hset : {ω | nsign W H₀ m ω = true} = {ω | 0 ≤ W (m : Fin d) ω} := by
    ext ω; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, nsign_true_iff]
  rw [hset]; exact hW.signs_fair (m : Fin d) m.2

private lemma indep_nsign_outerData (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ) :
    IndepFun (fun ω => (fun m => nsign W H₀ m ω : {x // x ∈ H₀} → Bool)) (outerData W H₀) μ := by
  have hG : Measurable (fun v : {x // x ∈ H₀} → ℝ =>
      (fun m => if (1 : ℝ) ≤ v m then true else false : {x // x ∈ H₀} → Bool)) :=
    measurable_pi_iff.mpr fun m => Measurable.ite
      (measurableSet_le measurable_const (measurable_pi_apply m)) measurable_const measurable_const
  have heq : (fun ω => (fun m => nsign W H₀ m ω : {x // x ∈ H₀} → Bool))
      = (fun v : {x // x ∈ H₀} → ℝ =>
          (fun m => if (1 : ℝ) ≤ v m then true else false : {x // x ∈ H₀} → Bool))
        ∘ (fun ω (j : {x // x ∈ H₀}) => sgnReal W (j : Fin d) ω) := by
    funext ω m; simp only [Function.comp_apply]; exact nsign_eq_comp W H₀ m ω
  rw [heq]
  exact hW.signs_indep_outer.comp hG measurable_id

omit mΩ in
/-- Subtype-vs-`Fin d` count bridge: filtering the null subtype by a predicate on the underlying
`Fin d` index has the same cardinality as filtering `H₀` directly. -/
private lemma card_filter_subtype (H₀ : Finset (Fin d)) (Q : Fin d → Prop) [DecidablePred Q] :
    ((Finset.univ : Finset {x // x ∈ H₀}).filter (fun m => Q m.val)).card
      = (H₀.filter Q).card := by
  rw [← Finset.card_image_of_injective _ Subtype.coe_injective]
  congr 1
  ext x
  constructor
  · intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨m.2, hm.2⟩
  · intro hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_image]
    exact ⟨⟨x, hx.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2⟩, rfl⟩

/-- The reconstruction of the count process `cproc 0..n` from `(outerData, nsign⃗)`: the above-`θ_k`
null set is recovered from the magnitudes (`outerData.1`), and the counts `V₊(θ_k)`, `V₋(θ_k)` are
the `true`/`false` subcounts of the `nsign` vector over it. Off the null set `⋃_{m∈H₀}{W m = 0}` it
agrees with `fun k => cproc k`. -/
private noncomputable def reconCproc (H₀ : Finset (Fin d)) (n : ℕ) (h : n < d)
    (p : ((Fin d → ℝ) × (Fin d → ℝ)) × ({x // x ∈ H₀} → Bool)) :
    Fin (n + 1) → (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ :=
  fun k =>
    (p.1.1, p.1.2,
      (((Finset.univ : Finset {x // x ∈ H₀}).filter
        (fun m => orderStat p.1.1 ⟨k.val, Nat.lt_of_le_of_lt (Nat.lt_succ_iff.mp k.isLt) h⟩
          ≤ p.1.1 m.val ∧ p.2 m = true)).card : ℝ),
      (((Finset.univ : Finset {x // x ∈ H₀}).filter
        (fun m => orderStat p.1.1 ⟨k.val, Nat.lt_of_le_of_lt (Nat.lt_succ_iff.mp k.isLt) h⟩
          ≤ p.1.1 m.val ∧ p.2 m = false)).card : ℝ))

omit mΩ in
private lemma measurable_subcount (H₀ : Finset (Fin d)) (r : Fin d) (target : Bool) :
    Measurable (fun p : ((Fin d → ℝ) × (Fin d → ℝ)) × ({x // x ∈ H₀} → Bool) =>
      (((Finset.univ : Finset {x // x ∈ H₀}).filter
        (fun m => orderStat p.1.1 r ≤ p.1.1 m.val ∧ p.2 m = target)).card : ℝ)) := by
  have heq : (fun p : ((Fin d → ℝ) × (Fin d → ℝ)) × ({x // x ∈ H₀} → Bool) =>
        (((Finset.univ : Finset {x // x ∈ H₀}).filter
          (fun m => orderStat p.1.1 r ≤ p.1.1 m.val ∧ p.2 m = target)).card : ℝ))
      = fun p => ∑ m : {x // x ∈ H₀},
          if (orderStat p.1.1 r ≤ p.1.1 m.val ∧ p.2 m = target) then (1 : ℝ) else 0 := by
    funext p
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [heq]
  refine Finset.measurable_sum _ fun m _ => Measurable.ite (MeasurableSet.inter ?_ ?_)
    measurable_const measurable_const
  · exact measurableSet_le
      ((measurable_orderStat_eval r.val r.isLt).comp (measurable_fst.comp measurable_fst))
      ((measurable_pi_apply m.val).comp (measurable_fst.comp measurable_fst))
  · have hpm : Measurable (fun p : ((Fin d → ℝ) × (Fin d → ℝ)) × ({x // x ∈ H₀} → Bool) => p.2 m) :=
      (measurable_pi_apply m).comp measurable_snd
    exact hpm (measurableSet_singleton target)

omit mΩ in
private lemma measurable_reconCproc (H₀ : Finset (Fin d)) (n : ℕ) (h : n < d) :
    Measurable (reconCproc H₀ n h) := by
  refine measurable_pi_iff.mpr fun k => ?_
  refine Measurable.prodMk (measurable_fst.comp measurable_fst)
    (Measurable.prodMk (measurable_snd.comp measurable_fst) (Measurable.prodMk ?_ ?_))
  · exact measurable_subcount H₀ ⟨k.val, Nat.lt_of_le_of_lt (Nat.lt_succ_iff.mp k.isLt) h⟩ true
  · exact measurable_subcount H₀ ⟨k.val, Nat.lt_of_le_of_lt (Nat.lt_succ_iff.mp k.isLt) h⟩ false

omit mΩ in
/-- Off the null set, the reconstruction is exact:
`reconCproc (outerData, nsign⃗) = fun k => cproc k`. -/
private lemma reconCproc_eq (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ) (h : n < d) (ω : Ω)
    (hω : ∀ m ∈ H₀, W m ω ≠ 0) :
    reconCproc H₀ n h (outerData W H₀ ω, fun m => nsign W H₀ m ω)
      = fun k : Fin (n + 1) => cproc W H₀ k.val ω := by
  funext k
  have hkd : k.val < d := Nat.lt_of_le_of_lt (Nat.lt_succ_iff.mp k.isLt) h
  -- The above-`θ_k` predicate, recovered from `outerData.1 = |W ·|`.
  have hVp : (((Finset.univ : Finset {x // x ∈ H₀}).filter
        (fun m => orderStat (outerData W H₀ ω).1 ⟨k.val, hkd⟩ ≤ (outerData W H₀ ω).1 m.val
          ∧ nsign W H₀ m ω = true)).card : ℝ)
      = (Vplus W H₀ (θ W ⟨k.val, hkd⟩ ω) ω : ℝ) := by
    congr 1
    rw [Vplus_eq_aboveNulls_filter]
    have hcongr : ((Finset.univ : Finset {x // x ∈ H₀}).filter
        (fun m => orderStat (outerData W H₀ ω).1 ⟨k.val, hkd⟩ ≤ (outerData W H₀ ω).1 m.val
          ∧ nsign W H₀ m ω = true))
        = (Finset.univ : Finset {x // x ∈ H₀}).filter
          (fun m => θ W ⟨k.val, hkd⟩ ω ≤ |W m.val ω| ∧ 0 < W m.val ω) := by
      apply Finset.filter_congr
      intro m _
      have h1 : orderStat (outerData W H₀ ω).1 ⟨k.val, hkd⟩ = θ W ⟨k.val, hkd⟩ ω := rfl
      have h2 : (outerData W H₀ ω).1 m.val = |W m.val ω| := rfl
      rw [h1, h2, nsign_true_iff]
      have hne := hω m.val m.2
      constructor
      · rintro ⟨ha, hb⟩; exact ⟨ha, lt_of_le_of_ne hb (Ne.symm hne)⟩
      · rintro ⟨ha, hb⟩; exact ⟨ha, le_of_lt hb⟩
    rw [hcongr, card_filter_subtype H₀ (fun m => θ W ⟨k.val, hkd⟩ ω ≤ |W m ω| ∧ 0 < W m ω)]
    unfold aboveNulls
    rw [Finset.filter_filter]
  have hVm : (((Finset.univ : Finset {x // x ∈ H₀}).filter
        (fun m => orderStat (outerData W H₀ ω).1 ⟨k.val, hkd⟩ ≤ (outerData W H₀ ω).1 m.val
          ∧ nsign W H₀ m ω = false)).card : ℝ)
      = (Vminus W H₀ (θ W ⟨k.val, hkd⟩ ω) ω : ℝ) := by
    congr 1
    rw [Vminus_eq_aboveNulls_filter]
    have hcongr : ((Finset.univ : Finset {x // x ∈ H₀}).filter
        (fun m => orderStat (outerData W H₀ ω).1 ⟨k.val, hkd⟩ ≤ (outerData W H₀ ω).1 m.val
          ∧ nsign W H₀ m ω = false))
        = (Finset.univ : Finset {x // x ∈ H₀}).filter
          (fun m => θ W ⟨k.val, hkd⟩ ω ≤ |W m.val ω| ∧ W m.val ω < 0) := by
      apply Finset.filter_congr
      intro m _
      have h1 : orderStat (outerData W H₀ ω).1 ⟨k.val, hkd⟩ = θ W ⟨k.val, hkd⟩ ω := rfl
      have h2 : (outerData W H₀ ω).1 m.val = |W m.val ω| := rfl
      have hnsf : (nsign W H₀ m ω = false) ↔ W m.val ω < 0 := by
        unfold nsign; split_ifs with hpos
        · simp only [false_iff, not_lt]; exact hpos
        · simp only [not_le] at hpos; simp [hpos]
      rw [h1, h2, hnsf]
    rw [hcongr, card_filter_subtype H₀ (fun m => θ W ⟨k.val, hkd⟩ ω ≤ |W m ω| ∧ W m ω < 0)]
    unfold aboveNulls
    rw [Finset.filter_filter]
  simp only [reconCproc]
  rw [cproc]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
  · simp only; rw [dif_pos hkd]; exact hVp
  · simp only; rw [dif_pos hkd]; exact hVm

/-- A subcount over a `swap i₀ j₀`-stable finset is invariant under precomposing the sample by
`swap i₀ j₀` (relabelling two present coordinates leaves the count unchanged). -/
private lemma subcount_swap {ι : Type*} [DecidableEq ι] (i₀ j₀ : ι) (T : Finset ι)
    (hi : i₀ ∈ T) (hj : j₀ ∈ T) (b : ι → Bool) (target : Bool) :
    (T.filter (fun m => b (Equiv.swap i₀ j₀ m) = target)).card
      = (T.filter (fun m => b m = target)).card := by
  have hstab : ∀ x ∈ T, Equiv.swap i₀ j₀ x ∈ T := by
    intro x hx
    rcases eq_or_ne x i₀ with rfl | hxi
    · rwa [Equiv.swap_apply_left]
    · rcases eq_or_ne x j₀ with rfl | hxj
      · rwa [Equiv.swap_apply_right]
      · rwa [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  refine Finset.card_bij (fun m _ => Equiv.swap i₀ j₀ m) ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hstab m hm.1, hm.2⟩
  · intro a _ a' _ hab; exact (Equiv.swap i₀ j₀).injective hab
  · intro m' hm'
    rw [Finset.mem_filter] at hm'
    refine ⟨Equiv.swap i₀ j₀ m', ?_, Equiv.swap_apply_self _ _ _⟩
    rw [Finset.mem_filter]
    exact ⟨hstab m' hm'.1, by rw [Equiv.swap_apply_self]; exact hm'.2⟩

omit mΩ in
/-- The reconstruction is invariant under transposing the signs of two nulls `l, j` both above
`θ_n` (hence above `θ_k` for all `k ≤ n` by `orderStat` monotonicity): each count sees `l, j`
symmetrically, so `reconCproc (z, b ∘ swap l j) = reconCproc (z, b)`. -/
private lemma reconCproc_swap (H₀ : Finset (Fin d)) (n : ℕ) (h : n < d)
    (l j : Fin d) (hl : l ∈ H₀) (hj : j ∈ H₀)
    (z : (Fin d → ℝ) × (Fin d → ℝ)) (b : {x // x ∈ H₀} → Bool)
    (hz : orderStat z.1 ⟨n, h⟩ ≤ z.1 l ∧ orderStat z.1 ⟨n, h⟩ ≤ z.1 j) :
    reconCproc H₀ n h (z, b ∘ Equiv.swap (⟨l, hl⟩ : {x // x ∈ H₀}) ⟨j, hj⟩)
      = reconCproc H₀ n h (z, b) := by
  funext k
  have hkle : k.val ≤ n := Nat.lt_succ_iff.mp k.isLt
  have hmono : orderStat z.1 (⟨k.val, Nat.lt_of_le_of_lt hkle h⟩ : Fin d)
      ≤ orderStat z.1 ⟨n, h⟩ := by
    apply orderStat_monotone; simp only [Fin.le_def]; exact hkle
  have hiT : (⟨l, hl⟩ : {x // x ∈ H₀}) ∈ (Finset.univ : Finset {x // x ∈ H₀}).filter
      (fun m => orderStat z.1 (⟨k.val, Nat.lt_of_le_of_lt hkle h⟩ : Fin d) ≤ z.1 m.val) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans hmono hz.1⟩
  have hjT : (⟨j, hj⟩ : {x // x ∈ H₀}) ∈ (Finset.univ : Finset {x // x ∈ H₀}).filter
      (fun m => orderStat z.1 (⟨k.val, Nat.lt_of_le_of_lt hkle h⟩ : Fin d) ≤ z.1 m.val) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans hmono hz.2⟩
  simp only [reconCproc, Prod.mk.injEq]
  refine ⟨trivial, trivial, ?_, ?_⟩
  · congr 1
    rw [← Finset.filter_filter, ← Finset.filter_filter]
    exact subcount_swap _ _ _ hiT hjT b true
  · congr 1
    rw [← Finset.filter_filter, ← Finset.filter_filter]
    exact subcount_swap _ _ _ hiT hjT b false

/-- **Extraction (the assembled measure-theoretic core).** A `𝒢rev n`-measurable event `F`
on which the two nulls `l, j` are above `θ_n` is, modulo a null set, the pre-image under
`(outerData, nsign⃗)` of a measurable `C` invariant under transposing the sign coordinates `l, j`.

Reason: `𝒢rev n = ⨆_{k ≤ n} σ(cproc k)`, and each `cproc k` is — off the null set
`⋃_{m ∈ H₀} {W m = 0}` — a measurable function of `(outerData, nsign⃗)` (the counts `V₊(θ_k)`,
`V₋(θ_k)` are the `nsign`-subcounts of the magnitude-determined above-`θ_k` null set,
`reconCproc`). Folding in the `𝒢rev`-measurable constraint `l, j ∈ S_n` (true on `F`) makes `C`
invariant under the `l ↔ j` sign transposition, because `l, j` are then above `θ_k` for every
`k ≤ n` (θ monotone), so swapping their signs preserves every count.
- **USER-INPUT**: exchangeability of the i.i.d. fair null signs; Lu-BDA §21.3. -/
private lemma grev_event_outer_invariant (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ)
    (n : ℕ) (h : n < d) (l j : Fin d) (hl : l ∈ H₀) (hj : j ∈ H₀)
    (F : Set Ω) (hF : MeasurableSet[𝒢rev W H₀ hW.meas n] F)
    (hFl : F ⊆ {ω | l ∈ aboveNulls W H₀ n h ω})
    (hFj : F ⊆ {ω | j ∈ aboveNulls W H₀ n h ω}) :
    ∃ C : Set (((Fin d → ℝ) × (Fin d → ℝ)) × ({x // x ∈ H₀} → Bool)), MeasurableSet C ∧
      (∀ z b, (z, b) ∈ C ↔ (z, b ∘ Equiv.swap (⟨l, hl⟩ : {x // x ∈ H₀}) ⟨j, hj⟩) ∈ C) ∧
      F =ᵐ[μ] (fun ω => (outerData W H₀ ω, fun m => nsign W H₀ m ω)) ⁻¹' C := by
  classical
  -- bundle the count process over `k ≤ n`
  set cprocLE : Ω → (Fin (n + 1) → (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ) :=
    fun ω k => cproc W H₀ k.val ω with hcprocLE
  -- Step 1: `𝒢rev n ≤ comap cprocLE`, so `F` is a pre-image of a measurable `B`.
  have hle : (𝒢rev W H₀ hW.meas) n ≤ MeasurableSpace.comap cprocLE inferInstance := by
    have hgrev : (𝒢rev W H₀ hW.meas) n
        = ⨆ k, ⨆ (_ : k ≤ n), MeasurableSpace.comap (cproc W H₀ k) inferInstance := rfl
    rw [hgrev]
    refine iSup₂_le fun m hm => ?_
    have hcl : Measurable[MeasurableSpace.comap cprocLE inferInstance] cprocLE :=
      measurable_iff_comap_le.mpr le_rfl
    exact measurable_iff_comap_le.mp
      ((measurable_pi_apply (⟨m, Nat.lt_succ_of_le hm⟩ : Fin (n + 1))).comp hcl)
  obtain ⟨B, hBmeas, hBpre⟩ := hle F hF
  -- Step 2: off the null set `N`, `cprocLE = reconCproc ∘ M`.
  have hN : ∀ᵐ ω ∂μ, ∀ m ∈ H₀, W m ω ≠ 0 :=
    (ae_ball_iff H₀.countable_toSet).mpr (fun m hm => null_ne_zero W H₀ μ hW m hm)
  set M : Ω → ((Fin d → ℝ) × (Fin d → ℝ)) × ({x // x ∈ H₀} → Bool) :=
    fun ω => (outerData W H₀ ω, fun m => nsign W H₀ m ω) with hM
  -- the `z`-only above-`θ_n` constraint
  have hC₀meas : MeasurableSet {p : ((Fin d → ℝ) × (Fin d → ℝ)) × ({x // x ∈ H₀} → Bool) |
      orderStat p.1.1 ⟨n, h⟩ ≤ p.1.1 l ∧ orderStat p.1.1 ⟨n, h⟩ ≤ p.1.1 j} := by
    apply MeasurableSet.inter
    · exact measurableSet_le
        ((measurable_orderStat_eval n h).comp (measurable_fst.comp measurable_fst))
        ((measurable_pi_apply l).comp (measurable_fst.comp measurable_fst))
    · exact measurableSet_le
        ((measurable_orderStat_eval n h).comp (measurable_fst.comp measurable_fst))
        ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
  refine ⟨reconCproc H₀ n h ⁻¹' B ∩ {p | orderStat p.1.1 ⟨n, h⟩ ≤ p.1.1 l
      ∧ orderStat p.1.1 ⟨n, h⟩ ≤ p.1.1 j},
    (measurable_reconCproc H₀ n h hBmeas).inter hC₀meas, ?_, ?_⟩
  · -- swap-invariance of `C`
    intro z b
    constructor
    · rintro ⟨hrec, hc0⟩
      have hz : orderStat z.1 ⟨n, h⟩ ≤ z.1 l ∧ orderStat z.1 ⟨n, h⟩ ≤ z.1 j := hc0
      refine ⟨?_, hz⟩
      rw [Set.mem_preimage] at hrec ⊢
      rwa [reconCproc_swap H₀ n h l j hl hj z b hz]
    · rintro ⟨hrec, hc0⟩
      have hz : orderStat z.1 ⟨n, h⟩ ≤ z.1 l ∧ orderStat z.1 ⟨n, h⟩ ≤ z.1 j := hc0
      refine ⟨?_, hz⟩
      rw [Set.mem_preimage] at hrec ⊢
      rwa [← reconCproc_swap H₀ n h l j hl hj z b hz]
  · -- `F =ᵐ M⁻¹' C`
    have hrec : F =ᵐ[μ] (fun ω => reconCproc H₀ n h (M ω)) ⁻¹' B := by
      rw [← hBpre]
      filter_upwards [hN] with ω hω
      change (ω ∈ cprocLE ⁻¹' B) = (ω ∈ (fun ω => reconCproc H₀ n h (M ω)) ⁻¹' B)
      simp only [Set.mem_preimage]
      rw [show cprocLE ω = reconCproc H₀ n h (M ω) from (reconCproc_eq W H₀ n h ω hω).symm]
    have hFC0 : F ⊆ M ⁻¹' {p | orderStat p.1.1 ⟨n, h⟩ ≤ p.1.1 l
        ∧ orderStat p.1.1 ⟨n, h⟩ ≤ p.1.1 j} := by
      intro ω hωF
      have hlm := hFl hωF
      have hjm := hFj hωF
      rw [Set.mem_setOf_eq, mem_aboveNulls] at hlm hjm
      exact ⟨hlm.2, hjm.2⟩
    have hFeq : F ∩ M ⁻¹' {p | orderStat p.1.1 ⟨n, h⟩ ≤ p.1.1 l
        ∧ orderStat p.1.1 ⟨n, h⟩ ≤ p.1.1 j} = F := Set.inter_eq_left.mpr hFC0
    rw [Set.preimage_inter, ← hFeq]
    exact hrec.inter (Filter.EventuallyEq.refl _ _)

/-- **The exchangeable sign-swap (the single research nugget, Lu-BDA §21.3).** For any
`𝒢rev n`-measurable event `F` on which two nulls `l, j` are both above `θ_n`, the events
`F ∩ {0 < W l}` and `F ∩ {0 < W j}` have equal measure. This is the exchangeability of the
above-`θ_n` null signs: `F`'s defining data (magnitudes, non-null signs, the below-`θ_n` null signs,
and the above-count `A`) is invariant under swapping the signs of `l` and `j` (both above `θ_n`),
which preserves the i.i.d.-fair joint law (`signs_iIndep`/`signs_fair`/`signs_indep_outer`).

Proof: `grev_event_outer_invariant` represents `F` (mod null) as `(outerData, nsign⃗)⁻¹' C` for a
`swap l j`-invariant measurable `C`, and the abstract `measure_inter_swap_outer` discharges the
swap equality from independence of the null signs from the outer data + their i.i.d. fairness.
- **USER-INPUT**: exchangeability of the i.i.d. fair null signs; Lu-BDA §21.3. -/
private lemma aboveNulls_sign_swap (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ)
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|)
    (n : ℕ) (h : n < d) (l j : Fin d) (hl : l ∈ H₀) (hj : j ∈ H₀)
    (F : Set Ω) (hF : MeasurableSet[𝒢rev W H₀ hW.meas n] F)
    (hFl : F ⊆ {ω | l ∈ aboveNulls W H₀ n h ω})
    (hFj : F ⊆ {ω | j ∈ aboveNulls W H₀ n h ω}) :
    μ (F ∩ {ω | 0 < W l ω}) = μ (F ∩ {ω | 0 < W j ω}) := by
  -- Extract the outer-invariant pre-image representation of `F`, then apply the abstract swap.
  obtain ⟨C, hCmeas, hCinv, hFC⟩ :=
    grev_event_outer_invariant W H₀ μ hW n h l j hl hj F hF hFl hFj
  have hswap := measure_inter_swap_outer μ (measurable_nsign W H₀ hW.meas)
    (iIndepFun_nsign W H₀ μ hW) (fair_nsign W H₀ μ hW) (outerData W H₀)
    (measurable_outerData W H₀ hW.meas) (indep_nsign_outerData W H₀ μ hW) C hCmeas
    (⟨l, hl⟩ : {x // x ∈ H₀}) ⟨j, hj⟩ hCinv
  -- Bridge `μ(F ∩ {0 < W c}) = μ((outerData,nsign⃗)⁻¹C ∩ {nsign ⟨c⟩ = true})`.
  have hbridge : ∀ (c : Fin d) (hc : c ∈ H₀),
      μ (F ∩ {ω | 0 < W c ω})
        = μ ((fun ω => (outerData W H₀ ω, fun m => nsign W H₀ m ω)) ⁻¹' C
            ∩ {ω | nsign W H₀ ⟨c, hc⟩ ω = true}) := by
    intro c hc
    have h0 : {ω | 0 < W c ω} =ᵐ[μ] {ω | nsign W H₀ ⟨c, hc⟩ ω = true} := by
      filter_upwards [null_ne_zero W H₀ μ hW c hc] with ω hω
      show (0 < W c ω) = (nsign W H₀ ⟨c, hc⟩ ω = true)
      rw [eq_iff_iff, nsign_true_iff]
      exact ⟨fun hlt => le_of_lt hlt, fun hle => lt_of_le_of_ne hle (Ne.symm hω)⟩
    calc μ (F ∩ {ω | 0 < W c ω})
        = μ (F ∩ {ω | nsign W H₀ ⟨c, hc⟩ ω = true}) :=
          measure_congr ((Filter.EventuallyEq.refl _ F).inter h0)
      _ = μ ((fun ω => (outerData W H₀ ω, fun m => nsign W H₀ m ω)) ⁻¹' C
            ∩ {ω | nsign W H₀ ⟨c, hc⟩ ω = true}) :=
          measure_congr (hFC.inter (Filter.EventuallyEq.refl _ _))
  exact (hbridge l hl).trans (hswap.trans (hbridge j hj).symm)

/-- Set-integral of a product of two `{0,1}`-indicators is the measure of the triple intersection. -/
private lemma setIntegral_ite_mul_ite (μ : Measure Ω) (s : Set Ω) (P Q : Ω → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hP : MeasurableSet {ω | P ω}) (hQ : MeasurableSet {ω | Q ω}) :
    ∫ ω in s, (if P ω then (1 : ℝ) else 0) * (if Q ω then (1 : ℝ) else 0) ∂μ
      = (μ (s ∩ {ω | P ω} ∩ {ω | Q ω})).toReal := by
  have hrw : (fun ω => (if P ω then (1 : ℝ) else 0) * (if Q ω then (1 : ℝ) else 0))
      = ({ω | P ω} ∩ {ω | Q ω}).indicator (fun _ => (1 : ℝ)) := by
    funext ω; rw [Set.indicator_apply]
    by_cases hP' : P ω <;> by_cases hQ' : Q ω <;>
      simp [hP', hQ', Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [hrw, setIntegral_indicator (hP.inter hQ), setIntegral_const, smul_eq_mul, mul_one,
    ← Set.inter_assoc]
  rfl

/-- Integrability of a product of two `{0,1}`-indicators with measurable predicate sets. -/
private lemma integrable_ite_mul_ite (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Ω → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hP : MeasurableSet {ω | P ω}) (hQ : MeasurableSet {ω | Q ω}) :
    Integrable (fun ω => (if P ω then (1 : ℝ) else 0) * (if Q ω then (1 : ℝ) else 0)) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    ((Measurable.ite hP measurable_const measurable_const).mul
      (Measurable.ite hQ measurable_const measurable_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |if P ω then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
  have h2 : |if Q ω then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
  calc |if P ω then (1 : ℝ) else 0| * |if Q ω then (1 : ℝ) else 0|
      ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **The exchangeable per-coordinate core** (the isolated research nugget, Lu-BDA §21.3). Fix a null
`j`. Restricted to the event `{cIdx = j}` (where `j` is the rank-`n` coordinate, hence one of the
`A + B` above-`θ_n` nonzero nulls), the conditional sign probability is the
sampling-without-replacement ratio `A/(A+B)`:
`μ[𝟙(cIdx=j)·𝟙(0<W j) | 𝒢rev n] =ᵐ 𝟙(cIdx=j)·A/(A+B)`. The conditioning data `𝒢rev n` fixes the
magnitudes (hence `cIdx`, the above-`θ_n` null set `S_n` and `k = A+B`) and the count `A`, while the
individual above-`θ_n` null signs are i.i.d. fair and exchangeable (`signs_iIndep`/`signs_fair`)
and independent of the outer data + below-`θ_n` signs (`signs_indep_outer`).

**Now fully assembled** from the single exchangeable nugget `aboveNulls_sign_swap`: this proof is the
explicit `ae_eq_condExp_of_forall_setIntegral_eq` disintegration (the route the `SymmetricCondExp`
kernel uses, no `StandardBorelSpace`/`CondIndepFun`). It partitions `Ω` over the finitely many values
`T` of the random above-`θ_n` null set `S_n = aboveNulls`, rewrites `A = V₊(θ_n)` as the positive
subcount of `T` and `A+B = |T|` a.e. on each cell, and reduces the per-cell set-integral identity to
`aboveNulls_sign_swap` (the only remaining gap), which states that on a `𝒢rev n`-event where two
nulls `l, j` are both above `θ_n`, `μ(F ∩ {0<W l}) = μ(F ∩ {0<W j})` — the exchangeability of the
above-`θ_n` null signs. `count_condExp_minus` is derived algebraically from this.
- **USER-INPUT**: exchangeability of the i.i.d. fair null signs; Lu-BDA §21.3. -/
private lemma core_condExp_plus (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ)
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|)
    (n : ℕ) (h : n < d) (j : Fin d) (hj : j ∈ H₀) :
    μ[(fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0) * (if 0 < W j ω then (1 : ℝ) else 0))
        | 𝒢rev W H₀ hW.meas n]
      =ᵐ[μ] fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0)
          * ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
              / ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))) := by
  have hle : (𝒢rev W H₀ hW.meas n) ≤ mΩ := (𝒢rev W H₀ hW.meas).le n
  set f : Ω → ℝ := fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0)
      * (if 0 < W j ω then (1 : ℝ) else 0) with hfdef
  set g : Ω → ℝ := fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0)
      * ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
          / ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))) with hgdef
  -- ambient measurability of the magnitude proxy `{θ_n = |W j|}`
  have hθamb : Measurable (fun ω => θ W ⟨n, h⟩ ω) := by
    unfold θ
    exact (measurable_orderStat_eval n h).comp (measurable_pi_iff.mpr fun i => (hW.meas i).abs)
  have hcevamb : MeasurableSet {ω | θ W ⟨n, h⟩ ω = |W j ω|} :=
    measurableSet_eq_fun hθamb (hW.meas j).abs
  -- a.e. nonzero nulls
  have hnz_ae : ∀ᵐ ω ∂μ, ∀ l ∈ H₀, W l ω ≠ 0 :=
    (ae_ball_iff H₀.countable_toSet).mpr (fun l hl => null_ne_zero W H₀ μ hW l hl)
  -- f integrable
  have hf_int : Integrable f μ := by
    rw [hfdef]
    exact integrable_sel_mul W H₀ μ hW.meas hmag n h j
      (fun ω => if 0 < W j ω then (1 : ℝ) else 0)
      (Measurable.ite (measurableSet_lt measurable_const (hW.meas j)) measurable_const
        measurable_const) (fun ω => by split_ifs <;> norm_num)
  -- A, B as `𝒢rev`-measurable reals (count components of `cproc`)
  have hcproc : StronglyMeasurable[𝒢rev W H₀ hW.meas n] (cproc W H₀ n) :=
    Filtration.stronglyAdapted_natural
      (fun k => (measurable_cproc W H₀ hW.meas k).stronglyMeasurable) n
  have hAm : Measurable[𝒢rev W H₀ hW.meas n]
      (fun ω => (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) := by
    have h1 : Measurable[𝒢rev W H₀ hW.meas n] (fun ω => (cproc W H₀ n ω).2.2.1) :=
      (measurable_fst.comp (measurable_snd.comp measurable_snd)).comp hcproc.measurable
    have h2 : (fun ω => (cproc W H₀ n ω).2.2.1)
        = (fun ω => (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) := by
      funext ω; dsimp only [cproc]; rw [dif_pos h]
    rwa [h2] at h1
  have hBm : Measurable[𝒢rev W H₀ hW.meas n]
      (fun ω => (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) := by
    have h1 : Measurable[𝒢rev W H₀ hW.meas n] (fun ω => (cproc W H₀ n ω).2.2.2) :=
      (measurable_snd.comp (measurable_snd.comp measurable_snd)).comp hcproc.measurable
    have h2 : (fun ω => (cproc W H₀ n ω).2.2.2)
        = (fun ω => (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) := by
      funext ω; dsimp only [cproc]; rw [dif_pos h]
    rwa [h2] at h1
  have hg_aesm' : AEStronglyMeasurable[𝒢rev W H₀ hW.meas n] g μ := by
    rw [hgdef]
    exact (aesm'_cIdx_indicator W H₀ μ hW hmag n h j).mul
      (hAm.div (hAm.add hBm)).stronglyMeasurable.aestronglyMeasurable
  -- g integrable (bounded by 1)
  have hAamb : Measurable (fun ω => (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) :=
    measurable_from_nat.comp (measurable_Vplus_theta W H₀ hW.meas n h)
  have hBamb : Measurable (fun ω => (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) :=
    measurable_from_nat.comp (measurable_Vminus_theta W H₀ hW.meas n h)
  have hg_int : Integrable g μ := by
    rw [hgdef]
    refine (integrable_const (1 : ℝ)).mono'
      ((aesm_cIdx_indicator W H₀ μ hW.meas hmag n h j).mul
        (hAamb.div (hAamb.add hBamb)).aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |if cIdx W n h ω = j then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
    have hVpnn : (0 : ℝ) ≤ (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) := Nat.cast_nonneg _
    have hVmnn : (0 : ℝ) ≤ (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) := Nat.cast_nonneg _
    have h2 : |(Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
        / ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))| ≤ 1 := by
      rw [abs_div, abs_of_nonneg hVpnn, abs_of_nonneg (by linarith)]
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
          + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) from by linarith) with he | hpos
      · rw [← he, div_zero]; norm_num
      · rw [div_le_one hpos]; linarith
    calc |if cIdx W n h ω = j then (1 : ℝ) else 0|
          * |(Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
              / ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))|
        ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  -- main: reduce to set-integral identity, then partition over `S_n = T`
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hf_int
    (fun s _ _ => hg_int.integrableOn) ?_ hg_aesm').symm
  intro s hs _
  -- partition-of-unity over the finite values `T` of `S_n`
  have hpart : ∀ (φ : Ω → ℝ), Integrable φ μ →
      ∫ ω in s, φ ω ∂μ
        = ∑ T ∈ H₀.powerset, ∫ ω in s ∩ {ω | aboveNulls W H₀ n h ω = T}, φ ω ∂μ := by
    intro φ hφ
    have hpt : ∀ ω, φ ω
        = ∑ T ∈ H₀.powerset, ({ω' | aboveNulls W H₀ n h ω' = T}.indicator φ) ω := by
      intro ω
      symm
      calc (∑ T ∈ H₀.powerset, ({ω' | aboveNulls W H₀ n h ω' = T}.indicator φ) ω)
          = ∑ T ∈ H₀.powerset, (if aboveNulls W H₀ n h ω = T then φ ω else 0) := by
            apply Finset.sum_congr rfl; intro T _
            simp only [Set.indicator_apply, Set.mem_setOf_eq]
        _ = φ ω := by
            rw [Finset.sum_ite_eq H₀.powerset (aboveNulls W H₀ n h ω) (fun _ => φ ω)]
            exact if_pos (Finset.mem_powerset.mpr (aboveNulls_subset W H₀ n h ω))
    calc ∫ ω in s, φ ω ∂μ
        = ∫ ω in s, ∑ T ∈ H₀.powerset,
            ({ω' | aboveNulls W H₀ n h ω' = T}.indicator φ) ω ∂μ :=
          setIntegral_congr_fun (hle s hs) (fun ω _ => hpt ω)
      _ = ∑ T ∈ H₀.powerset,
            ∫ ω in s, ({ω' | aboveNulls W H₀ n h ω' = T}.indicator φ) ω ∂μ :=
          integral_finset_sum _ (fun T _ =>
            (hφ.indicator (hle _ (measurableSet'_aboveNulls_eq W H₀ hW.meas n h T))).integrableOn)
      _ = ∑ T ∈ H₀.powerset, ∫ ω in s ∩ {ω | aboveNulls W H₀ n h ω = T}, φ ω ∂μ := by
          apply Finset.sum_congr rfl; intro T _
          rw [setIntegral_indicator (hle _ (measurableSet'_aboveNulls_eq W H₀ hW.meas n h T))]
  rw [hpart g hg_int, hpart f hf_int]
  apply Finset.sum_congr rfl
  intro T hT
  have hTsub : T ⊆ H₀ := Finset.mem_powerset.mp hT
  have hsTmeas : MeasurableSet (s ∩ {ω | aboveNulls W H₀ n h ω = T}) :=
    (hle s hs).inter (hle _ (measurableSet'_aboveNulls_eq W H₀ hW.meas n h T))
  by_cases hjT : j ∈ T
  · -- `j ∈ T`: the exchangeable cell
    have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨j, hjT⟩
    have hTne : (T.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hTpos.ne'
    -- the `𝒢rev`-measurable conditioning event of the cell
    have hFmeas' : MeasurableSet[𝒢rev W H₀ hW.meas n]
        ((s ∩ {ω | aboveNulls W H₀ n h ω = T}) ∩ {ω | θ W ⟨n, h⟩ ω = |W j ω|}) :=
      (hs.inter (measurableSet'_aboveNulls_eq W H₀ hW.meas n h T)).inter
        (measurableSet'_cev W H₀ hW.meas n h j)
    have hFj : ((s ∩ {ω | aboveNulls W H₀ n h ω = T}) ∩ {ω | θ W ⟨n, h⟩ ω = |W j ω|})
        ⊆ {ω | j ∈ aboveNulls W H₀ n h ω} := by
      intro ω hωF
      have hAT : aboveNulls W H₀ n h ω = T := hωF.1.2
      rw [Set.mem_setOf_eq, hAT]; exact hjT
    have hFl : ∀ l ∈ T, ((s ∩ {ω | aboveNulls W H₀ n h ω = T}) ∩ {ω | θ W ⟨n, h⟩ ω = |W j ω|})
        ⊆ {ω | l ∈ aboveNulls W H₀ n h ω} := by
      intro l hl ω hωF
      have hAT : aboveNulls W H₀ n h ω = T := hωF.1.2
      rw [Set.mem_setOf_eq, hAT]; exact hl
    -- f-side: `∫ = μ(F ∩ {0 < W j})`
    have hfside : ∫ ω in s ∩ {ω | aboveNulls W H₀ n h ω = T}, f ω ∂μ
        = (μ ((s ∩ {ω | aboveNulls W H₀ n h ω = T}) ∩ {ω | θ W ⟨n, h⟩ ω = |W j ω|}
            ∩ {ω | 0 < W j ω})).toReal := by
      have hfeq : ∫ ω in s ∩ {ω | aboveNulls W H₀ n h ω = T}, f ω ∂μ
          = ∫ ω in s ∩ {ω | aboveNulls W H₀ n h ω = T},
              (if θ W ⟨n, h⟩ ω = |W j ω| then (1 : ℝ) else 0)
                * (if 0 < W j ω then (1 : ℝ) else 0) ∂μ := by
        apply setIntegral_congr_ae hsTmeas
        filter_upwards [hmag] with ω hω _
        rw [hfdef]; dsimp only; congr 1
        by_cases hc : cIdx W n h ω = j
        · rw [if_pos hc, if_pos ((cIdx_eq_iff W n h ω hω j).mp hc)]
        · rw [if_neg hc, if_neg (fun he => hc ((cIdx_eq_iff W n h ω hω j).mpr he))]
      rw [hfeq, setIntegral_ite_mul_ite μ _ _ _ hcevamb
        (measurableSet_lt measurable_const (hW.meas j))]
    -- g-side: `∫ = (∑_{l∈T} μ(F ∩ {0 < W l}))/|T|`
    have hgside : ∫ ω in s ∩ {ω | aboveNulls W H₀ n h ω = T}, g ω ∂μ
        = (∑ l ∈ T, (μ ((s ∩ {ω | aboveNulls W H₀ n h ω = T}) ∩ {ω | θ W ⟨n, h⟩ ω = |W j ω|}
            ∩ {ω | 0 < W l ω})).toReal) / (T.card : ℝ) := by
      have hgeq : ∫ ω in s ∩ {ω | aboveNulls W H₀ n h ω = T}, g ω ∂μ
          = ∫ ω in s ∩ {ω | aboveNulls W H₀ n h ω = T},
              (∑ l ∈ T, (if θ W ⟨n, h⟩ ω = |W j ω| then (1 : ℝ) else 0)
                * (if 0 < W l ω then (1 : ℝ) else 0)) / (T.card : ℝ) ∂μ := by
        apply setIntegral_congr_ae hsTmeas
        filter_upwards [hmag, hnz_ae] with ω hω hnz hωsT
        have hAT : aboveNulls W H₀ n h ω = T := hωsT.2
        rw [hgdef]; dsimp only
        have hcidxeq : (if cIdx W n h ω = j then (1 : ℝ) else 0)
            = (if θ W ⟨n, h⟩ ω = |W j ω| then (1 : ℝ) else 0) := by
          by_cases hc : cIdx W n h ω = j
          · rw [if_pos hc, if_pos ((cIdx_eq_iff W n h ω hω j).mp hc)]
          · rw [if_neg hc, if_neg (fun he => hc ((cIdx_eq_iff W n h ω hω j).mpr he))]
        have hVp : (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
            = ((T.filter (fun l => 0 < W l ω)).card : ℝ) := by
          rw [Vplus_eq_aboveNulls_filter, hAT]
        have hAB : (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
            = (T.card : ℝ) := by
          rw [← Nat.cast_add, Vplus_add_Vminus_eq_card W H₀ n h ω (fun l hl => hnz l hl), hAT]
        have hcard : ((T.filter (fun l => 0 < W l ω)).card : ℝ)
            = ∑ l ∈ T, (if 0 < W l ω then (1 : ℝ) else 0) := by
          rw [Finset.card_filter, Nat.cast_sum]
          apply Finset.sum_congr rfl; intro l _; split_ifs <;> simp
        rw [hcidxeq, hAB, hVp, hcard, ← mul_div_assoc, Finset.mul_sum]
      rw [hgeq, integral_div,
        integral_finset_sum T (fun l _ =>
          (integrable_ite_mul_ite μ _ _ hcevamb
            (measurableSet_lt measurable_const (hW.meas l))).integrableOn)]
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      exact setIntegral_ite_mul_ite μ _ _ _ hcevamb
        (measurableSet_lt measurable_const (hW.meas l))
    -- combine via the exchangeable swap
    rw [hgside, hfside]
    have hswap : ∀ l ∈ T,
        (μ ((s ∩ {ω | aboveNulls W H₀ n h ω = T}) ∩ {ω | θ W ⟨n, h⟩ ω = |W j ω|}
            ∩ {ω | 0 < W l ω})).toReal
          = (μ ((s ∩ {ω | aboveNulls W H₀ n h ω = T}) ∩ {ω | θ W ⟨n, h⟩ ω = |W j ω|}
              ∩ {ω | 0 < W j ω})).toReal := by
      intro l hl
      congr 1
      exact aboveNulls_sign_swap W H₀ μ hW hmag n h l j (hTsub hl) hj _ hFmeas' (hFl l hl) hFj
    rw [Finset.sum_congr rfl hswap, Finset.sum_const, nsmul_eq_mul, mul_comm, mul_div_assoc,
      div_self hTne, mul_one]
  · -- `j ∉ T`: the cell selector `𝟙(cIdx = j)` vanishes a.e.
    have hcidx0 : ∀ᵐ ω ∂μ,
        ω ∈ s ∩ {ω | aboveNulls W H₀ n h ω = T} → (if cIdx W n h ω = j then (1 : ℝ) else 0) = 0 := by
      filter_upwards [hmag] with ω hω hωsT
      have hAT : aboveNulls W H₀ n h ω = T := hωsT.2
      rw [if_neg]; intro hc
      have he : θ W ⟨n, h⟩ ω = |W j ω| := (cIdx_eq_iff W n h ω hω j).mp hc
      have hjmem : j ∈ aboveNulls W H₀ n h ω :=
        (mem_aboveNulls W H₀ n h ω j).mpr ⟨hj, le_of_eq he⟩
      rw [hAT] at hjmem; exact hjT hjmem
    have hf0 : ∫ ω in s ∩ {ω | aboveNulls W H₀ n h ω = T}, f ω ∂μ = 0 := by
      rw [show (∫ ω in s ∩ {ω | aboveNulls W H₀ n h ω = T}, f ω ∂μ)
          = ∫ _ω in s ∩ {ω | aboveNulls W H₀ n h ω = T}, (0 : ℝ) ∂μ from ?_, integral_zero]
      apply setIntegral_congr_ae hsTmeas
      filter_upwards [hcidx0] with ω hω hωsT
      rw [hfdef]; dsimp only; rw [hω hωsT, zero_mul]
    have hg0 : ∫ ω in s ∩ {ω | aboveNulls W H₀ n h ω = T}, g ω ∂μ = 0 := by
      rw [show (∫ ω in s ∩ {ω | aboveNulls W H₀ n h ω = T}, g ω ∂μ)
          = ∫ _ω in s ∩ {ω | aboveNulls W H₀ n h ω = T}, (0 : ℝ) ∂μ from ?_, integral_zero]
      apply setIntegral_congr_ae hsTmeas
      filter_upwards [hcidx0] with ω hω hωsT
      rw [hgdef]; dsimp only; rw [hω hωsT, zero_mul]
    rw [hg0, hf0]

/-- **The exchangeable per-coordinate core, negative sign.** Derived from `core_condExp_plus` via
`𝟙(W j < 0) =ᵐ 1 − 𝟙(0 < W j)` (nulls are a.s. nonzero, `null_ne_zero`) and `condExp` linearity,
using that on `{cIdx = j}` the denominator `A + B ≥ 1` (the crossed null is one of the nonzero
above-`θ_n` nulls). -/
private lemma core_condExp_minus (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ)
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|)
    (n : ℕ) (h : n < d) (j : Fin d) (hj : j ∈ H₀) :
    μ[(fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0) * (if W j ω < 0 then (1 : ℝ) else 0))
        | 𝒢rev W H₀ hW.meas n]
      =ᵐ[μ] fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0)
          * ((Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
              / ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))) := by
  have hle : 𝒢rev W H₀ hW.meas n ≤ mΩ := (𝒢rev W H₀ hW.meas).le n
  -- integrabilities
  have hej_int := integrable_sel W H₀ μ hW.meas hmag n h j
  have hfj_int := integrable_sel_mul W H₀ μ hW.meas hmag n h j
    (fun ω => if 0 < W j ω then (1 : ℝ) else 0)
    (Measurable.ite (measurableSet_lt measurable_const (hW.meas j)) measurable_const
      measurable_const) (fun ω => by split_ifs <;> norm_num)
  -- condExp of the bare selector equals itself (𝒢rev-measurable a.e.)
  have hcej : μ[(fun ω => if cIdx W n h ω = j then (1 : ℝ) else 0) | 𝒢rev W H₀ hW.meas n]
      =ᵐ[μ] fun ω => if cIdx W n h ω = j then (1 : ℝ) else 0 :=
    condExp_of_aestronglyMeasurable' hle (aesm'_cIdx_indicator W H₀ μ hW hmag n h j) hej_int
  -- f'j =ᵐ ej - fj
  have hfmj_eq : (fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0)
        * (if W j ω < 0 then (1 : ℝ) else 0))
      =ᵐ[μ] (fun ω => if cIdx W n h ω = j then (1 : ℝ) else 0)
        - (fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0) * (if 0 < W j ω then (1 : ℝ) else 0)) := by
    filter_upwards [null_ne_zero W H₀ μ hW j hj] with ω hω
    simp only [Pi.sub_apply]
    by_cases hpos : 0 < W j ω
    · have hnn : ¬ W j ω < 0 := by linarith
      simp [hnn, hpos]
    · have hneg : W j ω < 0 := lt_of_le_of_ne (not_lt.mp hpos) hω
      simp [hneg, hpos]
  -- condExp linearity
  have step : μ[(fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0)
        * (if W j ω < 0 then (1 : ℝ) else 0)) | 𝒢rev W H₀ hW.meas n]
      =ᵐ[μ] μ[(fun ω => if cIdx W n h ω = j then (1 : ℝ) else 0) | 𝒢rev W H₀ hW.meas n]
        - μ[(fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0)
            * (if 0 < W j ω then (1 : ℝ) else 0)) | 𝒢rev W H₀ hW.meas n] :=
    (condExp_congr_ae hfmj_eq).trans (condExp_sub hej_int hfj_int _)
  have hcfj := core_condExp_plus W H₀ μ hW hmag n h j hj
  filter_upwards [step, hcej, hcfj, null_ne_zero W H₀ μ hW j hj, hmag]
    with ω hstep hcejω hcfjω hω hmagω
  rw [hstep]; simp only [Pi.sub_apply]; rw [hcejω, hcfjω]
  by_cases hc : cIdx W n h ω = j
  · have hθ : θ W ⟨n, h⟩ ω = |W j ω| := (cIdx_eq_iff W n h ω hmagω j).mp hc
    have hAB : 0 < (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
        + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) := by
      rcases lt_or_gt_of_ne hω with hneg | hpos
      · have hmemM : j ∈ Sminus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ := by
          simp only [Finset.mem_inter, Sminus, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨⟨le_of_eq hθ, hneg⟩, hj⟩
        have hB1 : (1 : ℝ) ≤ (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) := by
          have : 1 ≤ Vminus W H₀ (θ W ⟨n, h⟩ ω) ω := Finset.card_pos.mpr ⟨j, hmemM⟩
          exact_mod_cast this
        have := (Nat.cast_nonneg (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω) : (0:ℝ) ≤ _); linarith
      · have hmemP : j ∈ Splus W (θ W ⟨n, h⟩ ω) ω ∩ H₀ := by
          simp only [Finset.mem_inter, Splus, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨⟨le_of_eq hθ, hpos⟩, hj⟩
        have hA1 : (1 : ℝ) ≤ (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) := by
          have : 1 ≤ Vplus W H₀ (θ W ⟨n, h⟩ ω) ω := Finset.card_pos.mpr ⟨j, hmemP⟩
          exact_mod_cast this
        have := (Nat.cast_nonneg (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω) : (0:ℝ) ≤ _); linarith
    simp only [if_pos hc, one_mul]
    rw [sub_eq_iff_eq_add, ← add_div, eq_div_iff hAB.ne', one_mul]
    ring
  · rw [if_neg hc]; ring

/-- **Exchangeable conditional expectation of the positive-null removal** (`count_condExp`, the
crux, Lu-BDA §21.3). The increment `ΔV₊ = V₊(θ_n) − V₊(θ_{n+1})` is the indicator that the rank-`n`
coordinate `cIdx` is a *positive null*. Conditioned on the count filtration `𝒢rev n`, the crossed
null is positive with the sampling-without-replacement probability `A/(A+B)` (`A = V₊(θ_n)`,
`B = V₋(θ_n)`), restricted to the event that `cIdx` is a null at all:
`μ[ΔV₊ | 𝒢rev n] =ᵐ 𝟙(cIdx ∈ H₀) · A/(A+B)`.
- **USER-INPUT**: exchangeability of the i.i.d. fair null signs (`hW.signs_iIndep`/`signs_fair`/
  `signs_indep_outer`); Lu-BDA §21.3. -/
private lemma count_condExp_plus (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ)
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) (n : ℕ) (h : n < d) (h1 : n + 1 < d) :
    μ[(fun ω => (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
          - (Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ)) | 𝒢rev W H₀ hW.meas n]
      =ᵐ[μ] fun ω => (if cIdx W n h ω ∈ H₀ then (1 : ℝ) else 0)
          * ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
              / ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))) := by
  -- ΔV₊ =ᵐ ∑_{j∈H₀} 𝟙(cIdx=j)·𝟙(0<Wj); push through condExp via `condExp_finset_sum` and the
  -- per-coordinate core `core_condExp_plus`; reassemble the sum to `𝟙(cIdx∈H₀)·A/(A+B)`.
  have hfint : ∀ j ∈ H₀, Integrable
      (fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0) * (if 0 < W j ω then (1 : ℝ) else 0)) μ :=
    fun j _ => integrable_sel_mul W H₀ μ hW.meas hmag n h j
      (fun ω => if 0 < W j ω then (1 : ℝ) else 0)
      (Measurable.ite (measurableSet_lt measurable_const (hW.meas j)) measurable_const
        measurable_const) (fun ω => by split_ifs <;> norm_num)
  have hdP : (fun ω => (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
        - (Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ))
      =ᵐ[μ] ∑ j ∈ H₀, fun ω =>
        (if cIdx W n h ω = j then (1 : ℝ) else 0) * (if 0 < W j ω then (1 : ℝ) else 0) := by
    filter_upwards [hmag] with ω hω
    have hterm : ∀ j : Fin d,
        (if cIdx W n h ω = j then (1 : ℝ) else 0) * (if 0 < W j ω then (1 : ℝ) else 0)
          = if cIdx W n h ω = j then (if 0 < W j ω then (1 : ℝ) else 0) else 0 :=
      fun j => by split_ifs <;> norm_num
    rw [dPlus_eq_indicator W H₀ n h h1 ω hω, Finset.sum_apply]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq H₀ (cIdx W n h ω) (fun j => if 0 < W j ω then (1 : ℝ) else 0)]
    by_cases hm : cIdx W n h ω ∈ H₀
    · by_cases hp : 0 < W (cIdx W n h ω) ω <;> simp [hm, hp]
    · simp [hm]
  calc μ[(fun ω => (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
          - (Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ)) | 𝒢rev W H₀ hW.meas n]
      =ᵐ[μ] μ[∑ j ∈ H₀, fun ω =>
        (if cIdx W n h ω = j then (1 : ℝ) else 0) * (if 0 < W j ω then (1 : ℝ) else 0)
        | 𝒢rev W H₀ hW.meas n] := condExp_congr_ae hdP
    _ =ᵐ[μ] ∑ j ∈ H₀, μ[fun ω =>
        (if cIdx W n h ω = j then (1 : ℝ) else 0) * (if 0 < W j ω then (1 : ℝ) else 0)
        | 𝒢rev W H₀ hW.meas n] := condExp_finset_sum hfint _
    _ =ᵐ[μ] ∑ j ∈ H₀, fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0)
        * ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
            / ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))) :=
        eventuallyEq_sum (fun j hj => core_condExp_plus W H₀ μ hW hmag n h j hj)
    _ =ᵐ[μ] fun ω => (if cIdx W n h ω ∈ H₀ then (1 : ℝ) else 0)
        * ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
            / ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))) := by
      filter_upwards with ω
      simp only [Finset.sum_apply]
      rw [← Finset.sum_mul, Finset.sum_ite_eq H₀ (cIdx W n h ω) (fun _ => (1 : ℝ))]

/-- **Exchangeable conditional expectation of the negative-null removal** (`count_condExp`, Lu-BDA
§21.3); the `V₋` analogue of `count_condExp_plus`, with conditional probability `B/(A+B)`. -/
private lemma count_condExp_minus (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ)
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) (n : ℕ) (h : n < d) (h1 : n + 1 < d) :
    μ[(fun ω => (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
          - (Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ)) | 𝒢rev W H₀ hW.meas n]
      =ᵐ[μ] fun ω => (if cIdx W n h ω ∈ H₀ then (1 : ℝ) else 0)
          * ((Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
              / ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))) := by
  -- ΔV₋ =ᵐ ∑_{j∈H₀} 𝟙(cIdx=j)·𝟙(Wj<0); push through condExp via `condExp_finset_sum` and the
  -- per-coordinate core `core_condExp_minus`; reassemble to `𝟙(cIdx∈H₀)·B/(A+B)`.
  have hfint : ∀ j ∈ H₀, Integrable
      (fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0) * (if W j ω < 0 then (1 : ℝ) else 0)) μ :=
    fun j _ => integrable_sel_mul W H₀ μ hW.meas hmag n h j
      (fun ω => if W j ω < 0 then (1 : ℝ) else 0)
      (Measurable.ite (measurableSet_lt (hW.meas j) measurable_const) measurable_const
        measurable_const) (fun ω => by split_ifs <;> norm_num)
  have hdM : (fun ω => (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
        - (Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ))
      =ᵐ[μ] ∑ j ∈ H₀, fun ω =>
        (if cIdx W n h ω = j then (1 : ℝ) else 0) * (if W j ω < 0 then (1 : ℝ) else 0) := by
    filter_upwards [hmag] with ω hω
    have hterm : ∀ j : Fin d,
        (if cIdx W n h ω = j then (1 : ℝ) else 0) * (if W j ω < 0 then (1 : ℝ) else 0)
          = if cIdx W n h ω = j then (if W j ω < 0 then (1 : ℝ) else 0) else 0 :=
      fun j => by split_ifs <;> norm_num
    rw [dMinus_eq_indicator W H₀ n h h1 ω hω, Finset.sum_apply]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq H₀ (cIdx W n h ω) (fun j => if W j ω < 0 then (1 : ℝ) else 0)]
    by_cases hm : cIdx W n h ω ∈ H₀
    · by_cases hp : W (cIdx W n h ω) ω < 0 <;> simp [hm, hp]
    · simp [hm]
  calc μ[(fun ω => (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
          - (Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ)) | 𝒢rev W H₀ hW.meas n]
      =ᵐ[μ] μ[∑ j ∈ H₀, fun ω =>
        (if cIdx W n h ω = j then (1 : ℝ) else 0) * (if W j ω < 0 then (1 : ℝ) else 0)
        | 𝒢rev W H₀ hW.meas n] := condExp_congr_ae hdM
    _ =ᵐ[μ] ∑ j ∈ H₀, μ[fun ω =>
        (if cIdx W n h ω = j then (1 : ℝ) else 0) * (if W j ω < 0 then (1 : ℝ) else 0)
        | 𝒢rev W H₀ hW.meas n] := condExp_finset_sum hfint _
    _ =ᵐ[μ] ∑ j ∈ H₀, fun ω => (if cIdx W n h ω = j then (1 : ℝ) else 0)
        * ((Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
            / ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))) :=
        eventuallyEq_sum (fun j hj => core_condExp_minus W H₀ μ hW hmag n h j hj)
    _ =ᵐ[μ] fun ω => (if cIdx W n h ω ∈ H₀ then (1 : ℝ) else 0)
        * ((Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
            / ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))) := by
      filter_upwards with ω
      simp only [Finset.sum_apply]
      rw [← Finset.sum_mul, Finset.sum_ite_eq H₀ (cIdx W n h ω) (fun _ => (1 : ℝ))]

/-- **One-step conditional expectation inequality** (the high-risk core lemma):
`μ[Yproc (n+1) | 𝒢rev n] ≤ᵐ[μ] Yproc n`. The step is a supermartingale by the **count filtration**
/ exchangeability, not a "fresh independent coin":

* At a step `n → n+1` whose crossed coordinate `θ_n → θ_{n+1}` is a **non-null** coordinate, the
  null counts `V₊, V₋` (which count only `H₀`) are unchanged, so `Yproc (n+1) = Yproc n` — a trivial
  (deterministic) martingale step.
* At a **null** step, the removed null's sign is uniform among the remaining nulls (exchangeability
  of the i.i.d. fair null signs given the outer data, `count_condExp`): with `A = V₊(θ_n)`,
  `B = V₋(θ_n)` and `k = A + B`, the crossed null is positive with probability `A/k` (then
  `V₊ → A−1`, `V₋ → B`) and negative with probability `B/k` (then `V₊ → A`, `V₋ → B−1`), so
  `E[Yproc (n+1) | 𝒢rev n] = (A/k)·(A−1)/(1+B) + (B/k)·A/B = A/(1+B) = Yproc n`.

- **USER-INPUT**: sign exchangeability from `hW.signs_iIndep`/`signs_fair`/`signs_indep_outer`;
  Lu-BDA §21.3. -/
lemma step_condExp_le (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ)
    -- USER-INPUT: a.s. distinct magnitudes (continuous knock-off statistics, no |Wᵢ| ties); Lu-BDA §21.3.
    -- Needed so each threshold step removes exactly one coordinate (the single-null exchangeable step).
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) (n : ℕ) :
    μ[Yproc W H₀ (n + 1) | 𝒢rev W H₀ hW.meas n] ≤ᵐ[μ] Yproc W H₀ n := by
  by_cases h1 : n + 1 < d
  · -- The non-trivial step `n → n+1` (both indices in range).
    have h : n < d := by omega
    have hle : 𝒢rev W H₀ hW.meas n ≤ mΩ := (𝒢rev W H₀ hW.meas).le n
    -- mΩ-measurability of the four count values.
    have hAfμ : Measurable (fun ω => (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) :=
      measurable_from_nat.comp (measurable_Vplus_theta W H₀ hW.meas n h)
    have hApμ : Measurable (fun ω => (Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ)) :=
      measurable_from_nat.comp (measurable_Vplus_theta W H₀ hW.meas (n + 1) h1)
    have hBfμ : Measurable (fun ω => (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) :=
      measurable_from_nat.comp (measurable_Vminus_theta W H₀ hW.meas n h)
    have hBpμ : Measurable (fun ω => (Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ)) :=
      measurable_from_nat.comp (measurable_Vminus_theta W H₀ hW.meas (n + 1) h1)
    -- Counts are bounded by `H₀.card`.
    have hVp_card : ∀ (t : ℝ) (ω : Ω), (Vplus W H₀ t ω : ℝ) ≤ (H₀.card : ℝ) := fun t ω => by
      simp only [Vplus]; exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    have hVm_card : ∀ (t : ℝ) (ω : Ω), (Vminus W H₀ t ω : ℝ) ≤ (H₀.card : ℝ) := fun t ω => by
      simp only [Vminus]; exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    -- `𝒢rev n`-strong measurability of the count values (components of `cproc n`).
    have hcproc : StronglyMeasurable[𝒢rev W H₀ hW.meas n] (cproc W H₀ n) :=
      Filtration.stronglyAdapted_natural
        (fun k => (measurable_cproc W H₀ hW.meas k).stronglyMeasurable) n
    have hAf_sm : StronglyMeasurable[𝒢rev W H₀ hW.meas n]
        (fun ω => (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) := by
      have he : (fun ω => (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))
          = (fun x : (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ => x.2.2.1) ∘ (cproc W H₀ n) := by
        funext ω; simp only [Function.comp_apply, cproc]; rw [dif_pos h]
      rw [he]
      exact ((measurable_fst.comp (measurable_snd.comp measurable_snd)).comp
        hcproc.measurable).stronglyMeasurable
    have hBf_sm : StronglyMeasurable[𝒢rev W H₀ hW.meas n]
        (fun ω => (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) := by
      have he : (fun ω => (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))
          = (fun x : (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ => x.2.2.2) ∘ (cproc W H₀ n) := by
        funext ω; simp only [Function.comp_apply, cproc]; rw [dif_pos h]
      rw [he]
      exact ((measurable_snd.comp (measurable_snd.comp measurable_snd)).comp
        hcproc.measurable).stronglyMeasurable
    -- Named coefficient (`cZero, cP, cM`), increment (`dP, dM`), probability (`gP, gM`) functions.
    set cZero : Ω → ℝ := fun ω =>
      (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) / (1 + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) with hcZero
    set cP : Ω → ℝ := fun ω =>
      ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) - 1) / (1 + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))
        - (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) / (1 + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) with hcP
    set cM : Ω → ℝ := fun ω =>
      (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) / (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
        - (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) / (1 + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) with hcM
    set dP : Ω → ℝ := fun ω =>
      (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) - (Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ) with hdP
    set dM : Ω → ℝ := fun ω =>
      (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) - (Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ) with hdM
    set gP : Ω → ℝ := fun ω => (if cIdx W n h ω ∈ H₀ then (1 : ℝ) else 0)
        * ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
            / ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))) with hgP
    set gM : Ω → ℝ := fun ω => (if cIdx W n h ω ∈ H₀ then (1 : ℝ) else 0)
        * ((Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
            / ((Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))) with hgM
    -- `𝒢rev n`-strong measurability of the coefficients.
    have hcZero_sm : StronglyMeasurable[𝒢rev W H₀ hW.meas n] cZero := by
      rw [hcZero]; exact hAf_sm.div (stronglyMeasurable_const.add hBf_sm)
    have hcP_sm : StronglyMeasurable[𝒢rev W H₀ hW.meas n] cP := by
      rw [hcP]
      exact ((hAf_sm.sub stronglyMeasurable_const).div
        (stronglyMeasurable_const.add hBf_sm)).sub
        (hAf_sm.div (stronglyMeasurable_const.add hBf_sm))
    have hcM_sm : StronglyMeasurable[𝒢rev W H₀ hW.meas n] cM := by
      rw [hcM]
      exact (hAf_sm.div hBf_sm).sub (hAf_sm.div (stronglyMeasurable_const.add hBf_sm))
    -- Integrability via boundedness on the probability measure `μ`.
    have hfin : ∀ (f : Ω → ℝ) (C : ℝ), AEStronglyMeasurable f μ → (∀ ω, |f ω| ≤ C) →
        Integrable f μ := fun f C hf hb => (integrable_const C).mono' hf
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb ω)
    have hiZero : Integrable cZero μ := by
      refine hfin cZero (H₀.card : ℝ) (hcZero_sm.mono hle).aestronglyMeasurable (fun ω => ?_)
      simp only [hcZero]
      have hb0 : (0 : ℝ) ≤ (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) := Nat.cast_nonneg _
      rw [abs_of_nonneg (by positivity)]
      exact le_trans (div_le_self (Nat.cast_nonneg _) (by linarith)) (hVp_card _ _)
    have hidP : Integrable dP μ := by
      refine hfin dP (H₀.card : ℝ) (hAfμ.sub hApμ).aestronglyMeasurable (fun ω => ?_)
      simp only [hdP]
      have h1' : (0 : ℝ) ≤ (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) := Nat.cast_nonneg _
      have h2' : (0 : ℝ) ≤ (Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ) := Nat.cast_nonneg _
      have h3' := hVp_card (θ W ⟨n, h⟩ ω) ω
      have h4' := hVp_card (θ W ⟨n + 1, h1⟩ ω) ω
      rw [abs_le]; constructor <;> linarith
    have hidM : Integrable dM μ := by
      refine hfin dM (H₀.card : ℝ) (hBfμ.sub hBpμ).aestronglyMeasurable (fun ω => ?_)
      simp only [hdM]
      have h1' : (0 : ℝ) ≤ (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) := Nat.cast_nonneg _
      have h2' : (0 : ℝ) ≤ (Vminus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ) := Nat.cast_nonneg _
      have h3' := hVm_card (θ W ⟨n, h⟩ ω) ω
      have h4' := hVm_card (θ W ⟨n + 1, h1⟩ ω) ω
      rw [abs_le]; constructor <;> linarith
    have hiuP : Integrable (cP * dP) μ := by
      refine hfin (cP * dP) (H₀.card : ℝ)
        ((hcP_sm.mono hle).aestronglyMeasurable.mul (hAfμ.sub hApμ).aestronglyMeasurable)
        (fun ω => ?_)
      rw [Pi.mul_apply, abs_mul]
      have hb0 : (0 : ℝ) ≤ (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) := Nat.cast_nonneg _
      have hbcP : |cP ω| ≤ 1 := by
        have hcPeq : cP ω = -(1 / (1 + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))) := by
          simp only [hcP]; ring
        rw [hcPeq, abs_neg, abs_of_nonneg (by positivity)]
        rw [div_le_one (by linarith)]; linarith
      have hbdP : |dP ω| ≤ (H₀.card : ℝ) := by
        simp only [hdP]
        have h1' : (0 : ℝ) ≤ (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) := Nat.cast_nonneg _
        have h2' : (0 : ℝ) ≤ (Vplus W H₀ (θ W ⟨n + 1, h1⟩ ω) ω : ℝ) := Nat.cast_nonneg _
        have h3' := hVp_card (θ W ⟨n, h⟩ ω) ω
        have h4' := hVp_card (θ W ⟨n + 1, h1⟩ ω) ω
        rw [abs_le]; constructor <;> linarith
      calc |cP ω| * |dP ω| ≤ 1 * (H₀.card : ℝ) :=
            mul_le_mul hbcP hbdP (abs_nonneg _) zero_le_one
        _ = (H₀.card : ℝ) := one_mul _
    have hiuM : Integrable (cM * dM) μ := by
      have hbig := ((Yproc_integrable W H₀ hW.meas μ (n + 1)).sub hiZero).sub hiuP
      refine hbig.congr ?_
      filter_upwards [hmag] with ω hω
      have hsr := step_removal_eq W H₀ n h h1 ω hω
      simp only [Pi.sub_apply, Pi.mul_apply, hcZero, hcP, hdP, hcM, hdM]
      linear_combination hsr
    -- The exchangeable conditional expectations of the increments.
    have hPc : μ[dP | 𝒢rev W H₀ hW.meas n] =ᵐ[μ] gP := by
      rw [hdP, hgP]; exact count_condExp_plus W H₀ μ hW hmag n h h1
    have hMc : μ[dM | 𝒢rev W H₀ hW.meas n] =ᵐ[μ] gM := by
      rw [hdM, hgM]; exact count_condExp_minus W H₀ μ hW hmag n h h1
    -- Pull the `𝒢rev n`-measurable coefficients out of the conditional expectation.
    have huP : μ[cP * dP | 𝒢rev W H₀ hW.meas n] =ᵐ[μ] cP * gP := by
      have h2 := condExp_mul_of_stronglyMeasurable_left hcP_sm hiuP hidP
      filter_upwards [h2, hPc] with ω ha hb
      rw [ha]; simp only [Pi.mul_apply]; rw [hb]
    have huM : μ[cM * dM | 𝒢rev W H₀ hW.meas n] =ᵐ[μ] cM * gM := by
      have h2 := condExp_mul_of_stronglyMeasurable_left hcM_sm hiuM hidM
      filter_upwards [h2, hMc] with ω ha hb
      rw [ha]; simp only [Pi.mul_apply]; rw [hb]
    -- Combine: `μ[Yproc(n+1)|𝒢rev n] =ᵐ cZero + cP·gP + cM·gM`.
    have e1 : μ[Yproc W H₀ (n + 1) | 𝒢rev W H₀ hW.meas n]
        =ᵐ[μ] μ[cZero + cP * dP + cM * dM | 𝒢rev W H₀ hW.meas n] := by
      apply condExp_congr_ae
      filter_upwards [hmag] with ω hω
      have hsr := step_removal_eq W H₀ n h h1 ω hω
      simp only [Pi.add_apply, Pi.mul_apply, hcZero, hcP, hdP, hcM, hdM]
      linear_combination hsr
    have e2 := condExp_add (hiZero.add hiuP) hiuM (𝒢rev W H₀ hW.meas n)
    have e3 := condExp_add hiZero hiuP (𝒢rev W H₀ hW.meas n)
    have e0 : μ[cZero | 𝒢rev W H₀ hW.meas n] = cZero :=
      condExp_of_stronglyMeasurable hle hcZero_sm hiZero
    have hce : μ[Yproc W H₀ (n + 1) | 𝒢rev W H₀ hW.meas n]
        =ᵐ[μ] (fun ω => cZero ω + cP ω * gP ω + cM ω * gM ω) := by
      filter_upwards [e1, e2, e3, huP, huM] with ω q1 q2 q3 qp qm
      have e0ω : μ[cZero | 𝒢rev W H₀ hW.meas n] ω = cZero ω := congrFun e0 ω
      simp only [Pi.add_apply, Pi.mul_apply] at q2 q3 qp qm ⊢
      rw [q1, q2, q3, e0ω, qp, qm]
    -- Pointwise bound: `cZero + cP·gP + cM·gM ≤ Yproc n` (= `cZero`), by `step_ratio_le''`.
    refine hce.trans_le ?_
    filter_upwards [hmag] with ω hω
    rw [show Yproc W H₀ n ω = (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
        / (1 + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)) from by simp only [Yproc]; rw [dif_pos h]]
    by_cases hcase : cIdx W n h ω ∈ H₀
    · simp only [hcZero, hcP, hcM, hgP, hgM, if_pos hcase, one_mul]
      exact step_ratio_le'' (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω) (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω)
    · simp only [hcZero, hgP, hgM, if_neg hcase, zero_mul, mul_zero, add_zero, le_refl]
  · -- Boundary: `n+1 ≥ d`, so `Yproc (n+1) = 0` and `μ[0|𝒢rev n] = 0 ≤ Yproc n`.
    have hz : μ[Yproc W H₀ (n + 1) | 𝒢rev W H₀ hW.meas n] = (0 : Ω → ℝ) := by
      have h0 : Yproc W H₀ (n + 1) = (0 : Ω → ℝ) := by
        funext ω; simp only [Yproc, Pi.zero_apply]; rw [dif_neg h1]
      rw [h0, condExp_zero]
    rw [hz]
    exact ae_of_all _ fun ω => Yproc_nonneg W H₀ n ω

/-- `Yproc W H₀` is a supermartingale w.r.t. `𝒢rev W H₀ hW.meas`. Assembled from
`supermartingale_nat` applied to `step_condExp_le`; all hypotheses are in scope. (The only
remaining debt in the chain is the isolated exchangeable core `core_condExp_plus`.) -/
lemma knockoff_supermartingale (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ)
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) :
    Supermartingale (Yproc W H₀) (𝒢rev W H₀ hW.meas) μ :=
  supermartingale_nat
    (Yproc_adapted W H₀ hW.meas)
    (fun n => Yproc_integrable W H₀ hW.meas μ n)
    (fun n => step_condExp_le W H₀ μ hW hmag n)

/-! ## 5. Stopping time (tauStar) -/

/-- `tauStar W H₀ α ω` is the index in `{0, …, d}` corresponding to the knock-off threshold
`tStar W α ω` in the `Yproc` index space: the first n for which `FDPhat(θ n ω) ≤ α`, where `θ`
ranges over the order statistics of **all `d`** magnitudes. Bounded by `d`. Defined via
`hittingBtwn` on the FDPhat-at-θ process. Re-indexing over all `d` magnitudes (Candès §11.5) is
what makes `tauStar` align with `tStar = min{ t ∈ {|W_j|} : FDPhat ≤ α }`.
- **USER-INPUT**: the index-to-threshold correspondence; Lu-BDA §21.3. -/
noncomputable def tauStar (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) : Ω → ℕ∞ :=
  fun ω => ↑(hittingBtwn
    (fun (n : ℕ) (ω : Ω) => if h : n < d then FDPhat W (θ W ⟨n, h⟩ ω) ω else α - 1)
    (Set.Iic α) 0 d ω)

/-- `#S⁺(t)` splits into the null count `V₊(t)` plus the non-null positives above `t`. -/
private lemma Splus_card_decomp (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (t : ℝ) (ω : Ω) :
    (Splus W t ω).card =
      Vplus W H₀ t ω + (H₀ᶜ.filter (fun j => t ≤ |W j ω| ∧ 0 < W j ω)).card := by
  have key := Finset.card_inter_add_card_sdiff (Splus W t ω) H₀
  have hsd : Splus W t ω \ H₀ = H₀ᶜ.filter (fun j => t ≤ |W j ω| ∧ 0 < W j ω) := by
    ext j
    simp only [Finset.mem_sdiff, Splus, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl]
    tauto
  rw [hsd] at key
  simp only [Vplus]; omega

/-- `#S⁻(t)` splits into the null count `V₋(t)` plus the non-null negatives above `t`. -/
private lemma Sminus_card_decomp (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (t : ℝ) (ω : Ω) :
    (Sminus W t ω).card =
      Vminus W H₀ t ω + (H₀ᶜ.filter (fun j => t ≤ |W j ω| ∧ W j ω < 0)).card := by
  have key := Finset.card_inter_add_card_sdiff (Sminus W t ω) H₀
  have hsd : Sminus W t ω \ H₀ = H₀ᶜ.filter (fun j => t ≤ |W j ω| ∧ W j ω < 0) := by
    ext j
    simp only [Finset.mem_sdiff, Sminus, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl]
    tauto
  rw [hsd] at key
  simp only [Vminus]; omega

/-- The FDPhat-at-θ process is adapted to the count filtration `𝒢rev`: `FDPhat(θ_n)` is a Borel
function of `cproc n`. `#S±(θ_n) = V±(θ_n) + (non-null count above θ_n)`, where `V±(θ_n)` are the
count components of `cproc n` and the non-null counts are functions of the magnitudes + non-null
signs (also in `cproc n`); the threshold `θ_n ≤ |W_j|` is the rank condition `n < #{k | …}` over all
`d` coordinates.
- **USER-INPUT**: adaptedness from the count-filtration structure; Lu-BDA §21.3. -/
private lemma FDPhat_atTheta_adapted (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ)
    (hWmeas : ∀ j, Measurable (W j)) :
    Adapted (𝒢rev W H₀ hWmeas)
      (fun (n : ℕ) (ω : Ω) =>
        if h : n < d then FDPhat W (θ W ⟨n, h⟩ ω) ω else α - 1) := by
  intro n
  -- The rank predicate, as a function of a magnitude vector `m`, over all `d` coordinates.
  let rank : (Fin d → ℝ) → Fin d → ℕ := fun m j =>
    ((Finset.univ : Finset (Fin d)).filter
      (fun k => m k ≤ m j)).card
  -- The Borel function `G` of `cproc n` computing the process value.
  let G : ((Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ) → ℝ := fun x =>
    if n < d then
      (x.2.2.2 + ((H₀ᶜ.filter (fun j => n < rank x.1 j ∧ x.2.1 j = -1)).card : ℝ) + 1)
        / max (x.2.2.1 + ((H₀ᶜ.filter
            (fun j => n < rank x.1 j ∧ x.2.1 j = 1 ∧ x.1 j ≠ 0)).card : ℝ)) 1
    else α - 1
  have hc : StronglyMeasurable[𝒢rev W H₀ hWmeas n] (cproc W H₀ n) :=
    Filtration.stronglyAdapted_natural
      (fun n => (measurable_cproc W H₀ hWmeas n).stronglyMeasurable) n
  -- `G` is measurable.
  have hrank_meas : ∀ j, Measurable (fun x : (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ => rank x.1 j) :=
    fun j => by
      simp only [rank]
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.measurable_sum _ fun k _ =>
        Measurable.ite (measurableSet_le
          ((measurable_pi_apply _).comp measurable_fst)
          ((measurable_pi_apply j).comp measurable_fst)) measurable_const measurable_const
  have hcnt_meas : ∀ (P : Fin d → (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ → Prop)
      [∀ j x, Decidable (P j x)],
      (∀ j, MeasurableSet {x | P j x}) →
      Measurable (fun x : (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ =>
        ((H₀ᶜ.filter (fun j => P j x)).card : ℝ)) := by
    intro P _ hP
    apply measurable_from_top.comp
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.measurable_sum _ fun j _ =>
      Measurable.ite (hP j) measurable_const measurable_const
  have hGmeas : Measurable G := by
    simp only [G]
    by_cases h : n < d
    · simp only [h, if_true]
      apply Measurable.div
      · apply Measurable.add
        · apply Measurable.add (measurable_snd.comp (measurable_snd.comp measurable_snd))
          exact hcnt_meas _ fun j => (measurableSet_lt measurable_const (hrank_meas j)).inter
            (measurableSet_eq_fun ((measurable_pi_apply j).comp
              (measurable_fst.comp measurable_snd)) measurable_const)
        · exact measurable_const
      · refine Measurable.max (Measurable.add
          (measurable_fst.comp (measurable_snd.comp measurable_snd)) ?_) measurable_const
        exact hcnt_meas _ fun j => (measurableSet_lt measurable_const (hrank_meas j)).inter
          ((measurableSet_eq_fun ((measurable_pi_apply j).comp
            (measurable_fst.comp measurable_snd)) measurable_const).inter
            (measurableSet_eq_fun ((measurable_pi_apply j).comp measurable_fst)
              measurable_const).compl)
    · simp only [h, if_false]; exact measurable_const
  -- The process value equals `G (cproc n)`.
  have hval : (fun ω => if h : n < d then FDPhat W (θ W ⟨n, h⟩ ω) ω else α - 1)
      = G ∘ cproc W H₀ n := by
    funext ω
    simp only [Function.comp_apply, G, cproc]
    by_cases h : n < d
    · simp only [h, ↓reduceDIte, if_true]
      have hrankθ : ∀ j, θ W ⟨n, h⟩ ω ≤ |W j ω| ↔ n < rank (fun j => |W j ω|) j := by
        intro j; exact orderStat_le_iff_card_lt _ ⟨n, h⟩ _
      have hpos : ∀ j ∈ H₀ᶜ, (θ W ⟨n, h⟩ ω ≤ |W j ω| ∧ 0 < W j ω) ↔
          (n < rank (fun j => |W j ω|) j ∧
            (if j ∈ H₀ then (0:ℝ) else sgnReal W j ω) = 1 ∧ |W j ω| ≠ 0) := by
        intro j hj
        rw [Finset.mem_compl] at hj
        rw [hrankθ j, if_neg hj]
        refine and_congr_right (fun _ => ?_)
        constructor
        · intro hp; exact ⟨if_pos hp.le, by positivity⟩
        · rintro ⟨hs, hne⟩
          have h0 : 0 ≤ W j ω := by by_contra hc; rw [sgnReal, if_neg hc] at hs; norm_num at hs
          rcases lt_or_eq_of_le h0 with hlt | heq
          · exact hlt
          · exact absurd (by rw [← heq]; simp) hne
      have hneg : ∀ j ∈ H₀ᶜ, (θ W ⟨n, h⟩ ω ≤ |W j ω| ∧ W j ω < 0) ↔
          (n < rank (fun j => |W j ω|) j ∧ (if j ∈ H₀ then (0:ℝ) else sgnReal W j ω) = -1) := by
        intro j hj
        rw [Finset.mem_compl] at hj
        rw [hrankθ j, if_neg hj, sgnReal]
        refine and_congr_right (fun _ => ?_)
        constructor
        · intro hlt; rw [if_neg (not_le.mpr hlt)]
        · intro hs; by_contra hc; rw [if_pos (not_lt.mp hc)] at hs; norm_num at hs
      rw [FDPhat, Splus_card_decomp W H₀ _ ω, Sminus_card_decomp W H₀ _ ω,
        Finset.filter_congr hpos, Finset.filter_congr hneg]
      push_cast
      ring
    · simp only [h, ↓reduceDIte, if_false]
  have hsm := hGmeas.comp hc.measurable
  rw [← hval] at hsm
  exact hsm

/-- `tauStar W H₀ α` is an `IsStoppingTime` for `𝒢rev W H₀ hWmeas`, being a hitting time of an
adapted process to a measurable set.
- **USER-INPUT**: stopping-time property from `Adapted.isStoppingTime_hittingBtwn`; Lu-BDA §21.3. -/
lemma tauStar_isStoppingTime (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ)
    (hWmeas : ∀ j, Measurable (W j)) :
    IsStoppingTime (𝒢rev W H₀ hWmeas) (tauStar W H₀ α) := by
  unfold tauStar
  exact Adapted.isStoppingTime_hittingBtwn (FDPhat_atTheta_adapted W H₀ α hWmeas) measurableSet_Iic

omit mΩ in
/-- `tauStar W H₀ α ω ≤ d` for all ω: bounded by the total number of coordinates.
- **LEAN-ONLY**: from `hittingBtwn_le` applied to the hitting time bound. -/
lemma tauStar_le (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) (ω : Ω) :
    tauStar W H₀ α ω ≤ (d : ℕ∞) := by
  simp only [tauStar]
  exact WithTop.coe_le_coe.mpr (hittingBtwn_le ω)

/-! ## 6. Bridge: stoppedValue = V₊(t*)/(1+V₋(t*)) -/

omit mΩ in
/-- Every magnitude `|W j ω|` is realised as some order statistic `θ W m ω`: take `m` to be the
inverse sorting permutation applied to `j`.
- **LEAN-ONLY**: surjectivity of the order-statistic indexing onto the magnitude multiset. -/
private lemma exists_orderStat_eq_abs (W : Fin d → Ω → ℝ) (ω : Ω) (j : Fin d) :
    ∃ m : Fin d, θ W m ω = |W j ω| := by
  refine ⟨(Tuple.sort (fun i => |W i ω|)).symm j, ?_⟩
  change orderStat (fun i => |W i ω|) ((Tuple.sort (fun i => |W i ω|)).symm j) = |W j ω|
  simp only [orderStat, Equiv.apply_symm_apply]

omit mΩ in
/-- `θ W ⟨n, h⟩ ω` is one of the magnitudes `{|W j ω|}` (it is `|W·ω|` at the sorted index).
- **LEAN-ONLY**: the order statistic is a value of the magnitude tuple. -/
private lemma theta_mem_image (W : Fin d → Ω → ℝ) (ω : Ω) (n : ℕ) (h : n < d) :
    θ W ⟨n, h⟩ ω ∈ (Finset.univ : Finset (Fin d)).image (fun j => |W j ω|) := by
  rw [Finset.mem_image]
  exact ⟨Tuple.sort (fun i => |W i ω|) ⟨n, h⟩, Finset.mem_univ _, rfl⟩

/-- Order-statistic bridge: the V₊/V₋ ratio at `tStar` equals `Yproc` at the hitting index.
The argument: FDPhat is a step-function of all magnitudes; its minimizer over `{|W j|}` with
FDPhat ≤ α (the threshold `tStar`) is itself one of the order statistics `θ_k` (now ranging over
**all `d`** magnitudes), and is exactly the magnitude at the first hitting index `k` found by
`hittingBtwn`. There `V₊(tStar) = V₊(θ_k)` and `V₋(tStar) = V₋(θ_k)`, so
`V₊(tStar)/(1+V₋(tStar)) = V₊(θ_k)/(1+V₋(θ_k)) = Yproc k ω`.
- **USER-INPUT**: order-statistic analysis; Lu-BDA §21.3 (Candès STATS-300C §11.5). -/
private lemma ratio_eq_Yproc_hittingIdx
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) (ω : Ω) :
    (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) =
    Yproc W H₀
      (hittingBtwn
        (fun (n : ℕ) (ω : Ω) => if h : n < d then FDPhat W (θ W ⟨n, h⟩ ω) ω else α - 1)
        (Set.Iic α) 0 d ω) ω := by
  -- The FDPhat-at-θ process `P` and its hitting index `k` over the magnitude order statistics.
  set P : ℕ → Ω → ℝ :=
    (fun (n : ℕ) (ω : Ω) => if h : n < d then FDPhat W (θ W ⟨n, h⟩ ω) ω else α - 1) with hP_def
  set k : ℕ := hittingBtwn P (Set.Iic α) 0 d ω with hk_def
  -- The candidate magnitudes `tStar` minimises over.
  obtain ⟨cands, hcands⟩ :
      ∃ c : Finset ℝ, c = ((Finset.univ : Finset (Fin d)).image (fun j => |W j ω|)).filter
        (fun t => FDPhat W t ω ≤ α) := ⟨_, rfl⟩
  have mem_cands : ∀ x, x ∈ cands ↔
      x ∈ (Finset.univ : Finset (Fin d)).image (fun j => |W j ω|) ∧ FDPhat W x ω ≤ α := fun x => by
    rw [hcands]; exact Finset.mem_filter
  have htStar_eq : tStar W α ω =
      if h : cands.Nonempty then cands.min' h else 1 + ∑ j, |W j ω| := by
    rw [hcands]; rfl
  -- `P` evaluated on the two branches of its dependent `if`.
  have hPval : ∀ (n : ℕ) (h : n < d), P n ω = FDPhat W (θ W ⟨n, h⟩ ω) ω := fun n h => by
    simp only [hP_def]; exact dif_pos h
  have hPd : P d ω = α - 1 := by simp only [hP_def]; exact dif_neg (lt_irrefl d)
  -- There is always a hit (at `n = d`, where `P d ω = α - 1 ≤ α`); hence `k ≤ d` and `P k ω ≤ α`.
  have hExists : ∃ j ∈ Set.Icc (0 : ℕ) d, P j ω ∈ Set.Iic α := by
    refine ⟨d, Set.mem_Icc.mpr ⟨Nat.zero_le d, le_refl d⟩, ?_⟩
    rw [Set.mem_Iic, hPd]; linarith
  have hk_le : k ≤ d := by rw [hk_def]; exact hittingBtwn_le ω
  have hPk_le : P k ω ≤ α := by
    have h := hittingBtwn_mem_set hExists
    rw [← hk_def] at h
    exact Set.mem_Iic.mp h
  by_cases hne : cands.Nonempty
  · -- Non-degenerate: `tStar = min cands`; show the hitting index `k < d` and `θ_k = tStar`.
    obtain ⟨j₁, -, hj₁⟩ :
        ∃ j ∈ (Finset.univ : Finset (Fin d)), |W j ω| = cands.min' hne :=
      Finset.mem_image.mp ((mem_cands _).mp (Finset.min'_mem cands hne)).1
    obtain ⟨m₁, hθm₁⟩ := exists_orderStat_eq_abs W ω j₁
    have hθm₁' : θ W m₁ ω = cands.min' hne := hθm₁.trans hj₁
    -- `FDPhat(θ_{m₁}) = FDPhat(tStar) ≤ α`, so `m₁` is in the hitting set ⇒ `k ≤ m₁ < d`.
    have hPm₁mem : P m₁.val ω ∈ Set.Iic α := by
      rw [Set.mem_Iic, hPval m₁.val m₁.isLt,
        show θ W ⟨m₁.val, m₁.isLt⟩ ω = cands.min' hne from hθm₁']
      exact ((mem_cands _).mp (Finset.min'_mem cands hne)).2
    have hk_m₁ : k ≤ m₁.val := by
      rw [hk_def]
      exact hittingBtwn_le_of_mem (Nat.zero_le m₁.val) (le_of_lt m₁.isLt) hPm₁mem
    have hk_lt : k < d := lt_of_le_of_lt hk_m₁ m₁.isLt
    -- `tStar ≤ θ_k`: `θ_k` is a candidate (magnitude with `FDPhat ≤ α`), and `tStar = min cands`.
    have hFDPk : FDPhat W (θ W ⟨k, hk_lt⟩ ω) ω ≤ α := by rw [← hPval k hk_lt]; exact hPk_le
    have hθk_cands : θ W ⟨k, hk_lt⟩ ω ∈ cands :=
      (mem_cands _).mpr ⟨theta_mem_image W ω k hk_lt, hFDPk⟩
    have h1 : cands.min' hne ≤ θ W ⟨k, hk_lt⟩ ω := Finset.min'_le cands _ hθk_cands
    -- `θ_k ≤ tStar = θ_{m₁}` by monotonicity of the order statistics (`k ≤ m₁`).
    have hfin_le : (⟨k, hk_lt⟩ : Fin d) ≤ m₁ := by rw [Fin.le_iff_val_le_val]; exact hk_m₁
    have h2 : θ W ⟨k, hk_lt⟩ ω ≤ cands.min' hne := by
      rw [← hθm₁']; exact orderStat_monotone (fun i => |W i ω|) hfin_le
    have key : cands.min' hne = θ W ⟨k, hk_lt⟩ ω := le_antisymm h1 h2
    rw [htStar_eq, dif_pos hne, key]
    have hRHS : Yproc W H₀ k ω =
        (Vplus W H₀ (θ W ⟨k, hk_lt⟩ ω) ω : ℝ) / (1 + (Vminus W H₀ (θ W ⟨k, hk_lt⟩ ω) ω : ℝ)) := by
      unfold Yproc; rw [dif_pos hk_lt]
    rw [hRHS]
  · -- Degenerate: no candidate, `tStar = 1 + ∑|W|` exceeds every magnitude, `k = d`, both sides 0.
    have hk_eq_d : k = d := by
      rcases hk_le.lt_or_eq with hlt | heq
      · exact absurd ⟨θ W ⟨k, hlt⟩ ω,
          (mem_cands _).mpr ⟨theta_mem_image W ω k hlt,
            by rw [← hPval k hlt]; exact hPk_le⟩⟩ hne
      · exact heq
    -- `tStar = 1 + ∑|W|` strictly exceeds every magnitude `|W j ω|`.
    have htStar_gt : ∀ j : Fin d, |W j ω| < 1 + ∑ i, |W i ω| := fun j => by
      have hle : |W j ω| ≤ ∑ i, |W i ω| :=
        Finset.single_le_sum (fun i _ => abs_nonneg (W i ω)) (Finset.mem_univ j)
      linarith
    have hSplus_empty : Splus W (1 + ∑ j, |W j ω|) ω = ∅ := by
      unfold Splus
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      rw [Finset.mem_filter] at hj
      exact absurd hj.2.1 (not_le.mpr (htStar_gt j))
    have hSminus_empty : Sminus W (1 + ∑ j, |W j ω|) ω = ∅ := by
      unfold Sminus
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      rw [Finset.mem_filter] at hj
      exact absurd hj.2.1 (not_le.mpr (htStar_gt j))
    have hVplus0 : Vplus W H₀ (1 + ∑ j, |W j ω|) ω = 0 := by
      unfold Vplus; rw [hSplus_empty, Finset.empty_inter, Finset.card_empty]
    have hVminus0 : Vminus W H₀ (1 + ∑ j, |W j ω|) ω = 0 := by
      unfold Vminus; rw [hSminus_empty, Finset.empty_inter, Finset.card_empty]
    have hYd : Yproc W H₀ d ω = 0 := by simp [Yproc]
    rw [htStar_eq, dif_neg hne, hk_eq_d, hYd, hVplus0, hVminus0]
    norm_num

/-- The stopped value `stoppedValue (Yproc W H₀) (tauStar W H₀ α) ω` equals the ratio
`V₊(tStar W α ω)/(1+V₋(tStar W α ω))`: unfolding `stoppedValue` and `tauStar` reduces the
claim to `ratio_eq_Yproc_hittingIdx` via `(↑k : ℕ∞).untopA = k` (`WithTop.untopD_coe`).
- **USER-INPUT**: bridge between the Yproc index space and the tStar threshold value; Lu-BDA §21.3. -/
lemma ratio_eq_stoppedValue (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) (ω : Ω) :
    (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) =
    stoppedValue (Yproc W H₀) (tauStar W H₀ α) ω := by
  -- stoppedValue u τ ω = u (τ ω).untopA ω; tauStar ω = ↑(hittingBtwn ... ω);
  -- (↑k : ℕ∞).untopA = k is definitional (untopA = untopD arbitary; match on `some k` = k).
  unfold stoppedValue tauStar
  exact ratio_eq_Yproc_hittingIdx W H₀ α ω

/-! ## 7. Master theorem -/

/-- **Master inequality** (Lu-BDA §21.3): `E[V₊(t*)/(1+V₋(t*))] ≤ 1`, by exhibiting the
threshold-indexed ratio as a supermartingale (one-step inequality from the exchangeable null-sign
field) and applying optional stopping (`supermartingale_integral_stoppedValue_le`) plus the
initial bound `knockoff_initial_le`. -/
theorem knockoff_ratio_stopped_le_one (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℝ)
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ)
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) :
    ∫ ω, (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) ∂μ ≤ 1 := by
  haveI : SigmaFiniteFiltration μ (𝒢rev W H₀ hW.meas) := inferInstance
  have h_ratio_eq :
      ∫ ω, (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) ∂μ =
      ∫ ω, stoppedValue (Yproc W H₀) (tauStar W H₀ α) ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall (ratio_eq_stoppedValue W H₀ α))
  rw [h_ratio_eq]
  calc ∫ ω, stoppedValue (Yproc W H₀) (tauStar W H₀ α) ω ∂μ
      ≤ ∫ ω, Yproc W H₀ 0 ω ∂μ :=
          supermartingale_integral_stoppedValue_le
            (knockoff_supermartingale W H₀ μ hW hmag)
            (tauStar_isStoppingTime W H₀ α hW.meas)
            (tauStar_le W H₀ α)
    _ = ∫ ω, (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall (Yproc_zero_eq W H₀))
    _ ≤ 1 := knockoff_initial_le μ W H₀ hW

end StatLean.MultipleTesting
