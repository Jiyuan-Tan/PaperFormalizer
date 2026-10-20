module
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences

@[expose] public section

/-!
# Sequential convergence of varying sets

The metric sequential Painlevé--Kuratowski convergence used in van der Vaart,
*Asymptotic Statistics*, Corollary 5.58.  Both halves are retained: recovery of
every limit-set point and closedness under every strictly increasing
subsequence.
-/

open Filter Topology

namespace AsymptoticStatistics.ForMathlib

/-- Sequential Painlevé--Kuratowski convergence `Hₙ → H` in a metric space.

Constitutive (vdV §5.9 p.80): `H` is exactly the collection of limits recovered
by points of `Hₙ`, and every convergent selection along an arbitrary strict
subsequence has its limit in `H`.

Edge behavior: membership is required at every natural index, not merely
eventually, so a missing finite prefix can prevent recovery.  If `H = ∅`, the
recovery clause is vacuous and the outer clause says that no subsequential
selection from the `Hₙ` can converge. -/
def SetConverges {D : Type*} [MetricSpace D]
    (Hn : ℕ → Set D) (H : Set D) : Prop :=
  (∀ h ∈ H, ∃ hn : ℕ → D, (∀ n, hn n ∈ Hn n) ∧ Tendsto hn atTop (𝓝 h)) ∧
  (∀ (φ : ℕ → ℕ), StrictMono φ → ∀ hn : ℕ → D,
    (∀ n, hn n ∈ Hn (φ n)) → ∀ h, Tendsto hn atTop (𝓝 h) → h ∈ H)

/-- The inner-recovery projection of `SetConverges`. -/
theorem SetConverges.exists_recovery {D : Type*} [MetricSpace D]
    {Hn : ℕ → Set D} {H : Set D} (hconv : SetConverges Hn H)
    {h : D} (hh : h ∈ H) :
    ∃ hn : ℕ → D, (∀ n, hn n ∈ Hn n) ∧ Tendsto hn atTop (𝓝 h) := by
  exact hconv.1 h hh

/-- The arbitrary-strict-subsequence outer projection of `SetConverges`. -/
theorem SetConverges.subsequence_limit_mem {D : Type*} [MetricSpace D]
    {Hn : ℕ → Set D} {H : Set D} (hconv : SetConverges Hn H)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {hn : ℕ → D}
    (hmem : ∀ n, hn n ∈ Hn (φ n)) {h : D}
    (hlim : Tendsto hn atTop (𝓝 h)) : h ∈ H := by
  exact hconv.2 φ hφ hn hmem h hlim

/-- A convergent full selection has its limit in the limiting set. -/
theorem SetConverges.limit_mem {D : Type*} [MetricSpace D]
    {Hn : ℕ → Set D} {H : Set D} (hconv : SetConverges Hn H)
    {hn : ℕ → D} (hmem : ∀ n, hn n ∈ Hn n) {h : D}
    (hlim : Tendsto hn atTop (𝓝 h)) : h ∈ H := by
  exact hconv.subsequence_limit_mem strictMono_id hmem hlim

/-- Set convergence is preserved by passage to a strict subsequence.

The recovery sequence for the subsequence is reselected; it is not obtained by
blindly restricting an arbitrary recovery sequence. -/
theorem SetConverges.subsequence {D : Type*} [MetricSpace D]
    {Hn : ℕ → Set D} {H : Set D} (hconv : SetConverges Hn H)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    SetConverges (fun n => Hn (φ n)) H := by
  constructor
  · intro h hh
    rcases hconv.exists_recovery hh with ⟨hn, hmem, hlim⟩
    exact ⟨hn ∘ φ, fun n => hmem (φ n), hlim.comp hφ.tendsto_atTop⟩
  · intro ψ hψ hn hmem h hlim
    exact hconv.subsequence_limit_mem (hφ.comp hψ) hmem hlim

/-- The limit of a sequentially Painlevé--Kuratowski convergent sequence of
sets is closed.  The proof diagonalizes recovery sequences for a convergent
sequence of points of `H`, then applies arbitrary-subsequence outer
closedness. -/
theorem SetConverges.limit_closed {D : Type*} [MetricSpace D]
    {Hn : ℕ → Set D} {H : Set D} (hconv : SetConverges Hn H) :
    IsClosed H := by
  apply IsSeqClosed.isClosed
  intro x h hxmem hxlim
  choose recovery hrecovery_mem hrecovery_lim using
    fun n => hconv.exists_recovery (hxmem n)
  have heventual : ∀ n, ∃ N, ∀ m ≥ N,
      dist (recovery n m) (x n) < 1 / ((n : ℝ) + 1) := fun n =>
    (Metric.tendsto_atTop.1 (hrecovery_lim n)) _ (by positivity)
  choose threshold hthreshold using heventual
  let φ : ℕ → ℕ := fun n =>
    Nat.rec (threshold 0) (fun i m => max (threshold (i + 1)) (m + 1)) n
  have hφ_succ (n : ℕ) :
      φ (n + 1) = max (threshold (n + 1)) (φ n + 1) := by
    simp [φ]
  have hthreshold_le : ∀ n, threshold n ≤ φ n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n =>
        rw [hφ_succ]
        exact Nat.le_max_left _ _
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun n => by
    rw [hφ_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self (φ n)) (Nat.le_max_right _ _)
  let diagonal : ℕ → D := fun n => recovery n (φ n)
  have hdiagonal_mem : ∀ n, diagonal n ∈ Hn (φ n) := fun n =>
    hrecovery_mem n (φ n)
  have hdiagonal_lim : Tendsto diagonal atTop (𝓝 h) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    rcases (Metric.tendsto_atTop.1 hxlim) (ε / 2) (half_pos hε) with ⟨Nx, hNx⟩
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    rcases (Metric.tendsto_atTop.1 hinv) (ε / 2) (half_pos hε) with ⟨Ne, hNe⟩
    refine ⟨max Nx Ne, fun n hn => ?_⟩
    have hxnear : dist (x n) h < ε / 2 :=
      hNx n (le_trans (Nat.le_max_left _ _) hn)
    have hinvnear : 1 / ((n : ℝ) + 1) < ε / 2 := by
      have h := hNe n (le_trans (Nat.le_max_right _ _) hn)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
      exact h
    have hdiagnear : dist (diagonal n) (x n) < ε / 2 :=
      lt_trans (hthreshold n (φ n) (hthreshold_le n)) hinvnear
    calc
      dist (diagonal n) h ≤ dist (diagonal n) (x n) + dist (x n) h := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hdiagnear hxnear
      _ = ε := by ring
  exact hconv.subsequence_limit_mem hφ hdiagonal_mem hdiagonal_lim

end AsymptoticStatistics.ForMathlib
