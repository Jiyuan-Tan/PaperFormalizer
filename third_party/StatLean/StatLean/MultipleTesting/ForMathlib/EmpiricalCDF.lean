module
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# Empirical CDF and threshold counting processes — ForMathlib brick

The empirical distribution function of finitely many real statistics and the two counting
processes the multiple-testing martingale arguments run on. For `p : Fin n → Ω → ℝ` (think:
`n` p-values) and a threshold `t : ℝ`:

* `countLE p t ω` — the **rejection count** `R(t) = #{ j : pⱼ(ω) ≤ t }`;
* `nullCountLE H₀ p t ω` — the **false-rejection count** `V(t) = #{ j ∈ H₀ : pⱼ(ω) ≤ t }` over a
  set `H₀` of true nulls;
* `empiricalCDF p t ω = R(t)/n` — the **empirical CDF** `F̂ₙ(t)`.

These feed the Benjamini–Hochberg-under-dependence, BH-via-martingale, Storey, and
Kolmogorov–Smirnov developments (Candès STAT 300C, Lectures 3, 5–7). Theorem-agnostic; the only
lemmas here are monotonicity in `t`, the `≤ n` / `V ≤ R` bounds, and measurability in `ω`.

Reference: Candès, Lecture 3 (Def. 1, empirical CDF), STAT 300C Notes.
-/

open MeasureTheory
open scoped BigOperators

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : ℕ}

/-- The rejection count `R(t) = #{ j : pⱼ(ω) ≤ t }` (Candès L3; the `R(t)` of the BH/Storey
martingale arguments). -/
noncomputable def countLE (p : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun j => p j ω ≤ t)).card

/-- The false-rejection count `V(t) = #{ j ∈ H₀ : pⱼ(ω) ≤ t }` over the true-null set `H₀`
(Candès L3, L7; the `V(t)` of the BH/Storey martingale arguments). -/
noncomputable def nullCountLE (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  (H₀.filter (fun j => p j ω ≤ t)).card

/-- The empirical CDF `F̂ₙ(t) = R(t)/n` of the statistics `p` (Candès L3, Def. 1, STAT 300C). For
`n = 0` this is `0/0 = 0`. -/
noncomputable def empiricalCDF (p : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (countLE p t ω : ℝ) / n

/-! ## Basic properties (proved on branch `mt/empirical-cdf`). -/

/-- `R(t) ≤ n`. -/
theorem countLE_le (p : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) : countLE p t ω ≤ n := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_univ]

/-- `R(·)` is monotone in the threshold. -/
theorem countLE_mono (p : Fin n → Ω → ℝ) (ω : Ω) {s t : ℝ} (hst : s ≤ t) :
    countLE p s ω ≤ countLE p t ω := by
  refine Finset.card_le_card ?_
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, le_trans hj.2 hst⟩

/-- `V(t) ≤ R(t)`: the false-rejection count is at most the rejection count. -/
theorem nullCountLE_le_countLE (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) :
    nullCountLE H₀ p t ω ≤ countLE p t ω := by
  refine Finset.card_le_card ?_
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨Finset.mem_univ j, hj.2⟩

/-- `V(·)` is monotone in the threshold. -/
theorem nullCountLE_mono (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (ω : Ω) {s t : ℝ} (hst : s ≤ t) :
    nullCountLE H₀ p s ω ≤ nullCountLE H₀ p t ω := by
  refine Finset.card_le_card ?_
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, le_trans hj.2 hst⟩

/-- For fixed `t`, the rejection count is a measurable function of `ω` when each `pⱼ` is
measurable — needed for the expectations in the martingale arguments. -/
theorem measurable_countLE (p : Fin n → Ω → ℝ) (hp : ∀ j, Measurable (p j)) (t : ℝ) :
    Measurable (fun ω => countLE p t ω) := by
  simp only [countLE, Finset.card_filter]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact Measurable.ite (measurableSet_le (hp j) measurable_const) measurable_const measurable_const

/-- For fixed `t`, the false-rejection count is a measurable function of `ω`. -/
theorem measurable_nullCountLE (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ)
    (hp : ∀ j, Measurable (p j)) (t : ℝ) :
    Measurable (fun ω => nullCountLE H₀ p t ω) := by
  simp only [nullCountLE, Finset.card_filter]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact Measurable.ite (measurableSet_le (hp j) measurable_const) measurable_const measurable_const

/-- The empirical CDF lies in `[0,1]` (for `n ≥ 1`). -/
theorem empiricalCDF_nonneg (p : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) : 0 ≤ empiricalCDF p t ω := by
  unfold empiricalCDF
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The empirical CDF is at most one. -/
theorem empiricalCDF_le_one (p : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) : empiricalCDF p t ω ≤ 1 := by
  unfold empiricalCDF
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · rw [div_le_one (by positivity)]
    exact_mod_cast countLE_le p t ω

end StatLean.MultipleTesting
