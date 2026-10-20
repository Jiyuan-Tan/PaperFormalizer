module
public import StatLean.ConcentrationInequalities.Chaining.FinsetMaximal

@[expose] public section

/-!
# Countable-supremum lift engines

Index-polymorphic monotone-convergence engines turning **per-finite-subset**
bounds into **countable-supremum** bounds, in the junk-free carriers:

* `lintegral_biSup_le_of_forall_finset` — if
  `∫⁻ ⨆_{i∈F} g_i ≤ B` for every finite `F ⊆ C`, then
  `∫⁻ ⨆_{i∈C} g_i ≤ B` for countable `C` (`g` valued in `ℝ≥0∞`);
* `measure_exists_lt_le_of_forall_finset` (and its pair variant) — a uniform
  per-finite-window tail bound `μ{thr < max_F f} ≤ β` passes to the event
  that SOME member (pair) of the countable family exceeds the threshold;
* Bochner bridges `integrable_biSup_of_lintegral_biSup_ne_top` /
  `integral_biSup_le_of_lintegral_biSup_le` recovering real-integral displays
  from the `ℝ≥0∞` primaries under a `≠ ⊤` guard;
* pointwise plumbing: `lintegral_biSup_finset_ofReal_eq` (finite
  `⨆ ENNReal.ofReal` ↔ `ENNReal.ofReal ∘ ∫ Finset.sup'`),
  `toReal_biSup_ofReal` (the one infinite `ofReal`/`⨆` commutation, guarded),
  and the threshold bridges `exists_lt_of_lt_biSup_real` /
  `exists_pair_lt_of_lt_biSup_real` absorbing the `Real.sSup` junk value.

These generalize the two lifts previously inlined in
`dudley_inequality_countable` (`Chaining/Dudley.lean`) and
`dudley_tail_three_term_countable` (`Chaining/DudleyTail.lean`), and the
class-specific `integral_biSup_le_of_forall_finset` of the VC cluster.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Remark 7.2.1 and the p. 227 footnote ("the
general case typically follows by approximation"): these engines are the
approximation step, shared by every countable/separable supremum form of the
chaining batch.

**Proof formalization notes.** No probability hypothesis anywhere — the
engines hold for an arbitrary measure (`B = ⊤` and `C = ∅` branches are
trivial). The tail engines conclude on the **existential** event
`{ω | ∃ i ∈ C, thr < f i ω}`, deliberately junk-free (no real supremum in
the statement); the formal-`⨆` displays are recovered downstream through
`exists_lt_of_lt_biSup_real`, whose `0 ≤ c` hypothesis absorbs the
`Real.sSup ∅ = 0` junk branch. Monotone convergence runs along the prefix
exhaustion `S n := (Finset.range (n+1)).image f` of an enumeration
(`Set.Countable.exists_eq_range`); events use
`tendsto_measure_iUnion_atTop` (measures are continuous from below on
arbitrary monotone sequences). Named-sorry fallback of this work item:
`toReal_biSup_ofReal` (the guarded `ofReal`/`⨆` commutation).

**Bibliographic comments.** The finite-subset reading of `E sup` is standard
in the chaining literature (Talagrand, *Upper and Lower Bounds for
Stochastic Processes*, Springer 2014, §2.2); the monotone-convergence lift
to countable index sets is folklore.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Countable-sup lift engine, lintegral form** (sup policy): if every
finite subfamily's `∫⁻`-sup obeys a bound `B : ℝ≥0∞`, so does the countable
family's — monotone convergence along a prefix exhaustion. Index-polymorphic
`ℝ≥0∞` twin of the VC cluster's `integral_biSup_le_of_forall_finset`; no
probability hypothesis, and the `C = ∅` / `B = ⊤` corners are trivial. -/
lemma lintegral_biSup_le_of_forall_finset {ι : Type*} {g : ι → Ω → ℝ≥0∞}
    {C : Set ι}
    -- LEAN-ONLY: countable index family per the sup policy
    (hcnt : C.Countable)
    -- LEAN-ONLY: a.e.-measurability of each coordinate (MCT)
    (hmeas : ∀ i ∈ C, AEMeasurable (g i) μ)
    {B : ℝ≥0∞}
    -- LEAN-ONLY: the per-finite-subfamily bound being lifted
    (hB : ∀ F : Finset ι, ↑F ⊆ C → F.Nonempty →
      ∫⁻ ω, ⨆ i ∈ F, g i ω ∂μ ≤ B) :
    ∫⁻ ω, ⨆ i ∈ C, g i ω ∂μ ≤ B := by
  classical
  rcases Set.eq_empty_or_nonempty C with rfl | hCne
  · have hz : ∀ ω, (⨆ i ∈ (∅ : Set ι), g i ω) = 0 := by intro ω; simp
    simp only [hz, lintegral_zero]
    exact (zero_le (a := B))
  -- Prefix exhaustion of the countable index set by finite windows.
  obtain ⟨e, he⟩ := hcnt.exists_eq_range hCne
  set S : ℕ → Finset ι := fun n => (Finset.range (n + 1)).image e with hSdef
  have hSne : ∀ n, (S n).Nonempty := fun n =>
    ⟨e 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos n), rfl⟩⟩
  have hSsub : ∀ n, (↑(S n) : Set ι) ⊆ C := by
    intro n x hx
    simp only [hSdef, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_range] at hx
    obtain ⟨k, _, hk⟩ := hx
    rw [he]; exact ⟨k, hk⟩
  have hSmono : ∀ a b : ℕ, a ≤ b → S a ⊆ S b := by
    intro a b hab x hx
    simp only [hSdef, Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨k, hk, hkx⟩ := hx
    exact ⟨k, by omega, hkx⟩
  have hUnion : (⋃ n, (↑(S n) : Set ι)) = C := by
    refine Set.Subset.antisymm (Set.iUnion_subset hSsub) ?_
    rw [he]
    rintro x ⟨k, rfl⟩
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    exact Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), rfl⟩)
  -- The monotone-convergence integrand family.
  set Φ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨆ i ∈ (↑(S n) : Set ι), g i ω with hΦ
  have hΦmeas : ∀ n, AEMeasurable (Φ n) μ := fun n =>
    AEMeasurable.biSup (↑(S n) : Set ι) (S n).countable_toSet
      fun i hi => hmeas i (hSsub n hi)
  have hΦmono : ∀ ω, Monotone fun n => Φ n ω := by
    intro ω m n hmn
    simp only [hΦ]
    exact iSup_le_iSup_of_subset (Finset.coe_subset.mpr (hSmono m n hmn))
  have hA : ∀ ω, (⨆ i ∈ C, g i ω) = ⨆ n, Φ n ω := by
    intro ω
    rw [← hUnion, iSup_iUnion]
  calc ∫⁻ ω, ⨆ i ∈ C, g i ω ∂μ = ∫⁻ ω, ⨆ n, Φ n ω ∂μ := lintegral_congr hA
    _ = ⨆ n, ∫⁻ ω, Φ n ω ∂μ := lintegral_iSup' hΦmeas (ae_of_all _ hΦmono)
    _ ≤ B := by
        refine iSup_le fun n => ?_
        have hn := hB (S n) (hSsub n) (hSne n)
        simpa only [hΦ, Finset.iSup_coe] using hn

/-- **Countable-sup lift engine, tail form** (sup policy): a uniform
per-finite-window tail bound at a fixed threshold passes to the event that
SOME member of the countable family exceeds the threshold — continuity of
the measure from below along the windows. The existential event is
deliberately junk-free (no real supremum appears); combine with
`exists_lt_of_lt_biSup_real` to bound formal-`⨆` events. -/
lemma measure_exists_lt_le_of_forall_finset {ι : Type*} {f : ι → Ω → ℝ}
    {C : Set ι}
    -- LEAN-ONLY: countable index family per the sup policy
    (hcnt : C.Countable)
    {thr : ℝ} {β : ℝ≥0∞}
    -- LEAN-ONLY: the per-finite-window tail bound being lifted
    (hB : ∀ (F : Finset ι) (hFne : F.Nonempty), ↑F ⊆ C →
      μ {ω | thr < F.sup' hFne fun i => f i ω} ≤ β) :
    μ {ω | ∃ i ∈ C, thr < f i ω} ≤ β := by
  classical
  rcases Set.eq_empty_or_nonempty C with rfl | hCne
  · have hE : {ω | ∃ i ∈ (∅ : Set ι), thr < f i ω} = (∅ : Set Ω) := by
      ext ω; simp
    rw [hE, measure_empty]
    exact (zero_le (a := β))
  -- Finite exhaustion of the countable carrier.
  obtain ⟨e, he⟩ := hcnt.exists_eq_range hCne
  set S : ℕ → Finset ι := fun n => (Finset.range (n + 1)).image e with hSdef
  have hSne : ∀ n, (S n).Nonempty := fun n =>
    ⟨e 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos n), rfl⟩⟩
  have hSsub : ∀ n, (↑(S n) : Set ι) ⊆ C := by
    intro n x hx
    simp only [hSdef, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_range] at hx
    obtain ⟨k, _, hk⟩ := hx
    rw [he]; exact ⟨k, hk⟩
  have hSmono : ∀ a b : ℕ, a ≤ b → S a ⊆ S b := by
    intro a b hab x hx
    simp only [hSdef, Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨k, hk, hkx⟩ := hx
    exact ⟨k, by omega, hkx⟩
  set B : ℕ → Set Ω := fun n => {ω | thr < (S n).sup' (hSne n) fun i => f i ω}
    with hBdef
  have hBmono : Monotone B := by
    intro a b hab ω hω
    simp only [hBdef, Set.mem_setOf_eq] at hω ⊢
    refine lt_of_lt_of_le hω (Finset.sup'_le (hSne a) _ fun i hi => ?_)
    exact Finset.le_sup' (fun i => f i ω) (hSmono a b hab hi)
  have hincl : {ω | ∃ i ∈ C, thr < f i ω} ⊆ ⋃ n, B n := by
    intro ω hω
    obtain ⟨i, hiC, hlt⟩ := hω
    rw [he] at hiC
    obtain ⟨k, hk⟩ := hiC
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    simp only [hBdef, Set.mem_setOf_eq]
    have hiS : i ∈ S k :=
      Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), hk⟩
    exact lt_of_lt_of_le hlt (Finset.le_sup' (fun i => f i ω) hiS)
  calc μ {ω | ∃ i ∈ C, thr < f i ω} ≤ μ (⋃ n, B n) := measure_mono hincl
    _ ≤ β := le_of_tendsto (tendsto_measure_iUnion_atTop hBmono)
        (Filter.Eventually.of_forall fun n => hB (S n) (hSne n) (hSsub n))

/-- Pair variant of `measure_exists_lt_le_of_forall_finset`: per-window
bounds on the product maximum `(F ×ˢ F).sup'` lift to the event that some
PAIR of the countable family exceeds the threshold (the shape of
Eq. (8.15)). -/
lemma measure_exists_pair_lt_le_of_forall_finset {ι : Type*}
    {f : ι → ι → Ω → ℝ} {C : Set ι}
    -- LEAN-ONLY: countable index family per the sup policy
    (hcnt : C.Countable)
    {thr : ℝ} {β : ℝ≥0∞}
    -- LEAN-ONLY: the per-finite-window pair tail bound being lifted
    (hB : ∀ (F : Finset ι) (hFne : F.Nonempty), ↑F ⊆ C →
      μ {ω | thr < (F ×ˢ F).sup' (hFne.product hFne) fun p => f p.1 p.2 ω}
        ≤ β) :
    μ {ω | ∃ i ∈ C, ∃ j ∈ C, thr < f i j ω} ≤ β := by
  classical
  rcases Set.eq_empty_or_nonempty C with rfl | hCne
  · have hE : {ω | ∃ i ∈ (∅ : Set ι), ∃ j ∈ (∅ : Set ι), thr < f i j ω}
        = (∅ : Set Ω) := by
      ext ω; simp
    rw [hE, measure_empty]
    exact (zero_le (a := β))
  -- Finite exhaustion of the countable carrier.
  obtain ⟨e, he⟩ := hcnt.exists_eq_range hCne
  set S : ℕ → Finset ι := fun n => (Finset.range (n + 1)).image e with hSdef
  have hSne : ∀ n, (S n).Nonempty := fun n =>
    ⟨e 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos n), rfl⟩⟩
  have hSsub : ∀ n, (↑(S n) : Set ι) ⊆ C := by
    intro n x hx
    simp only [hSdef, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_range] at hx
    obtain ⟨k, _, hk⟩ := hx
    rw [he]; exact ⟨k, hk⟩
  have hSmono : ∀ a b : ℕ, a ≤ b → S a ⊆ S b := by
    intro a b hab x hx
    simp only [hSdef, Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨k, hk, hkx⟩ := hx
    exact ⟨k, by omega, hkx⟩
  set B : ℕ → Set Ω := fun n => {ω | thr < (S n ×ˢ S n).sup'
    ((hSne n).product (hSne n)) fun p => f p.1 p.2 ω} with hBdef
  have hBmono : Monotone B := by
    intro a b hab ω hω
    simp only [hBdef, Set.mem_setOf_eq] at hω ⊢
    refine lt_of_lt_of_le hω
      (Finset.sup'_le ((hSne a).product (hSne a)) _ fun p hp => ?_)
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact Finset.le_sup' (fun p => f p.1 p.2 ω)
      (Finset.mem_product.mpr ⟨hSmono a b hab hp1, hSmono a b hab hp2⟩)
  have hincl : {ω | ∃ i ∈ C, ∃ j ∈ C, thr < f i j ω} ⊆ ⋃ n, B n := by
    intro ω hω
    obtain ⟨i, hiC, j, hjC, hlt⟩ := hω
    rw [he] at hiC hjC
    obtain ⟨k, hk⟩ := hiC
    obtain ⟨l, hl⟩ := hjC
    refine Set.mem_iUnion.mpr ⟨max k l, ?_⟩
    simp only [hBdef, Set.mem_setOf_eq]
    have hiS : i ∈ S (max k l) := Finset.mem_image.mpr
      ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_left k l)), hk⟩
    have hjS : j ∈ S (max k l) := Finset.mem_image.mpr
      ⟨l, Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_right k l)), hl⟩
    have hp : (i, j) ∈ S (max k l) ×ˢ S (max k l) :=
      Finset.mem_product.mpr ⟨hiS, hjS⟩
    exact lt_of_lt_of_le hlt (Finset.le_sup' (fun p => f p.1 p.2 ω) hp)
  calc μ {ω | ∃ i ∈ C, ∃ j ∈ C, thr < f i j ω} ≤ μ (⋃ n, B n) := measure_mono hincl
    _ ≤ β := le_of_tendsto (tendsto_measure_iUnion_atTop hBmono)
        (Filter.Eventually.of_forall fun n => hB (S n) (hSne n) (hSsub n))

/-- Finite `⨆ ENNReal.ofReal` as `ENNReal.ofReal` of the Bochner integral of
the `Finset.sup'` carrier: the per-level bridge between the engine's
integrand and the per-finite-subset theorems. The sup'-level sign hypothesis
is sharp — anchored families have negative members but a `0`-valued member
at the anchor. -/
lemma lintegral_biSup_finset_ofReal_eq {ι : Type*} {F : Finset ι}
    (hFne : F.Nonempty) {f : ι → Ω → ℝ}
    -- LEAN-ONLY: nonnegative finite maximum (sharp junk guard)
    (h0 : ∀ ω, 0 ≤ F.sup' hFne fun i => f i ω)
    -- LEAN-ONLY: integrability of the finite maximum (ψ₂ or per-coordinate)
    (hInt : MeasureTheory.Integrable (fun ω => F.sup' hFne fun i => f i ω) μ) :
    ∫⁻ ω, ⨆ i ∈ F, ENNReal.ofReal (f i ω) ∂μ
      = ENNReal.ofReal (∫ ω, F.sup' hFne (fun i => f i ω) ∂μ) := by
  classical
  have hpt : ∀ ω, (⨆ i ∈ F, ENNReal.ofReal (f i ω))
      = ENNReal.ofReal (F.sup' hFne fun i => f i ω) := by
    intro ω
    rw [Finset.comp_sup'_eq_sup'_comp hFne ENNReal.ofReal
        (fun x y => ENNReal.ofReal_max x y),
      Finset.sup'_eq_sup, Finset.sup_eq_iSup]
    rfl
  calc ∫⁻ ω, ⨆ i ∈ F, ENNReal.ofReal (f i ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (F.sup' hFne fun i => f i ω) ∂μ := lintegral_congr hpt
    _ = ENNReal.ofReal (∫ ω, F.sup' hFne (fun i => f i ω) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ h0)).symm

/-- Auxiliary: a real set-bounded supremum of a nonnegative family is
nonnegative — every junk branch (`i ∉ C`, empty index type, unbounded family)
evaluates to `Real.sSup ∅ = 0`. -/
private lemma biSup_nonneg_of_mem {ι : Type*} {C : Set ι} {h : ι → ℝ}
    (h0 : ∀ i ∈ C, 0 ≤ h i) : 0 ≤ ⨆ i ∈ C, h i := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Real.iSup_of_isEmpty]
  by_cases hbdd : BddAbove (Set.range fun i => ⨆ (_ : i ∈ C), h i)
  · obtain ⟨i₀⟩ := hι
    refine le_ciSup_of_le hbdd i₀ ?_
    by_cases hi : i₀ ∈ C
    · rw [ciSup_pos hi]; exact h0 _ hi
    · haveI : IsEmpty (i₀ ∈ C) := ⟨hi⟩
      rw [Real.iSup_of_isEmpty]
  · rw [Real.iSup_of_not_bddAbove hbdd]

/-- The guarded infinite `ofReal`/`⨆` commutation: for a nonnegative family
with finite `ℝ≥0∞`-supremum, `toReal` of the `⨆ ENNReal.ofReal` recovers the
real supremum. (Mathlib has no `ENNReal.ofReal_iSup`; the `≠ ⊤` guard is
what makes this true — an unbounded family junks the real side to `0` while
the `ℝ≥0∞` side is honestly `⊤`.) -/
lemma toReal_biSup_ofReal {ι : Type*} {C : Set ι} {h : ι → ℝ}
    -- LEAN-ONLY: nonnegative family (junk alignment)
    (h0 : ∀ i ∈ C, 0 ≤ h i)
    -- LEAN-ONLY: finite ℝ≥0∞ supremum (the commutation guard)
    (htop : (⨆ i ∈ C, ENNReal.ofReal (h i)) ≠ ⊤) :
    (⨆ i ∈ C, ENNReal.ofReal (h i)).toReal = ⨆ i ∈ C, h i := by
  classical
  -- Each member is dominated by `toReal` of the (finite) `ℝ≥0∞` supremum.
  have hmem : ∀ i ∈ C, h i ≤ (⨆ i ∈ C, ENNReal.ofReal (h i)).toReal := by
    intro i hi
    have hle : ENNReal.ofReal (h i) ≤ ⨆ i ∈ C, ENNReal.ofReal (h i) :=
      le_iSup₂ (f := fun i (_ : i ∈ C) => ENNReal.ofReal (h i)) i hi
    have := ENNReal.toReal_mono htop hle
    rwa [ENNReal.toReal_ofReal (h0 i hi)] at this
  -- Hence every branch of the real supremum is dominated, giving `≤`.
  have hbranch : ∀ i, (⨆ (_ : i ∈ C), h i)
      ≤ (⨆ i ∈ C, ENNReal.ofReal (h i)).toReal := by
    intro i
    by_cases hi : i ∈ C
    · rw [ciSup_pos hi]; exact hmem i hi
    · haveI : IsEmpty (i ∈ C) := ⟨hi⟩
      rw [Real.iSup_of_isEmpty]; exact ENNReal.toReal_nonneg
  have hbdd : BddAbove (Set.range fun i => ⨆ (_ : i ∈ C), h i) :=
    ⟨(⨆ i ∈ C, ENNReal.ofReal (h i)).toReal, by rintro y ⟨i, rfl⟩; exact hbranch i⟩
  have hle₁ : (⨆ i ∈ C, h i) ≤ (⨆ i ∈ C, ENNReal.ofReal (h i)).toReal :=
    Real.iSup_le hbranch ENNReal.toReal_nonneg
  -- The reverse direction: the real supremum dominates every member.
  have hmem' : ∀ i ∈ C, h i ≤ ⨆ i ∈ C, h i := by
    intro i hi
    exact le_ciSup_of_le hbdd i (le_of_eq (ciSup_pos (f := fun _ => h i) hi).symm)
  have hle₂ : (⨆ i ∈ C, ENNReal.ofReal (h i)) ≤ ENNReal.ofReal (⨆ i ∈ C, h i) :=
    iSup₂_le fun i hi => ENNReal.ofReal_le_ofReal (hmem' i hi)
  refine le_antisymm ?_ hle₁
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle₂
  rwa [ENNReal.toReal_ofReal (biSup_nonneg_of_mem h0)] at this

/-- Strict nonnegative thresholds pierce a real bounded supremum: the `0 ≤ c`
hypothesis absorbs the `Real.sSup` junk value (an unbounded or empty family
junks the supremum to `0 ≤ c`, contradicting the strict inequality). -/
lemma exists_lt_of_lt_biSup_real {ι : Type*} {S : Set ι} {h : ι → ℝ} {c : ℝ}
    -- LEAN-ONLY: nonnegative threshold (absorbs the `Real.sSup ∅ = 0` junk)
    (hc : 0 ≤ c)
    (hlt : c < ⨆ i ∈ S, h i) :
    ∃ i ∈ S, c < h i := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Real.iSup_of_isEmpty] at hlt; linarith
  obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup hlt
  by_cases hiS : i ∈ S
  · rw [ciSup_pos hiS] at hi
    exact ⟨i, hiS, hi⟩
  · haveI : IsEmpty (i ∈ S) := ⟨hiS⟩
    rw [Real.iSup_of_isEmpty] at hi
    linarith

/-- Pair version of `exists_lt_of_lt_biSup_real` for nested double suprema. -/
lemma exists_pair_lt_of_lt_biSup_real {ι : Type*} {S : Set ι}
    {h : ι → ι → ℝ} {c : ℝ}
    -- LEAN-ONLY: nonnegative threshold (absorbs the `Real.sSup ∅ = 0` junk)
    (hc : 0 ≤ c)
    (hlt : c < ⨆ i ∈ S, ⨆ j ∈ S, h i j) :
    ∃ i ∈ S, ∃ j ∈ S, c < h i j := by
  obtain ⟨i, hiS, hi⟩ := exists_lt_of_lt_biSup_real hc hlt
  obtain ⟨j, hjS, hj⟩ := exists_lt_of_lt_biSup_real hc hi
  exact ⟨i, hiS, j, hjS, hj⟩

/-- **Bochner bridge, integrability**: a countable nonnegative family whose
`⨆ ENNReal.ofReal` has finite lintegral has an integrable real supremum
(a.e. finiteness + countable measurability + `toReal_biSup_ofReal`). -/
lemma integrable_biSup_of_lintegral_biSup_ne_top {ι : Type*} {C : Set ι}
    {f : ι → Ω → ℝ}
    -- LEAN-ONLY: countable index family per the sup policy
    (hcnt : C.Countable)
    -- LEAN-ONLY: a.e.-measurability of each coordinate
    (hmeas : ∀ i ∈ C, AEMeasurable (f i) μ)
    -- LEAN-ONLY: nonnegative family (junk alignment)
    (h0 : ∀ i ∈ C, ∀ ω, 0 ≤ f i ω)
    -- LEAN-ONLY: finite lintegral of the ℝ≥0∞ primary
    (hfin : ∫⁻ ω, ⨆ i ∈ C, ENNReal.ofReal (f i ω) ∂μ ≠ ⊤) :
    MeasureTheory.Integrable (fun ω => ⨆ i ∈ C, f i ω) μ := by
  classical
  have hYmeas : AEMeasurable (fun ω => ⨆ i ∈ C, ENNReal.ofReal (f i ω)) μ :=
    AEMeasurable.biSup C hcnt fun i hi => (hmeas i hi).ennreal_ofReal
  have hint : MeasureTheory.Integrable
      (fun ω => (⨆ i ∈ C, ENNReal.ofReal (f i ω)).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hYmeas hfin
  refine hint.congr ?_
  filter_upwards [ae_lt_top' hYmeas hfin] with ω hω
  exact toReal_biSup_ofReal (fun i hi => h0 i hi ω) hω.ne

/-- **Bochner bridge, integral bound**: the real-integral display of a
countable-sup lintegral bound, under the `≠ ⊤` guard. -/
lemma integral_biSup_le_of_lintegral_biSup_le {ι : Type*} {C : Set ι}
    {f : ι → Ω → ℝ}
    -- LEAN-ONLY: countable index family per the sup policy
    (hcnt : C.Countable)
    -- LEAN-ONLY: a.e.-measurability of each coordinate
    (hmeas : ∀ i ∈ C, AEMeasurable (f i) μ)
    -- LEAN-ONLY: nonnegative family (junk alignment)
    (h0 : ∀ i ∈ C, ∀ ω, 0 ≤ f i ω)
    {B : ℝ≥0∞}
    -- LEAN-ONLY: the ℝ≥0∞ primary bound being displayed
    (hB : ∫⁻ ω, ⨆ i ∈ C, ENNReal.ofReal (f i ω) ∂μ ≤ B)
    -- LEAN-ONLY: finite bound so the real display is honest (junk-guard)
    (hBtop : B ≠ ⊤) :
    ∫ ω, ⨆ i ∈ C, f i ω ∂μ ≤ B.toReal := by
  classical
  have hfin : ∫⁻ ω, ⨆ i ∈ C, ENNReal.ofReal (f i ω) ∂μ ≠ ⊤ :=
    (hB.trans_lt (lt_top_iff_ne_top.mpr hBtop)).ne
  have hYmeas : AEMeasurable (fun ω => ⨆ i ∈ C, ENNReal.ofReal (f i ω)) μ :=
    AEMeasurable.biSup C hcnt fun i hi => (hmeas i hi).ennreal_ofReal
  have hInt : MeasureTheory.Integrable (fun ω => ⨆ i ∈ C, f i ω) μ :=
    integrable_biSup_of_lintegral_biSup_ne_top hcnt hmeas h0 hfin
  have hnn : 0 ≤ᵐ[μ] fun ω => ⨆ i ∈ C, f i ω :=
    ae_of_all _ fun ω => biSup_nonneg_of_mem fun i hi => h0 i hi ω
  rw [integral_eq_lintegral_of_nonneg_ae hnn hInt.1]
  have hcong : ∫⁻ ω, ENNReal.ofReal (⨆ i ∈ C, f i ω) ∂μ
      = ∫⁻ ω, ⨆ i ∈ C, ENNReal.ofReal (f i ω) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top' hYmeas hfin] with ω hω
    rw [← toReal_biSup_ofReal (fun i hi => h0 i hi ω) hω.ne,
      ENNReal.ofReal_toReal hω.ne]
  rw [hcong]
  exact ENNReal.toReal_mono hBtop hB

end StatLean.ConcentrationInequalities
