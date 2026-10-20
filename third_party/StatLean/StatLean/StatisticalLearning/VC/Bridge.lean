module
public import StatLean.StatisticalLearning.Rademacher.Defs
public import StatLean.StatisticalLearning.Core.SampleLaw
public import StatLean.ConcentrationInequalities.VC.SauerShelah
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Boolean classifiers ↔ set classes: the VC dictionary

The bridge between this area's learning-theoretic data model (predictors
`h : X → Bool`, 0–1 loss on pairs `X × Bool`, `risk`/`empRisk`) and the
set-class VC machinery of `ConcentrationInequalities/VC/` (`Shatters`,
`vcDim`, `traceFamily`, `empFrac` on `Set X`): the positive-set encoding of a
predictor class, the pair-space error set of a predictor, the risk/empirical
risk dictionaries, and the Sauer–Shelah trace count for the evaluated loss
family `{(𝟙[h(xᵢ)≠yᵢ])ᵢ : h ∈ 𝓗}` (SSBD §28.1 step 1: the loss vectors are
an XOR-mask of the trace vectors, so their number is bounded by the growth
function).

**Reference.** SSBD Definitions 6.2/6.3/6.5/6.9, Lemma 6.10, and §28.1
step 1. Transcriptions: `notes/statistical_learning/book_statements/ch6-28.md`.

**Formalization notes.** VC hypotheses downstream are phrased as
`vcDim (setClassOf 𝓗) ≤ d` — no new Boolean `vcDim` is introduced. The trace
bound deliberately avoids `growthFunction` (whose `ℕ∞` sup is junk `0` when
`X` has fewer than `n` points) and goes through `traceFamily` on the sample's
instance `Finset` directly, then Sauer–Shelah
(`ConcentrationInequalities/VC/SauerShelah.lean`).
-/

open MeasureTheory StatLean.ConcentrationInequalities
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {X : Type*} {n : ℕ}

/-- The positive-set encoding of a Boolean predictor class (SSBD's
identification of `h : X → {0,1}` with `{x | h(x) = 1}`). -/
def setClassOf (𝓗 : Set (X → Bool)) : Set (Set X) :=
  (fun h => {x | h x = true}) '' 𝓗

/-- The pair-space error set of a predictor: `{(x,y) | h(x) ≠ y}` — the 0–1
loss of `h` is its indicator (SSBD Eq. (3.1)). -/
def errSet (h : X → Bool) : Set (X × Bool) :=
  {p | h p.1 ≠ p.2}

/-- Risk dictionary: the 0–1 risk is the mass of the error set
(SSBD Eq. (3.1) vs Eq. (3.3), "the definitions coincide"). -/
theorem risk_zeroOneLoss_eq [MeasurableSpace X] (D : Measure (X × Bool))
    [IsProbabilityMeasure D] (h : X → Bool)
    -- USER-INPUT: measurable error set; SSBD Remark 3.1 (0–1-loss form)
    (hmeas : MeasurableSet (errSet h)) :
    risk D zeroOneLoss h = D.real (errSet h) := by
  have hfun : (fun p : X × Bool => zeroOneLoss h p) = (errSet h).indicator 1 := by
    funext p
    by_cases hp : h p.1 = p.2
    · have : p ∉ errSet h := by simpa [errSet] using hp
      simp [zeroOneLoss, hp, this]
    · have : p ∈ errSet h := by simpa [errSet] using hp
      simp [zeroOneLoss, hp, this]
  rw [risk, hfun, integral_indicator_one hmeas]

/-- Empirical-risk dictionary: the empirical 0–1 risk is the empirical
fraction of the error set (SSBD Eq. (2.2) vs `empFrac`); pure algebra. -/
theorem empRisk_zeroOneLoss_eq (s : Sample (X × Bool) n) (h : X → Bool) :
    empRisk zeroOneLoss s h = empFrac s (errSet h) := by
  rw [empRisk, empFrac]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hp : h (s i).1 = (s i).2
  · have : s i ∉ errSet h := by simpa [errSet] using hp
    simp [zeroOneLoss, hp, this]
  · have : s i ∈ errSet h := by simpa [errSet] using hp
    simp [zeroOneLoss, hp, this]

/-- The evaluated 0–1 loss family is finite: loss vectors take values in
`{0,1}ⁿ` (LEAN-ONLY; feeds the `Finset`-typed Massart lemma). -/
theorem finite_evalFamily_zeroOneLoss (𝓗 : Set (X → Bool))
    (s : Sample (X × Bool) n) :
    (evalFamily zeroOneLoss 𝓗 s).Finite := by
  classical
  refine Set.Finite.subset
    (Set.finite_range (fun (b : Fin n → Bool) => fun i => if b i then (1 : ℝ) else 0)) ?_
  rintro v ⟨h, -, rfl⟩
  refine ⟨fun i => decide (h (s i).1 ≠ (s i).2), ?_⟩
  funext i
  by_cases hp : h (s i).1 = (s i).2 <;> simp [zeroOneLoss, hp]

/-- The instance points of a sample, and the identification of loss vectors
with traces on them (LEAN-ONLY packaging of SSBD §28.1 step 1: on the
instance set `Λ`, `h` is determined by `Λ ∩ {h = true}`, and the label mask
`y` is common to all `h`, so distinct loss vectors need distinct traces). -/
private theorem exists_traceFamily_card_bound (𝓗 : Set (X → Bool))
    (s : Sample (X × Bool) n) :
    ∃ Λ : Finset X, Λ.card ≤ n ∧
      (evalFamily zeroOneLoss 𝓗 s).ncard ≤
        (traceFamily (setClassOf 𝓗) Λ).card := by
  classical
  refine ⟨Finset.image (fun i => (s i).1) Finset.univ, ?_, ?_⟩
  · calc (Finset.image (fun i => (s i).1) Finset.univ).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  · set Λ : Finset X := Finset.image (fun i => (s i).1) Finset.univ with hΛdef
    set φ : Finset X → Fin n → ℝ :=
      fun T i => if ((s i).1 ∈ T ↔ (s i).2 = true) then 0 else 1 with hφdef
    have hsub : evalFamily zeroOneLoss 𝓗 s ⊆
        ↑((traceFamily (setClassOf 𝓗) Λ).image φ) := by
      rintro v ⟨h, hh, rfl⟩
      have hS : {x | h x = true} ∈ setClassOf 𝓗 := ⟨h, hh, rfl⟩
      obtain ⟨T, hTΛ, hTeq⟩ := exists_finset_coe_of_subset_coe
        (Set.inter_subset_left : (↑Λ : Set X) ∩ {x | h x = true} ⊆ ↑Λ)
      have hTmem : T ∈ traceFamily (setClassOf 𝓗) Λ :=
        mem_traceFamily.mpr ⟨hTΛ, _, hS, hTeq.symm⟩
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨T, hTmem, ?_⟩)
      funext i
      have hxΛ : (s i).1 ∈ Λ :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      have hmemT : ((s i).1 ∈ T) ↔ (h (s i).1 = true) := by
        constructor
        · intro hx
          have hx' : (s i).1 ∈ (↑Λ : Set X) ∩ {x | h x = true} := by
            rw [← hTeq]; exact hx
          exact hx'.2
        · intro hx
          have hx' : (s i).1 ∈ (↑T : Set X) := by
            rw [hTeq]; exact ⟨hxΛ, hx⟩
          exact hx'
      simp only [hφdef]
      by_cases hp : h (s i).1 = (s i).2
      · rw [if_pos, zeroOneLoss, if_pos hp]
        rw [hmemT, hp]
      · rw [if_neg, zeroOneLoss, if_neg hp]
        rw [hmemT]
        intro hq
        exact hp (Bool.eq_iff_iff.mpr hq)
    calc (evalFamily zeroOneLoss 𝓗 s).ncard
        ≤ (↑((traceFamily (setClassOf 𝓗) Λ).image φ) : Set (Fin n → ℝ)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ((traceFamily (setClassOf 𝓗) Λ).image φ).card := Set.ncard_coe_finset _
      _ ≤ (traceFamily (setClassOf 𝓗) Λ).card := Finset.card_image_le

/-- **Loss-pattern count via Sauer–Shelah** (SSBD §28.1 step 1): if
`vcDim (setClassOf 𝓗) ≤ d`, the number of distinct loss vectors
`{(𝟙[h(xᵢ)≠yᵢ])ᵢ : h ∈ 𝓗}` on any `n`-sample is at most
`∑_{j=0}^d C(n,j)` — the XOR mask `y` identifies loss vectors with trace
vectors, and the trace count is Sauer–Shelah's. -/
theorem ncard_evalFamily_zeroOneLoss_le (𝓗 : Set (X → Bool)) {d : ℕ}
    (s : Sample (X × Bool) n)
    -- USER-INPUT: VC dimension bound; SSBD Lemma 6.10
    (hd : vcDim (setClassOf 𝓗) ≤ (d : ℕ∞)) :
    (evalFamily zeroOneLoss 𝓗 s).ncard ≤
      ∑ j ∈ Finset.range (d + 1), n.choose j := by
  obtain ⟨Λ, hΛn, hle⟩ := exists_traceFamily_card_bound 𝓗 s
  calc (evalFamily zeroOneLoss 𝓗 s).ncard
      ≤ (traceFamily (setClassOf 𝓗) Λ).card := hle
    _ ≤ ∑ k ∈ Finset.Iic d, Λ.card.choose k :=
        card_traceFamily_le_sum_choose hd Λ
    _ ≤ ∑ k ∈ Finset.Iic d, n.choose k :=
        Finset.sum_le_sum fun k _ => Nat.choose_le_choose k hΛn
    _ = ∑ j ∈ Finset.range (d + 1), n.choose j := by
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext k
        simp

/-- **Polynomial loss-pattern count** (SSBD Lemma 6.10 second half /
Lemma A.5): for `1 ≤ d` and `d + 1 < n`, the loss-pattern count is at most
`(en/d)^d`. -/
theorem ncard_evalFamily_zeroOneLoss_le_pow (𝓗 : Set (X → Bool)) {d : ℕ}
    (s : Sample (X × Bool) n)
    (hd : vcDim (setClassOf 𝓗) ≤ (d : ℕ∞))
    -- USER-INPUT: `1 ≤ d`; SSBD Lemma 6.10 (nondegenerate class)
    (hd1 : 1 ≤ d)
    -- USER-INPUT: `d + 1 < n`; SSBD Lemma 6.10 (`m > d + 1`)
    (hn : d + 1 < n) :
    ((evalFamily zeroOneLoss 𝓗 s).ncard : ℝ) ≤
      (Real.exp 1 * n / d) ^ d := by
  obtain ⟨Λ, hΛn, hle⟩ := exists_traceFamily_card_bound 𝓗 s
  have hcast : ((evalFamily zeroOneLoss 𝓗 s).ncard : ℝ) ≤
      ((traceFamily (setClassOf 𝓗) Λ).card : ℝ) := by exact_mod_cast hle
  exact hcast.trans (card_traceFamily_le_pow hd hd1 hΛn (by omega))

end StatLean.StatisticalLearning
