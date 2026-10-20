module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.Carrier
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing

@[expose] public section

/-!
# A Dudley dyadic net family for `(↥F, distL2 P)` from finite bracketing entropy

The Gaussian-chaining headline `GaussianChaining.gaussianChaining_UC` consumes its
dyadic net as **explicit data**: a family `net : ℕ → Finset T`, each `net j` a
`2^{-j}`-net of `T`, nested (`Monotone net`), together with the **Dudley
summability**
`Summable (fun j => 2^{-j} · √(log (2 · (net j).card)))`.
This file constructs that data for `T = ↥F` in the `L²(P)` semimetric `distL2 P`,
from the single analytic input `bracketingEntropyIntegral 1 F P < ⊤` (van der Vaart
§19.2's finite bracketing-entropy integral).

## Construction

* `cardNet hcov` — a card-controlled `ε`-net: from a finite `ε`-bracketing cover of
  `F`, a finite `S : Finset ↥F` with the `distL2 P`-ε-net property **and**
  `(S.card : ℕ∞) ≤ bracketingNumber ε F 2 P`. This is the card-aware refinement of
  `totallyBounded_L2` (which discards the count): each covering bracket contributes
  at most one representative, so the net is no larger than the minimal bracketing
  cover.
* `rawNet hF_ent F P j := cardNet …` — the per-scale net at `(1/2)^j`.
* `dudleyNet … j := (Finset.range (j+1)).biUnion (rawNet …)` — the nested net
  (`Monotone` by construction, still `2^{-j}`-dense since `rawNet j ⊆ dudleyNet j`).

## Main result

* `exists_dudley_net` — packages all four pieces (`net`, ε-net, `Monotone`, Dudley
  summability), discharging the chaining input from `bracketingEntropyIntegral 1 F P < ⊤`.

The Dudley-summability crux is a **sum-vs-integral comparison**: the dyadic series
`∑_q 2^{-q} √(log (1 + N_{[]}(2^{-q})))` is dominated by `2 · J_{[]}(1, F, L²(P))`
(`dyadic_sum_le_bracketingEntropyIntegral`, in `Bracketing`), which is finite. The
extra `√(log(2(j+1)))` wrinkle from nesting is sub-polynomial × geometric, hence
also summable.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §19.2, §19.6.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Card-controlled ε-net from the bracketing cover -/

/-- **Card-controlled `ε`-net of `(↥F, distL2 P)`.** From the minimal finite
`ε`-bracketing cover of `F` (`exists_minimal_bracketingCover`), pick one
representative `↥F`-element per covering bracket. The resulting finite set `S` is a
`distL2 P`-`ε`-net of `↥F` whose cardinality is at most the bracketing number
`N_{[]}(ε, F, L²(P))`. This is the card-aware version of `totallyBounded_L2`, which
discards the cardinality.

The cardinality bound is the whole point: it lets the downstream `hDudley`
summability (stated on `(net j).card`) be discharged from the entropy integral. -/
lemma cardNet {F : Set (Ω → ℝ)} {P : Measure Ω} {ε : ℝ}
    (hcov : HasFiniteBracketingCover F ε 2 P) :
    ∃ S : Finset ↥F,
      (∀ t : ↥F, ∃ s ∈ S, distL2 P (t : Ω → ℝ) (s : Ω → ℝ) < ε) ∧
      (S.card : ℕ∞) ≤ bracketingNumber ε F 2 P := by
  classical
  -- Extract the minimal finite `ε`-bracketing cover; its size equals the bracketing number.
  obtain ⟨k, l, u, hbr, hcov', hk_eq⟩ := exists_minimal_bracketingCover hcov
  -- The indices `i : Fin k` whose bracket actually contains some element of `F`.
  set Q : Fin k → Prop := fun i => ∃ f, f ∈ F ∧ ∀ x, l i x ≤ f x ∧ f x ≤ u i x with hQ
  -- For each `Q`-index pick a representative `rep i ∈ F` lying in bracket `i`,
  -- packaged as an element of the subtype `↥F`.
  have hrep : ∀ i, Q i → ∃ g : ↥F, ∀ x, l i x ≤ (g : Ω → ℝ) x ∧ (g : Ω → ℝ) x ≤ u i x := by
    intro i hi
    obtain ⟨g, hgF, hg⟩ := hi
    exact ⟨⟨g, hgF⟩, hg⟩
  -- The net = the representatives of the covering (`Q`-)brackets. Built over
  -- `(filter Q univ).attach` so no default `↥F`-element is needed (avoids requiring
  -- `F.Nonempty` here): the choose-witness uses the in-scope membership proof.
  set rep : ∀ i ∈ (Finset.univ.filter Q), ↥F :=
    fun i hi => (hrep i ((Finset.mem_filter.mp hi).2)).choose with hrep_def
  refine ⟨(Finset.univ.filter Q).attach.image (fun p => rep p.1 p.2), ?_, ?_⟩
  · -- ε-net property.
    intro t
    -- `t.1 ∈ F` lies in some bracket `i`.
    obtain ⟨i, hi_cov⟩ := hcov' (t : Ω → ℝ) t.2
    -- Bracket `i` is a covering bracket (it contains `t.1 ∈ F`), so it is a `Q`-index.
    have hQi : Q i := ⟨(t : Ω → ℝ), t.2, hi_cov⟩
    have hi_mem : i ∈ Finset.univ.filter Q := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hQi⟩
    refine ⟨rep i hi_mem, ?_, ?_⟩
    · -- `rep i ∈ S`.
      refine Finset.mem_image.mpr ⟨⟨i, hi_mem⟩, Finset.mem_attach _ _, rfl⟩
    · -- `distL2 P t (rep i) < ε`: both lie in bracket `i`.
      have hrep_spec : ∀ x, l i x ≤ (rep i hi_mem : Ω → ℝ) x ∧ (rep i hi_mem : Ω → ℝ) x ≤ u i x :=
        (hrep i ((Finset.mem_filter.mp hi_mem).2)).choose_spec
      -- Pointwise: `|t x - rep i x| ≤ u i x - l i x`.
      have h_ptwise : ∀ x,
          ‖((t : Ω → ℝ) - (rep i hi_mem : Ω → ℝ)) x‖ ≤ ‖(fun y => u i y - l i y) x‖ := by
        intro x
        have hl_t := (hi_cov x).1
        have ht_u := (hi_cov x).2
        have hl_r := (hrep_spec x).1
        have hr_u := (hrep_spec x).2
        simp only [Pi.sub_apply, Real.norm_eq_abs]
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u i x - l i x)]
        rw [abs_sub_le_iff]
        constructor <;> linarith
      have h_eLp_le : eLpNorm ((t : Ω → ℝ) - (rep i hi_mem : Ω → ℝ)) 2 P
          ≤ eLpNorm (fun y => u i y - l i y) 2 P := eLpNorm_mono h_ptwise
      have h_size : eLpNorm (fun y => u i y - l i y) 2 P < ENNReal.ofReal ε := (hbr i).size_lt
      have h_lt : eLpNorm ((t : Ω → ℝ) - (rep i hi_mem : Ω → ℝ)) 2 P < ENNReal.ofReal ε :=
        lt_of_le_of_lt h_eLp_le h_size
      exact ENNReal.toReal_lt_of_lt_ofReal h_lt
  · -- Cardinality bound: `S.card ≤ (filter Q univ).card ≤ k = bracketingNumber`.
    rw [hk_eq]
    have h1 : ((Finset.univ.filter Q).attach.image (fun p => rep p.1 p.2)).card
        ≤ (Finset.univ.filter Q).card := by
      refine le_trans (Finset.card_image_le) ?_
      rw [Finset.card_attach]
    have h2 : (Finset.univ.filter Q).card ≤ k := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      simp
    exact_mod_cast le_trans h1 h2

/-! ## Headline -/

/-- **Dudley dyadic net for `(↥F, distL2 P)`.** From a finite bracketing-entropy
integral `J_{[]}(1, F, L²(P)) < ⊤`, there is a nested dyadic net family
`net : ℕ → Finset ↥F` for the `L²(P)` semimetric on `↥F`, satisfying the three
properties the Gaussian-chaining headline `gaussianChaining_UC` requires: each
`net j` is a `2^{-j}`-net, the family is `Monotone`, and the Dudley series
`∑_j 2^{-j} √(log (2 · (net j).card))` is summable. -/
lemma exists_dudley_net {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (_hF_ne : F.Nonempty) :
    ∃ (net : ℕ → Finset ↥F),
      (∀ (j : ℕ) (t : ↥F), ∃ s ∈ net j,
        distL2 P (t : Ω → ℝ) (s : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ))) ∧
      Monotone net ∧
      Summable (fun j : ℕ =>
        (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card))) := by
  classical
  -- `2^{-j} = (1/2)^j` (used pervasively to align the goal's `(2:ℝ)^(-(j:ℤ))` with the
  -- dyadic scale `(1/2)^j` of `dyadic_sum_le_bracketingEntropyIntegral`).
  have hpow : ∀ j : ℕ, (2 : ℝ) ^ (-(j : ℤ)) = (1 / 2 : ℝ) ^ j := fun j => by
    rw [zpow_neg, ← inv_zpow, zpow_natCast]; norm_num
  -- A finite `ε`-bracketing cover at every scale (from the finite entropy integral).
  have Hcov : ∀ ε : ℝ, 0 < ε → HasFiniteBracketingCover F ε 2 P :=
    fun ε hε => hasFiniteBracketingCover_of_entropyIntegral_lt_top hF_ent hε
  -- The per-scale card-controlled net at scale `(1/2)^j`.
  have hscale_pos : ∀ j : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ j := fun j => by positivity
  let rawData : ∀ j : ℕ, {S : Finset ↥F //
      (∀ t : ↥F, ∃ s ∈ S, distL2 P (t : Ω → ℝ) (s : Ω → ℝ) < (1 / 2 : ℝ) ^ j) ∧
        (S.card : ℕ∞) ≤ bracketingNumber ((1 / 2 : ℝ) ^ j) F 2 P} :=
    fun j => ⟨(cardNet (Hcov _ (hscale_pos j))).choose,
      (cardNet (Hcov _ (hscale_pos j))).choose_spec⟩
  let rawNet : ℕ → Finset ↥F := fun j => (rawData j).1
  -- The ℕ-value of the bracketing number at scale `(1/2)^j` (finite by the cover).
  have hbn_lt : ∀ j : ℕ, bracketingNumber ((1 / 2 : ℝ) ^ j) F 2 P < ⊤ :=
    fun j => bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mpr (Hcov _ (hscale_pos j))
  let Nfun : ℕ → ℕ := fun j => (bracketingNumber ((1 / 2 : ℝ) ^ j) F 2 P).toNat
  have hN_eq : ∀ j : ℕ, (bracketingNumber ((1 / 2 : ℝ) ^ j) F 2 P) = (Nfun j : ℕ∞) :=
    fun j => (ENat.coe_toNat (hbn_lt j).ne).symm
  have hrawNet_card : ∀ j : ℕ, (rawNet j).card ≤ Nfun j := by
    intro j
    have h := (rawData j).2.2
    have h' : ((rawNet j).card : ℕ∞) ≤ (Nfun j : ℕ∞) := hN_eq j ▸ h
    exact_mod_cast h'
  have hrawNet_net : ∀ (j : ℕ) (t : ↥F),
      ∃ s ∈ rawNet j, distL2 P (t : Ω → ℝ) (s : Ω → ℝ) < (1 / 2 : ℝ) ^ j :=
    fun j => (rawData j).2.1
  -- The nested net.
  let net : ℕ → Finset ↥F := fun j => (Finset.range (j + 1)).biUnion rawNet
  refine ⟨net, ?_, ?_, ?_⟩
  · -- (1) ε-net property: `rawNet j ⊆ net j` is still `2^{-j}`-dense.
    intro j t
    obtain ⟨s, hs_mem, hs_lt⟩ := hrawNet_net j t
    refine ⟨s, ?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_self j), hs_mem⟩
    · rwa [hpow j]
  · -- (2) Monotone.
    intro a b hab
    have hsub : Finset.range (a + 1) ⊆ Finset.range (b + 1) :=
      Finset.range_mono (Nat.add_le_add_right hab 1)
    exact Finset.biUnion_subset_biUnion_of_subset_left rawNet hsub
  · -- (3) Dudley summability. `(net j).card ≤ ∑_{i≤j} (rawNet i).card ≤ (j+1)·Nfun j`.
    -- Card bound: nested biUnion ≤ sum of pieces ≤ (j+1)·Nfun j (antitone Nfun).
    have hN_antitone : ∀ {i j : ℕ}, i ≤ j → Nfun i ≤ Nfun j := by
      intro i j hij
      have hscale : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ i :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
      have hbn := bracketingNumber_antitone_eps (F := F) (P := P) (r := 2) hscale
      rw [hN_eq i, hN_eq j] at hbn
      exact_mod_cast hbn
    have hnet_card : ∀ j : ℕ, (net j).card ≤ (j + 1) * Nfun j := by
      intro j
      calc (net j).card
          ≤ ∑ i ∈ Finset.range (j + 1), (rawNet i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ Finset.range (j + 1), Nfun j := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            exact le_trans (hrawNet_card i) (hN_antitone hij)
        _ = (j + 1) * Nfun j := by rw [Finset.sum_const, Finset.card_range]; ring
    -- Split `√(log(2·card)) ≤ √(log(2(j+1))) + √(log(1+Nfun j))` (sqrt-subadditivity).
    have hsplit : ∀ j : ℕ,
        (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card))
          ≤ (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (j + 1)))
            + (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (1 + Nfun j)) := by
      intro j
      have hpow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(j : ℤ)) := by positivity
      have hNfun_nn : (0 : ℝ) ≤ (Nfun j : ℝ) := Nat.cast_nonneg _
      -- `2·card ≤ 2(j+1)·(1+Nfun j)` so `log(2·card) ≤ log(2(j+1)) + log(1+Nfun j)`.
      have hcard_pos : (0 : ℝ) < 2 * (j + 1 : ℝ) := by positivity
      have hN_pos : (0 : ℝ) < 1 + (Nfun j : ℝ) := by positivity
      have hN_ge_one : (1 : ℝ) ≤ 1 + (Nfun j : ℝ) := by linarith
      have hcard_le : (2 * (net j).card : ℝ) ≤ (2 * (j + 1)) * (1 + Nfun j) := by
        have h1 : ((net j).card : ℝ) ≤ ((j + 1) * Nfun j : ℕ) := by exact_mod_cast hnet_card j
        push_cast at h1 ⊢
        nlinarith [hNfun_nn, (by positivity : (0:ℝ) ≤ (j:ℝ))]
      have hlog_le : Real.log (2 * (net j).card)
          ≤ Real.log (2 * (j + 1)) + Real.log (1 + Nfun j) := by
        rcases Nat.eq_zero_or_pos (net j).card with h0 | hpos
        · rw [h0]; simp only [Nat.cast_zero, mul_zero, Real.log_zero]
          have h2 := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 * (j + 1))
          have h3 := Real.log_nonneg hN_ge_one
          linarith
        · have hcard_real_pos : (0 : ℝ) < 2 * (net j).card := by
            have : (1 : ℝ) ≤ (net j).card := by exact_mod_cast hpos
            linarith
          calc Real.log (2 * (net j).card)
              ≤ Real.log ((2 * (j + 1)) * (1 + Nfun j)) := Real.log_le_log hcard_real_pos hcard_le
            _ = Real.log (2 * (j + 1)) + Real.log (1 + Nfun j) :=
                Real.log_mul (by positivity) (by positivity)
      -- sqrt-subadditivity: `√(a+b) ≤ √a + √b` for `a, b ≥ 0`.
      have ha : (0 : ℝ) ≤ Real.log (2 * (j + 1)) :=
        Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 * (j + 1))
      have hb : (0 : ℝ) ≤ Real.log (1 + Nfun j) := Real.log_nonneg hN_ge_one
      have hsqrt_sub : Real.sqrt (Real.log (2 * (net j).card))
          ≤ Real.sqrt (Real.log (2 * (j + 1))) + Real.sqrt (Real.log (1 + Nfun j)) := by
        refine (Real.sqrt_le_sqrt hlog_le).trans ?_
        rw [show Real.sqrt (Real.log (2 * (j + 1))) + Real.sqrt (Real.log (1 + Nfun j))
              = Real.sqrt ((Real.sqrt (Real.log (2 * (j + 1)))
                  + Real.sqrt (Real.log (1 + Nfun j))) ^ 2) from
            (Real.sqrt_sq (by positivity)).symm]
        apply Real.sqrt_le_sqrt
        nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
          Real.sqrt_nonneg (Real.log (2 * (j + 1))), Real.sqrt_nonneg (Real.log (1 + Nfun j)),
          mul_nonneg (Real.sqrt_nonneg (Real.log (2 * (j + 1))))
            (Real.sqrt_nonneg (Real.log (1 + Nfun j)))]
      calc (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card))
          ≤ (2 : ℝ) ^ (-(j : ℤ))
              * (Real.sqrt (Real.log (2 * (j + 1))) + Real.sqrt (Real.log (1 + Nfun j))) :=
            mul_le_mul_of_nonneg_left hsqrt_sub hpow_nn
        _ = (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (j + 1)))
            + (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (1 + Nfun j)) := by ring
    -- Both dominating series are summable.
    have hsum1 : Summable (fun j : ℕ =>
        (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (j + 1)))) := by
      -- Crude: `√(log(2(j+1))) ≤ 2(j+1)`, geometric × polynomial.
      have hcmp : ∀ j : ℕ,
          (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (j + 1)))
            ≤ (2 * ((j : ℝ) + 1)) * (1 / 2 : ℝ) ^ j := by
        intro j
        rw [hpow j, mul_comm]
        gcongr
        have hx : (0 : ℝ) < 2 * ((j : ℝ) + 1) := by positivity
        have hlog : Real.log (2 * ((j : ℝ) + 1)) ≤ 2 * ((j : ℝ) + 1) := by
          nlinarith [Real.log_le_sub_one_of_pos hx]
        calc Real.sqrt (Real.log (2 * ((j : ℝ) + 1)))
            ≤ Real.sqrt (2 * ((j : ℝ) + 1)) := Real.sqrt_le_sqrt hlog
          _ ≤ 2 * ((j : ℝ) + 1) := by
              nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg (2 * ((j : ℝ) + 1)),
                Real.one_le_sqrt.mpr (show (1:ℝ) ≤ 2 * ((j:ℝ)+1) by
                  have := Nat.cast_nonneg (α := ℝ) j; linarith)]
      apply Summable.of_nonneg_of_le (fun j => by positivity) (fun j => by
        have := hcmp j
        simpa [Nat.cast_add, Nat.cast_one] using this)
      have hr : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
      -- `∑ (j+1)·(1/2)^j` summable (`summable_pow_mul_geometric` with the `1+·` shift),
      -- scaled by `2`.
      have hg : Summable (fun j : ℕ => ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j) := by
        have h1 : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) :=
          (summable_pow_mul_geometric_of_norm_lt_one 1 hr).congr (fun j => by rw [pow_one])
        have h2 : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
          summable_geometric_of_norm_lt_one hr
        exact (h1.add h2).congr (fun j => by simp only [one_div, inv_pow]; ring)
      exact (hg.mul_left 2).congr (fun j => by simp only [one_div, inv_pow]; ring)
    have hsum2 : Summable (fun j : ℕ =>
        (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (1 + Nfun j))) := by
      -- The entropy half: dominated by `2 · J_{[]}(1, F, L²(P)) < ⊤` via the dyadic
      -- sum-vs-integral comparison `dyadic_sum_le_bracketingEntropyIntegral`.
      -- Recast as `(g j).toReal` for an ENNReal series with finite sum.
      set g : ℕ → ℝ≥0∞ := fun j =>
        ENNReal.ofReal ((1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (1 + Nfun j))) with hg_def
      have hg_eq_entropy : ∀ j : ℕ,
          g j = ENNReal.ofReal ((1 / 2 : ℝ) ^ j) * entropyIntegrand ((1 / 2 : ℝ) ^ j) F P := by
        intro j
        rw [hg_def, entropyIntegrand, hN_eq j, entropyWeight_coe,
          ← ENNReal.ofReal_mul (by positivity)]
      have hsum_lt : (∑' j : ℕ, g j) ≠ ⊤ := by
        have hcmp := dyadic_sum_le_bracketingEntropyIntegral (F := F) (P := P)
          (δ := 1) (by norm_num)
        -- `∑' g j` is exactly the dyadic series (the `* 1` from `δ = 1` is a no-op).
        have hgeq : (∑' j : ℕ, g j)
            = ∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ q * 1)
                * entropyIntegrand ((1 / 2 : ℝ) ^ q * 1) F P := by
          refine tsum_congr (fun j => ?_)
          rw [hg_eq_entropy j]
          simp only [mul_one]
        have hle : (∑' j : ℕ, g j) ≤ 2 * bracketingEntropyIntegral 1 F P := by
          rw [hgeq]; exact hcmp
        refine ne_top_of_le_ne_top ?_ hle
        exact ENNReal.mul_ne_top (by norm_num) hF_ent.ne
      have hsummable_toReal : Summable (fun j => (g j).toReal) :=
        ENNReal.summable_toReal hsum_lt
      apply hsummable_toReal.congr
      intro j
      rw [hg_def, ENNReal.toReal_ofReal (by positivity), hpow j]
    exact Summable.of_nonneg_of_le (fun j => by positivity) hsplit (hsum1.add hsum2)

end AsymptoticStatistics.EmpiricalProcess
