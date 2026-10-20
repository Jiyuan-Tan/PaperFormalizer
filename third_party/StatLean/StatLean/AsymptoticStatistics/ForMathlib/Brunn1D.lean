module
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.Group.Pointwise
public import Mathlib.Analysis.Normed.Group.Pointwise
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
Asymptotic Statistics — One-dimensional Brunn-Minkowski volume inequality.

For nonempty bounded measurable sets `A, B ⊆ ℝ`, the Lebesgue measure of
the Minkowski sum `A + B` satisfies the additive lower bound

  `volume A + volume B ≤ volume (A + B)`,

and the convex-combination form (a.k.a. 1-D Brunn-Minkowski) reads

  `λ · volume A + (1 - λ) · volume B ≤ volume (λ • A + (1 - λ) • B)`

for any `λ ∈ [0, 1]`.

The imported API does not package the Brunn-Minkowski inequality. This
file proves the one-dimensional case as a `ForMathlib` brick, used by
`StatLean/AsymptoticStatistics/ForMathlib/PrekopaLeindler.lean`.

Strategy: prove the **compact** case directly via the standard "shift by
sup/inf" trick (`A` shifted into `(-∞, 0]` and `B` shifted into
`[0, +∞)`, so they overlap only at `{0}` and cover `A ∪ B` modulo a
measure-zero set inside `A + B`), then extend to the bounded measurable
case via inner regularity of Lebesgue measure on ℝ
(`InnerRegularCompactLTTop` instance, automatic on
`(ℝ, IsCompletelyPseudoMetrizableSpace, SecondCountableTopology, BorelSpace)`).
-/

open MeasureTheory Set Bornology
open scoped Pointwise ENNReal

namespace AsymptoticStatistics.ForMathlib

/-- Translates of a set have the same Lebesgue measure (left-translate
form, used in two flavours below). -/
private lemma volume_translate_right (A : Set ℝ) (c : ℝ) :
    volume ((fun x => x + c) '' A) = volume A := by
  -- (· + c) '' A = ((· + c) ⁻¹' A)? No: image vs preimage.
  -- Simpler: (· + c) '' A = (c + ·) '' A (since add comm), and (c + ·) '' A = ((-c) + ·) ⁻¹' A.
  have hcomm : (fun x => x + c) = (fun x => c + x) := by funext x; ring
  rw [hcomm, Set.image_add_left]
  exact measure_preimage_add (volume : Measure ℝ) (-c) A

/-- Translation of a Minkowski sum: `(A - α) + (B - β) = (A + B) - (α + β)`. -/
private lemma image_sub_add_image_sub (α β : ℝ) (A B : Set ℝ) :
    ((fun x => x + (-α)) '' A) + ((fun x => x + (-β)) '' B)
      = (fun x => x + (-(α + β))) '' (A + B) := by
  ext z
  constructor
  · rintro ⟨a', ⟨a, haA, rfl⟩, b', ⟨b, hbB, rfl⟩, rfl⟩
    refine ⟨a + b, ⟨a, haA, b, hbB, rfl⟩, ?_⟩; ring
  · rintro ⟨c, ⟨a, haA, b, hbB, rfl⟩, rfl⟩
    refine ⟨a + (-α), ⟨a, haA, rfl⟩, b + (-β), ⟨b, hbB, rfl⟩, ?_⟩; ring

/-- **Brunn-Minkowski (compact 1-D, additive form).**

For nonempty compact sets `A, B ⊆ ℝ`,

  `volume A + volume B ≤ volume (A + B)`.

**Proof**: choose `α := max A` and `β := min B` (compact + nonempty).
Translate `A' := A - α ⊆ (-∞, 0]` and `B' := B - β ⊆ [0, +∞)`. Then
`0 ∈ A'` and `0 ∈ B'`, so `A' ∪ B' ⊆ A' + B'` and `A' ∩ B' ⊆ {0}`,
hence `volume A + volume B = volume A' + volume B' = volume (A' ∪ B') ≤
volume (A' + B') = volume (A + B)` (the last equality by translation
invariance). -/
theorem brunn_minkowski_compact_add
    {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  -- Step 1: extract α := max A, β := min B (compact + nonempty).
  obtain ⟨α, hαA, hαLUB⟩ := hA.exists_isLUB hAne
  obtain ⟨β, hβB, hβGLB⟩ := hB.exists_isGLB hBne
  have hαMax : ∀ x ∈ A, x ≤ α := fun x hx => hαLUB.1 hx
  have hβMin : ∀ x ∈ B, β ≤ x := fun x hx => hβGLB.1 hx
  -- Step 2: translated sets A' := A - α, B' := B - β.
  set A' : Set ℝ := (fun x => x + (-α)) '' A
  set B' : Set ℝ := (fun x => x + (-β)) '' B
  have hvolA : volume A' = volume A := volume_translate_right A (-α)
  have hvolB : volume B' = volume B := volume_translate_right B (-β)
  -- A' ⊆ (-∞, 0], 0 ∈ A'.
  have hzero_A' : (0 : ℝ) ∈ A' := ⟨α, hαA, by simp⟩
  have hA'_le : ∀ x ∈ A', x ≤ 0 := by
    rintro x ⟨a, haA, rfl⟩
    have := hαMax a haA; linarith
  -- B' ⊆ [0, ∞), 0 ∈ B'.
  have hzero_B' : (0 : ℝ) ∈ B' := ⟨β, hβB, by simp⟩
  have hB'_ge : ∀ x ∈ B', 0 ≤ x := by
    rintro x ⟨b, hbB, rfl⟩
    have := hβMin b hbB; linarith
  -- A' ∪ B' ⊆ A' + B'.
  have hUnion_sub : A' ∪ B' ⊆ A' + B' := by
    rintro x (hx | hx)
    · exact ⟨x, hx, 0, hzero_B', by simp⟩
    · exact ⟨0, hzero_A', x, hx, by simp⟩
  -- A' ∩ B' ⊆ {0}; volume zero.
  have hint_sub : A' ∩ B' ⊆ ({0} : Set ℝ) := fun x ⟨hxA, hxB⟩ => by
    have h1 := hA'_le x hxA
    have h2 := hB'_ge x hxB
    have : x = 0 := le_antisymm h1 h2
    simpa using this
  have hvol_int : volume (A' ∩ B') = 0 :=
    measure_mono_null hint_sub (by simp)
  -- volume(A' ∪ B') = volume A' + volume B' (since intersection has measure 0).
  have hB'_meas : MeasurableSet B' :=
    (hB.image (continuous_id.add continuous_const)).measurableSet
  have hvol_union : volume (A' ∪ B') = volume A' + volume B' := by
    -- measure_union_add_inter₀ would work, but simpler: B' is measurable and
    -- A' \ B' ∪ B' = A' ∪ B', and A' ∩ B' has measure 0.
    have key : volume (A' ∪ B') + volume (A' ∩ B') = volume A' + volume B' :=
      measure_union_add_inter A' hB'_meas
    rw [hvol_int, add_zero] at key
    exact key
  -- volume (A' + B') = volume (A + B) (translation invariance).
  have hvol_ABprime : volume (A' + B') = volume (A + B) := by
    rw [show A' + B' = (fun x => x + (-(α + β))) '' (A + B) from
        image_sub_add_image_sub α β A B]
    exact volume_translate_right (A + B) (-(α + β))
  -- Final chain.
  calc volume A + volume B
      = volume A' + volume B' := by rw [hvolA, hvolB]
    _ = volume (A' ∪ B') := hvol_union.symm
    _ ≤ volume (A' + B') := measure_mono hUnion_sub
    _ = volume (A + B) := hvol_ABprime

/-- **Brunn-Minkowski (1-D, additive form).**

For nonempty bounded measurable sets `A, B ⊆ ℝ`,

  `volume A + volume B ≤ volume (A + B)`.

(`A + B` is the Minkowski sum; `volume` is the Lebesgue outer measure,
defined whether or not `A + B` is itself measurable.)

**Proof**: by inner regularity of Lebesgue measure on ℝ
(`InnerRegularCompactLTTop`, automatic instance for second-countable
metric Borel spaces), approximate `A` and `B` from below by compact
subsets `K_A ⊆ A`, `K_B ⊆ B` with arbitrarily good measure
approximation. The compact case `brunn_minkowski_compact_add` applies to
nonempty compact approximants, and singleton-compact fillers handle the
case when an approximant happens to be empty. Take ε → 0 to conclude. -/
theorem brunn_minkowski_1d_add
    {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAbnd : IsBounded A) (hBbnd : IsBounded B) :
    volume A + volume B ≤ volume (A + B) := by
  -- Both volumes are finite (bounded sets in ℝ have finite Lebesgue measure).
  have hvolA_ne : volume A ≠ ∞ := by
    rcases hAbnd.subset_closedBall 0 with ⟨r, hAr⟩
    refine ((measure_mono hAr).trans_lt ?_).ne
    rw [Real.volume_closedBall]
    exact ENNReal.ofReal_lt_top
  have hvolB_ne : volume B ≠ ∞ := by
    rcases hBbnd.subset_closedBall 0 with ⟨r, hBr⟩
    refine ((measure_mono hBr).trans_lt ?_).ne
    rw [Real.volume_closedBall]
    exact ENNReal.ofReal_lt_top
  -- Reduce to: ∀ ε > 0, volume A + volume B ≤ volume(A + B) + ε.
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  -- Choose δ := ε/2.
  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 2 with hδ_def
  have hε_pos : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := by exact_mod_cast hε
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    exact ENNReal.div_pos hε_pos.ne' (by simp [ENNReal.ofNat_ne_top])
  have hδ_ne : δ ≠ 0 := hδ_pos.ne'
  have hδδ : δ + δ = (ε : ℝ≥0∞) := by
    simp only [hδ_def]
    rw [ENNReal.div_add_div_same]
    -- Goal: ((ε : ℝ≥0∞) + ε) / 2 = ε. Use 2 * ε / 2 = ε.
    rw [show (ε : ℝ≥0∞) + (ε : ℝ≥0∞) = 2 * (ε : ℝ≥0∞) from (two_mul _).symm,
        mul_div_assoc]
    exact ENNReal.mul_div_cancel (a := (2 : ℝ≥0∞)) two_ne_zero (by norm_num)
  -- Inner regularity gives compact subsets approximating A, B.
  obtain ⟨K_A, hKA_sub, hKA_compact, hKA_lt⟩ :=
    hA.exists_isCompact_lt_add hvolA_ne hδ_ne
  obtain ⟨K_B, hKB_sub, hKB_compact, hKB_lt⟩ :=
    hB.exists_isCompact_lt_add hvolB_ne hδ_ne
  -- volume A < volume K_A + δ, volume B < volume K_B + δ.
  have hvolA_le : volume A ≤ volume K_A + δ := hKA_lt.le
  have hvolB_le : volume B ≤ volume K_B + δ := hKB_lt.le
  -- Pick a "filler" element: even if K_A = ∅, use a singleton from A (volume 0).
  -- Define K_A* := if K_A nonempty then K_A else {a₀}; same for K_B*.
  -- Both are compact and nonempty, with volume(K_A*) ≤ volume K_A (since {a₀} = volume 0).
  -- Apply compact BM to K_A*, K_B*.
  obtain ⟨a₀, ha₀⟩ := hAne
  obtain ⟨b₀, hb₀⟩ := hBne
  -- We split on emptiness of K_A and K_B; in each case, a singleton replaces an empty piece.
  have hsing_A : IsCompact ({a₀} : Set ℝ) ∧ ({a₀} : Set ℝ).Nonempty :=
    ⟨isCompact_singleton, ⟨a₀, rfl⟩⟩
  have hsing_B : IsCompact ({b₀} : Set ℝ) ∧ ({b₀} : Set ℝ).Nonempty :=
    ⟨isCompact_singleton, ⟨b₀, rfl⟩⟩
  -- Each of K_A and K_B may be empty; pick the suitable substitute.
  by_cases hKAne : K_A.Nonempty
  · by_cases hKBne : K_B.Nonempty
    · -- BOTH NONEMPTY.
      have hcompactBM := brunn_minkowski_compact_add hKA_compact hKB_compact hKAne hKBne
      have hsum_sub : K_A + K_B ⊆ A + B := by
        rintro z ⟨a, haK, b, hbK, rfl⟩
        exact ⟨a, hKA_sub haK, b, hKB_sub hbK, rfl⟩
      calc volume A + volume B
          ≤ (volume K_A + δ) + (volume K_B + δ) := add_le_add hvolA_le hvolB_le
        _ = (volume K_A + volume K_B) + (δ + δ) := by ring
        _ ≤ volume (K_A + K_B) + (δ + δ) := by gcongr
        _ ≤ volume (A + B) + (δ + δ) := by gcongr
        _ = volume (A + B) + ε := by rw [hδδ]
    · -- K_B EMPTY: substitute {b₀} for K_B.
      have hKB_empty : K_B = ∅ := Set.not_nonempty_iff_eq_empty.mp hKBne
      have hvolKB : volume K_B = 0 := by rw [hKB_empty, measure_empty]
      have hvolB_lt_δ : volume B < δ := by
        have := hKB_lt; rw [hvolKB, zero_add] at this; exact this
      have hcompactBM :=
        brunn_minkowski_compact_add hKA_compact hsing_B.1 hKAne hsing_B.2
      have hsing_vol : volume ({b₀} : Set ℝ) = 0 := Real.volume_singleton
      rw [hsing_vol, add_zero] at hcompactBM
      have hsum_sub : K_A + ({b₀} : Set ℝ) ⊆ A + B := by
        rintro z ⟨a, haK, b, hb, rfl⟩
        rw [Set.mem_singleton_iff.mp hb]
        exact ⟨a, hKA_sub haK, b₀, hb₀, rfl⟩
      calc volume A + volume B
          ≤ (volume K_A + δ) + δ := add_le_add hvolA_le hvolB_lt_δ.le
        _ = volume K_A + (δ + δ) := by ring
        _ ≤ volume (K_A + ({b₀} : Set ℝ)) + (δ + δ) := by gcongr
        _ ≤ volume (A + B) + (δ + δ) := by gcongr
        _ = volume (A + B) + ε := by rw [hδδ]
  · -- K_A EMPTY: substitute {a₀} for K_A.
    have hKA_empty : K_A = ∅ := Set.not_nonempty_iff_eq_empty.mp hKAne
    have hvolKA : volume K_A = 0 := by rw [hKA_empty, measure_empty]
    have hvolA_lt_δ : volume A < δ := by
      have := hKA_lt; rw [hvolKA, zero_add] at this; exact this
    by_cases hKBne : K_B.Nonempty
    · have hcompactBM :=
        brunn_minkowski_compact_add hsing_A.1 hKB_compact hsing_A.2 hKBne
      have hsing_vol : volume ({a₀} : Set ℝ) = 0 := Real.volume_singleton
      rw [hsing_vol, zero_add] at hcompactBM
      have hsum_sub : ({a₀} : Set ℝ) + K_B ⊆ A + B := by
        rintro z ⟨a, ha, b, hbK, rfl⟩
        rw [Set.mem_singleton_iff.mp ha]
        exact ⟨a₀, ha₀, b, hKB_sub hbK, rfl⟩
      calc volume A + volume B
          ≤ δ + (volume K_B + δ) := add_le_add hvolA_lt_δ.le hvolB_le
        _ = volume K_B + (δ + δ) := by ring
        _ ≤ volume (({a₀} : Set ℝ) + K_B) + (δ + δ) := by gcongr
        _ ≤ volume (A + B) + (δ + δ) := by gcongr
        _ = volume (A + B) + ε := by rw [hδδ]
    · -- BOTH EMPTY: volumes both < δ, sum < δ + δ = ε; trivial.
      have hKB_empty : K_B = ∅ := Set.not_nonempty_iff_eq_empty.mp hKBne
      have hvolKB : volume K_B = 0 := by rw [hKB_empty, measure_empty]
      have hvolB_lt_δ : volume B < δ := by
        have := hKB_lt; rw [hvolKB, zero_add] at this; exact this
      calc volume A + volume B
          ≤ δ + δ := add_le_add hvolA_lt_δ.le hvolB_lt_δ.le
        _ ≤ volume (A + B) + (δ + δ) := le_add_self
        _ = volume (A + B) + ε := by rw [hδδ]

/-- Lemma: scaling a set by a real number preserves measurability. -/
private lemma measurableSet_smul_real
    {S : Set ℝ} (hS : MeasurableSet S) (hSne : S.Nonempty) (l : ℝ) :
    MeasurableSet (l • S) := by
  rcases eq_or_ne l 0 with h0 | h0
  · subst h0
    rcases hSne with ⟨s, hs⟩
    have h_eq : (0 : ℝ) • S = ({0} : Set ℝ) := by
      ext x
      constructor
      · rintro ⟨_, _, rfl⟩; simp
      · rintro hx
        simp only [Set.mem_singleton_iff] at hx
        exact ⟨s, hs, by rw [hx]; simp⟩
    rw [h_eq]; exact MeasurableSet.singleton 0
  · have heq : (l • S : Set ℝ) = (fun x => l * x) '' S := rfl
    rw [heq]
    exact (MeasurableEquiv.smul (Units.mk0 l h0)).measurableSet_image.mpr hS

/-- Lemma: scaling a bounded set in ℝ by a real number gives a bounded
set. -/
private lemma isBounded_smul_real
    {S : Set ℝ} (hS : IsBounded S) (l : ℝ) :
    IsBounded (l • S) := by
  -- l • S = (l • ·) '' S; scalar multiplication by a constant is Lipschitz, so it preserves
  -- bounded sets.
  have heq : (l • S : Set ℝ) = (fun x : ℝ => l • x) '' S := rfl
  rw [heq]
  exact (lipschitzWith_smul l).isBounded_image hS

/-- Lemma: scaling preserves nonemptyness. -/
private lemma nonempty_smul_real
    {S : Set ℝ} (hS : S.Nonempty) (l : ℝ) :
    (l • S).Nonempty :=
  hS.image (fun x => l * x)

/-- **1-D Brunn-Minkowski volume inequality (convex-combination form).**

For nonempty bounded measurable sets `A, B ⊆ ℝ` and `λ ∈ [0, 1]`,

  `λ · volume A + (1 - λ) · volume B ≤ volume (λ • A + (1 - λ) • B)`.

The standard textbook 1-D Brunn-Minkowski statement. Proof reduces to
`brunn_minkowski_1d_add` applied to `l • A` and `(1 - l) • B`,
followed by `Real.volume_real_smul` to recover the `λ`/`1-λ` coefficients.

The factors on the left are written as `ENNReal.ofReal`-coercions
because the Lebesgue measure has codomain `ℝ≥0∞`. -/
theorem brunn_minkowski_1d
    {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAbnd : IsBounded A) (hBbnd : IsBounded B)
    {l : ℝ} (hl0 : 0 ≤ l) (_hl1 : l ≤ 1) :
    ENNReal.ofReal l * volume A + ENNReal.ofReal (1 - l) * volume B
      ≤ volume (l • A + (1 - l) • B) := by
  have h1ml_nn : 0 ≤ 1 - l := by linarith
  -- Properties of l • A and (1 - l) • B.
  have hlA_meas : MeasurableSet (l • A) := measurableSet_smul_real hA hAne l
  have h1mlB_meas : MeasurableSet ((1 - l) • B) := measurableSet_smul_real hB hBne (1 - l)
  have hlA_ne : (l • A).Nonempty := nonempty_smul_real hAne l
  have h1mlB_ne : ((1 - l) • B).Nonempty := nonempty_smul_real hBne (1 - l)
  have hlA_bnd : IsBounded (l • A) := isBounded_smul_real hAbnd l
  have h1mlB_bnd : IsBounded ((1 - l) • B) := isBounded_smul_real hBbnd (1 - l)
  -- Apply additive form.
  have hadd := brunn_minkowski_1d_add hlA_meas h1mlB_meas hlA_ne h1mlB_ne hlA_bnd h1mlB_bnd
  -- Volume of scaled set: addHaar_smul gives `volume (r • s) = ofReal |r^dim| * volume s`,
  -- and for ℝ with `finrank ℝ ℝ = 1` this simplifies to `ofReal |r| * volume s`.
  have hvol_lA : volume (l • A) = ENNReal.ofReal l * volume A := by
    rw [MeasureTheory.Measure.addHaar_smul (volume : Measure ℝ)]
    congr 1
    rw [Module.finrank_self, pow_one, abs_of_nonneg hl0]
  have hvol_1mlB : volume ((1 - l) • B) = ENNReal.ofReal (1 - l) * volume B := by
    rw [MeasureTheory.Measure.addHaar_smul (volume : Measure ℝ)]
    congr 1
    rw [Module.finrank_self, pow_one, abs_of_nonneg h1ml_nn]
  rw [← hvol_lA, ← hvol_1mlB]
  exact hadd

end AsymptoticStatistics.ForMathlib
