module
public import StatLean.ConcentrationInequalities.Maximal.CoveringNumbers
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Admissible sequences and the γ₂ functional

Talagrand's generic-chaining functional: an *admissible sequence* of a set
$T$ is an increasing-resolution sequence of subsets $(T_k)_{k \ge 0}$ with
$|T_0| = 1$ and $|T_k| \le 2^{2^k}$, and
$$ \gamma_2(T, d) \;=\; \inf_{(T_k)} \; \sup_{t \in T}
     \sum_{k=0}^{\infty} 2^{k/2}\, d(t, T_k), $$
the infimum over admissible sequences. Concept-layer file (no probability);
consumed by `Chaining/GenericChaining.lean`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.5.1, Definition 8.5.1, Eqs. (8.43) (admissible
sequence) and (8.45) (the γ₂ functional).

**Proof formalization notes.** `gammaFunctional` and `gammaTwo` are BOTH
`ℝ≥0∞`-valued (a real tsum/iSup would junk-degrade to `0` on divergent
sequences and corrupt the infimum downward); `2^{k/2}` is encoded as
`(Real.sqrt 2)^k`. The `nonempty` field of `AdmissibleSequence` is
Constitutive-by-necessity: Mathlib's `Metric.infDist x ∅ = 0` junk would
otherwise corrupt γ₂ downward. Edge behavior: `gammaTwo ∅ = ⊤` (infimum over
the empty type of admissible sequences — `card_zero` forces a point of `T`),
documented junk. Finiteness for finite `T` (`gammaTwo_lt_top_of_finite`) uses
the exhausting sequence `seq k = T` once `2^{2^k} ≥ |T|`. The book's "there
must be some `K` with `T_K = T`" step becomes the pseudometric-safe
`AdmissibleSequence.exists_eventually_dist_zero`: finite `T` + finite
functional ⇒ series terms → 0 ⇒ eventually a net point at distance `0`
(X-values are then a.e.-identified downstream). Named-sorry fallback of this
work item: `AdmissibleSequence.exists_eventually_dist_zero` (definitions,
finiteness, and the diameter lemmas proved).

**Bibliographic comments.** The γ₂ functional and generic chaining are due to
M. Talagrand, "Regularity of Gaussian processes," *Acta Math.* 159 (1987),
99–149, building on X. Fernique's majorizing measures (1975); the admissible-
sequence formulation is Talagrand, *The Generic Chaining*, Springer 2005, and
*Upper and Lower Bounds for Stochastic Processes*, Springer 2014, §2.3.
-/

open Set
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {E : Type*} [PseudoMetricSpace E]

/-- **Admissible sequence** (HDP §8.5.1, Definition 8.5.1, Eq. (8.43)): a
sequence of finite subsets of `T` with `|T₀| = 1` and `|T_k| ≤ 2^{2^k}`,
along which the γ₂ series is formed. -/
structure AdmissibleSequence (T : Set E) where
  /-- Constitutive (HDP §8.5.1, Eq. (8.43)): the level-`k` approximating
  finite subset `T_k`. -/
  seq : ℕ → Finset E
  /-- Constitutive (HDP §8.5.1, Eq. (8.43)): each level lies inside the
  carrier, `T_k ⊆ T`. -/
  subset_carrier : ∀ k, ↑(seq k) ⊆ T
  /-- Constitutive-by-necessity (HDP §8.5.1): each level is nonempty —
  Mathlib's `Metric.infDist x ∅ = 0` junk would corrupt γ₂ downward
  (the book's `|T₀| = 1` already forces nonemptiness at every level). -/
  nonempty : ∀ k, (seq k).Nonempty
  /-- Constitutive (HDP §8.5.1, Eq. (8.43)): the root level is a singleton,
  `|T₀| = 1`. -/
  card_zero : (seq 0).card = 1
  /-- Constitutive (HDP §8.5.1, Eq. (8.43)): the doubly-exponential
  cardinality budget `|T_k| ≤ 2^{2^k}`. -/
  card_le : ∀ k, (seq k).card ≤ 2 ^ 2 ^ k

/-- **γ₂ series along an admissible sequence** (HDP §8.5.1, Eq. (8.45), inner
quantity): `sup_{t ∈ T} Σ_k 2^{k/2} d(t, T_k)`, valued in `ℝ≥0∞` so that
divergent series register as `⊤` rather than junk `0`; `2^{k/2}` is encoded
as `(√2)^k`. -/
noncomputable def gammaFunctional {T : Set E} (A : AdmissibleSequence T) : ℝ≥0∞ :=
  ⨆ t ∈ T, ∑' k : ℕ, ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))

/-- **The γ₂ functional** (HDP §8.5.1, Eq. (8.45)): the infimum of the γ₂
series over all admissible sequences, in `ℝ≥0∞`. Edge behavior: `⊤` for
`T = ∅` (no admissible sequence exists), documented junk. -/
noncomputable def gammaTwo (T : Set E) : ℝ≥0∞ :=
  ⨅ A : AdmissibleSequence T, gammaFunctional A

/-- Nonempty sets admit admissible sequences (the constant singleton
sequence). -/
lemma nonempty_admissibleSequence {T : Set E}
    -- LEAN-ONLY: nonemptiness supplies the singleton root; HDP §8.5.1
    (hne : T.Nonempty) :
    Nonempty (AdmissibleSequence T) := by
  obtain ⟨a, ha⟩ := hne
  exact ⟨{ seq := fun _ => {a}
           subset_carrier := fun k => by
             rw [Finset.coe_singleton, Set.singleton_subset_iff]; exact ha
           nonempty := fun k => Finset.singleton_nonempty a
           card_zero := Finset.card_singleton a
           card_le := fun k => by
             rw [Finset.card_singleton]; exact Nat.one_le_pow _ _ (by norm_num) }⟩

/-- γ₂ is bounded by the series of any admissible sequence (`iInf_le`). -/
lemma gammaTwo_le {T : Set E} (A : AdmissibleSequence T) :
    -- LEAN-ONLY: iInf_le; no book content
    gammaTwo T ≤ gammaFunctional A := iInf_le _ A

/-- **Per-level distance bound from the γ₂ series** (HDP §8.5.2, proof
Step 1, Eq. (8.46) consequence): each series term sits below the whole
series, so `√2^k · d(t, T_k) ≤ (γ₂-series of A).toReal` whenever the series
is finite. This is the general-`T` replacement for the finite-`T` chain-end
device `exists_eventually_dist_zero`: it yields
`d(t, T_k) ≤ toReal · (√2)^{−k} → 0`, uniformly on any finite subset. -/
lemma sqrt_two_pow_mul_infDist_le_toReal_gammaFunctional {T : Set E}
    (A : AdmissibleSequence T)
    -- LEAN-ONLY: finite series (the ⊤ branch is trivial in the consumers)
    (hA : gammaFunctional A ≠ ⊤) {t : E}
    -- LEAN-ONLY: the point lives in the carrier
    (ht : t ∈ T) (k : ℕ) :
    Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k)
      ≤ (gammaFunctional A).toReal := by
  have hle : ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
      ≤ gammaFunctional A := by
    refine le_trans (ENNReal.le_tsum (f := fun k =>
      ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))) k) ?_
    exact le_iSup₂ (f := fun t (_ : t ∈ T) =>
      ∑' k, ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))) t ht
  have := ENNReal.toReal_mono hA hle
  rwa [ENNReal.toReal_ofReal
    (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) k) Metric.infDist_nonneg)] at this

/-- Finiteness of γ₂ for finite `T` (HDP §8.5.2, proof Step 1, "T finite
makes γ₂ finite"): the exhausting sequence `seq k = T` once `2^{2^k} ≥ |T|`
makes the series a finite sum. -/
lemma gammaTwo_lt_top_of_finite {T : Set E}
    -- LEAN-ONLY: T finite (the exhausting sequence exists)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness (γ₂ ∅ = ⊤ junk)
    (hne : T.Nonempty) :
    gammaTwo T < ⊤ := by
  classical
  obtain ⟨a, ha⟩ := hne
  have hFne : hfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]; exact ⟨a, ha⟩
  set N : ℕ := hfin.toFinset.card with hN
  -- threshold: `N ≤ 2 ^ 2 ^ N`
  have hk₀ : N ≤ 2 ^ 2 ^ N := by
    have h1 : N ≤ 2 ^ N := (Nat.lt_two_pow_self).le
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) h1)
  -- exhausting admissible sequence: singleton until `2 ^ 2 ^ k` covers `T`
  set seq : ℕ → Finset E :=
    fun k => if 1 ≤ k ∧ N ≤ 2 ^ 2 ^ k then hfin.toFinset else {a} with hseq
  have hseq_sub : ∀ k, ↑(seq k) ⊆ T := by
    intro k; rw [hseq]; dsimp only; split
    · rw [hfin.coe_toFinset]
    · rw [Finset.coe_singleton, Set.singleton_subset_iff]; exact ha
  have hseq_ne : ∀ k, (seq k).Nonempty := by
    intro k; rw [hseq]; dsimp only; split
    · exact hFne
    · exact Finset.singleton_nonempty a
  have hseq_card0 : (seq 0).card = 1 := by
    rw [hseq]; dsimp only
    rw [if_neg (by omega)]; exact Finset.card_singleton a
  have hseq_cardle : ∀ k, (seq k).card ≤ 2 ^ 2 ^ k := by
    intro k; rw [hseq]; dsimp only; split
    · rename_i h; rw [← hN]; exact h.2
    · rw [Finset.card_singleton]; exact Nat.one_le_pow _ _ (by norm_num)
  set A : AdmissibleSequence T :=
    { seq := seq, subset_carrier := hseq_sub, nonempty := hseq_ne,
      card_zero := hseq_card0, card_le := hseq_cardle } with hA
  have hAseq : ∀ k, A.seq k = seq k := fun k => by rw [hA]
  refine lt_of_le_of_lt (gammaTwo_le A) ?_
  -- uniform bound `M` on the distances to `a`
  set M : ℝ := hfin.toFinset.sup' hFne (fun x => dist x a) with hM
  set B : ℝ≥0∞ := ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (Real.sqrt 2 ^ k * M) with hB
  have hBfin : B < ⊤ := by
    rw [hB, ENNReal.sum_lt_top]; intro k _; exact ENNReal.ofReal_lt_top
  refine lt_of_le_of_lt (b := B) ?_ hBfin
  simp only [gammaFunctional, hAseq]
  refine iSup₂_le (fun t ht => ?_)
  -- terms vanish once the net has caught up with `T`
  have hzero : ∀ k ∉ Finset.range (N + 1),
      ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(seq k)) = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    have hk1 : 1 ≤ k := le_trans (by omega) hk
    have hNk : N ≤ k := le_trans (Nat.le_succ N) hk
    have hcond : N ≤ 2 ^ 2 ^ k :=
      hk₀.trans (Nat.pow_le_pow_right (by norm_num)
        (Nat.pow_le_pow_right (by norm_num) hNk))
    have hseqk : seq k = hfin.toFinset := by
      rw [hseq]; dsimp only; rw [if_pos ⟨hk1, hcond⟩]
    have hinf : Metric.infDist t ↑(seq k) = 0 := by
      rw [hseqk, hfin.coe_toFinset]; exact Metric.infDist_zero_of_mem ht
    rw [hinf, mul_zero, ENNReal.ofReal_zero]
  rw [tsum_eq_sum hzero, hB]
  refine Finset.sum_le_sum (fun k _ => ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Real.sqrt_nonneg 2) k)
  have ha_in : a ∈ ↑(seq k) := by
    rw [hseq]; dsimp only; split
    · exact Finset.mem_coe.mpr (hfin.mem_toFinset.mpr ha)
    · exact Finset.mem_coe.mpr (Finset.mem_singleton_self a)
  calc Metric.infDist t ↑(seq k) ≤ dist t a := Metric.infDist_le_dist_of_mem ha_in
    _ ≤ M := by rw [hM]; exact Finset.le_sup' (fun x => dist x a) (hfin.mem_toFinset.mpr ht)

/-- Pseudometric-safe chain end (HDP §8.5.2, proof Step 1, the "some `K` has
`T_K = T`" step): finite `T` + finite functional force the series terms to
`0`, so eventually every point of `T` has a net point at distance `0`. -/
lemma AdmissibleSequence.exists_eventually_dist_zero {T : Set E}
    -- LEAN-ONLY: T finite (finitely many values, series terms → 0)
    (hfin : T.Finite) {A : AdmissibleSequence T}
    -- LEAN-ONLY: finite functional (otherwise the series carries no
    -- information); HDP §8.5.2 Step 1
    (hA : gammaFunctional A ≠ ⊤) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ t ∈ T, ∃ a ∈ A.seq k, dist t a = 0 := by
  classical
  set G : ℝ := (gammaFunctional A).toReal with hG
  -- Per-term bound: `√2^k · d(t, T_k) ≤ γ₂(A)` (from `le_tsum` + `le_iSup₂`).
  have hterm : ∀ t ∈ T, ∀ k,
      Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k) ≤ G := by
    intro t ht k
    have hle : ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
        ≤ gammaFunctional A := by
      refine le_trans (ENNReal.le_tsum (f := fun k =>
        ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))) k) ?_
      exact le_iSup₂ (f := fun t (_ : t ∈ T) =>
        ∑' k, ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))) t ht
    have := ENNReal.toReal_mono hA hle
    rwa [ENNReal.toReal_ofReal
      (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) k) Metric.infDist_nonneg)] at this
  -- Positive-distance floor: `1` together with the finite set of positive
  -- pairwise distances in `T` (using `insert 1` to stay nonempty unconditionally).
  obtain ⟨δ, hδpos, hfloor⟩ :
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ T, ∀ s' ∈ T, dist s s' ≠ 0 → δ ≤ dist s s' := by
    set Pos : Finset ℝ :=
      ((hfin.toFinset ×ˢ hfin.toFinset).image (fun p => dist p.1 p.2)).filter (fun d => 0 < d)
      with hPos
    -- membership witness for a positive distance
    have hmem_of : ∀ s ∈ T, ∀ s' ∈ T, dist s s' ≠ 0 → dist s s' ∈ Pos := by
      intro s hs s' hs' hne0
      have hpos : 0 < dist s s' := lt_of_le_of_ne dist_nonneg (Ne.symm hne0)
      rw [hPos, Finset.mem_filter]
      refine ⟨?_, hpos⟩
      rw [Finset.mem_image]
      refine ⟨(s, s'), ?_, rfl⟩
      rw [Finset.mem_product]
      exact ⟨hfin.mem_toFinset.mpr hs, hfin.mem_toFinset.mpr hs'⟩
    by_cases hPne : Pos.Nonempty
    · refine ⟨Pos.min' hPne, ?_, ?_⟩
      · have hmin := Finset.min'_mem Pos hPne
        exact (Finset.mem_filter.mp hmin).2
      · intro s hs s' hs' hne0
        exact Finset.min'_le Pos (dist s s') (hmem_of s hs s' hs' hne0)
    · refine ⟨1, one_pos, ?_⟩
      intro s hs s' hs' hne0
      exact absurd ⟨dist s s', hmem_of s hs s' hs' hne0⟩ hPne
  -- `√2^k → ∞`, so eventually `G/δ < √2^k`.
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using this
  have htend : Filter.Tendsto (fun k : ℕ => Real.sqrt 2 ^ k) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt h1
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp (htend.eventually_gt_atTop (G / δ))
  refine ⟨k₀, fun k hk_ge t ht => ?_⟩
  -- infDist is attained on the finite (hence compact) net.
  have hcpt : IsCompact (↑(A.seq k) : Set E) := (A.seq k).finite_toSet.isCompact
  have hne : (↑(A.seq k) : Set E).Nonempty := Finset.coe_nonempty.mpr (A.nonempty k)
  obtain ⟨a, ha_mem, ha_eq⟩ := hcpt.exists_infDist_eq_dist hne t
  have haT : a ∈ T := A.subset_carrier k ha_mem
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 ^ k := pow_pos (by linarith) k
  -- `d(t, T_k) ≤ G / √2^k < δ`.
  have hb := hterm t ht k
  rw [mul_comm] at hb
  have hinf_le : Metric.infDist t ↑(A.seq k) ≤ G / Real.sqrt 2 ^ k :=
    (le_div_iff₀ hsqrt_pos).mpr hb
  have hGd : G / Real.sqrt 2 ^ k < δ := by
    have hk := hk₀ k hk_ge
    rw [div_lt_iff₀ hδpos] at hk
    rw [div_lt_iff₀ hsqrt_pos]; linarith
  have hinf_lt : Metric.infDist t ↑(A.seq k) < δ := lt_of_le_of_lt hinf_le hGd
  -- So `d(t, a) < δ`; the floor forces `d(t, a) = 0`.
  have hdt : dist t a < δ := by rw [← ha_eq]; exact hinf_lt
  have hzero : dist t a = 0 := by
    by_contra hcon
    exact absurd hdt (not_lt.mpr (hfloor t ht a haT hcon))
  exact ⟨a, Finset.mem_coe.mp ha_mem, hzero⟩

/-- The `k = 0` term of the γ₂ series (HDP §8.5.2): the distance to the root
singleton is dominated by the functional. -/
lemma ofReal_infDist_zero_le_gammaFunctional {T : Set E}
    (A : AdmissibleSequence T) {t : E}
    -- LEAN-ONLY: membership so the biSup dominates the t-series
    (ht : t ∈ T) :
    ENNReal.ofReal (Metric.infDist t ↑(A.seq 0)) ≤ gammaFunctional A := by
  have h0 : ENNReal.ofReal (Metric.infDist t ↑(A.seq 0))
      = ENNReal.ofReal (Real.sqrt 2 ^ 0 * Metric.infDist t ↑(A.seq 0)) := by
    rw [pow_zero, one_mul]
  rw [h0]
  refine le_trans (ENNReal.le_tsum (f := fun k =>
    ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))) 0) ?_
  exact le_iSup₂ (f := fun t (_ : t ∈ T) =>
    ∑' k, ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))) t ht

/-- Diameter domination (HDP §8.5.2, proof Step 3): `seq 0` is a singleton
`{a₀}` and `diam T ≤ 2 sup_t d(t, a₀)`; absorbs the `u·diam` term of the
tail event into `u·γ₂`. -/
lemma ofReal_diam_le_two_mul_gammaFunctional {T : Set E}
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty)
    -- LEAN-ONLY: boundedness so `Metric.diam` is meaningful
    (hbd : Bornology.IsBounded T)
    (A : AdmissibleSequence T) :
    ENNReal.ofReal (Metric.diam T) ≤ 2 * gammaFunctional A := by
  rcases eq_or_ne (gammaFunctional A) ⊤ with htop | htop
  · rw [htop, ENNReal.mul_top (by norm_num)]; exact le_top
  · obtain ⟨a₀, ha₀⟩ := Finset.card_eq_one.mp A.card_zero
    -- per-point bound `‖dist x a₀‖ ≤ γ`
    have hpt : ∀ x ∈ T, ENNReal.ofReal (dist x a₀) ≤ gammaFunctional A := by
      intro x hx
      have h := ofReal_infDist_zero_le_gammaFunctional A hx
      rwa [ha₀, Finset.coe_singleton, Metric.infDist_singleton] at h
    have hptR : ∀ x ∈ T, dist x a₀ ≤ (gammaFunctional A).toReal := by
      intro x hx
      have h := ENNReal.toReal_mono htop (hpt x hx)
      rwa [ENNReal.toReal_ofReal dist_nonneg] at h
    have hdiam : Metric.diam T ≤ 2 * (gammaFunctional A).toReal := by
      refine Metric.diam_le_of_forall_dist_le (by positivity) (fun x hx y hy => ?_)
      calc dist x y ≤ dist x a₀ + dist a₀ y := dist_triangle x a₀ y
        _ = dist x a₀ + dist y a₀ := by rw [dist_comm a₀ y]
        _ ≤ (gammaFunctional A).toReal + (gammaFunctional A).toReal :=
            add_le_add (hptR x hx) (hptR y hy)
        _ = 2 * (gammaFunctional A).toReal := by ring
    calc ENNReal.ofReal (Metric.diam T)
        ≤ ENNReal.ofReal (2 * (gammaFunctional A).toReal) := ENNReal.ofReal_le_ofReal hdiam
      _ = 2 * gammaFunctional A := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal htop,
            ENNReal.ofReal_ofNat]

end StatLean.ConcentrationInequalities
