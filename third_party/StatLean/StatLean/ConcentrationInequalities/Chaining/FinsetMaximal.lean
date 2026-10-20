module
public import StatLean.ConcentrationInequalities.Maximal.FiniteMaximal

@[expose] public section

/-!
# Finset-indexed maximal inequalities for sub-Gaussian variables

Finset-indexed adapters of the existing `Fin d`-indexed maximal inequalities
(`Maximal/FiniteMaximal.lean`): for a nonempty finite index set
$s$ and centered sub-Gaussian variables $(X_i)_{i \in s}$ with variance
proxy $\sigma^2$,
$$ \mathbb{P}\Bigl(\max_{i \in s} X_i > t\Bigr)
     \le |s|\, e^{-t^2/(2\sigma^2)}, \qquad
   \mathbb{E}\Bigl[\max_{i \in s} X_i\Bigr] \le \sigma \sqrt{2 \log |s|}, $$
so that chaining levels can take maxima over pair-Finsets (`closePairs`)
directly, without re-indexing to `Fin d` at every level.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §2.5, Eq. (2.22) / Exercise 2.5.10; the underlying
`Fin d` theorems are Lu, *Big Data Analysis*, §6.2, Theorem 6.2 (Finite
Maximal Inequality). Used at each chaining level in HDP §8.1, Eq. (8.11).

**Proof formalization notes.** Pure reindexing via `s.equivFin` of
`tail_max_le` and `expectation_max_le` (`Maximal/FiniteMaximal.lean`) — no
new probabilistic content. Carriers: the tail form takes the set-bounded
supremum `⨆ i ∈ s, X i ω` (junk-safe there since the threshold is `≥ 0`),
while the expectation form is stated with the junk-free `Finset.sup'`
maximum, exactly mirroring the proven `Fin`-indexed `expectation_max_le`.
`biSup_finset_eq_sup'` (and its sharp core
`biSup_finset_eq_sup'_of_sup'_nonneg`) converts between the two carriers
under the nonnegativity guard; `le_biSup_finset` is the unconditional member
bound; `integrable_biSup_finset` / `integrable_sup'_finset` are the public
Finset twins of `FiniteMaximal`'s private domination helper.

**Bibliographic comments.** The maximal inequality for finitely many
sub-Gaussian variables is folklore via the Cramér–Chernoff method; the
standard modern reference is S. Boucheron, G. Lugosi, and P. Massart,
*Concentration Inequalities: A Nonasymptotic Theory of Independence*, Oxford
University Press, 2013, §2.5. No single seminal attribution is appropriate.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Conversion between the set-bounded supremum `⨆ i ∈ s, f i` and
`Finset.sup'` over a nonempty Finset — sharp form.

Junk-value caveat (why `h0` is REQUIRED, statement fix at the debt gate): over
a general `f : ι → ℝ` the unguarded equality is **false**: the outer
`⨆ i, ⨆ (_ : i ∈ s), f i` ranges over *all* of `ι`, and for `i ∉ s` the inner
supremum is the junk value `sSup (∅ : Set ℝ) = 0`. Hence
`⨆ i ∈ s, f i = max (s.sup' hs f) 0` whenever `ι \ s ≠ ∅`, so e.g.
`⨆ i ∈ ({0} : Finset ℕ), (-1 : ℝ) = 0 ≠ -1 = sup'`. `0 ≤ s.sup' hs f` is the
sharp hypothesis under which the identity holds; anchored chaining families
(containing a `0` member value) supply it via `Finset.le_sup'_of_le`. -/
lemma biSup_finset_eq_sup'_of_sup'_nonneg {ι : Type*} {s : Finset ι}
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined and the real biSup
    -- is not junk; no book content
    (hs : s.Nonempty) (f : ι → ℝ)
    -- LEAN-ONLY: nonnegative maximum — the sharp junk-value guard (see
    -- docstring); no book content
    (h0 : 0 ≤ s.sup' hs f) :
    (⨆ i ∈ s, f i) = s.sup' hs f := by
  classical
  -- Each inner supremum branch is `≤ sup'`: `f i` when `i ∈ s`, junk `0` otherwise.
  have hbranch : ∀ i, (⨆ (_ : i ∈ s), f i) ≤ s.sup' hs f := by
    intro i
    by_cases hi : i ∈ s
    · rw [ciSup_pos hi]; exact Finset.le_sup' f hi
    · haveI : IsEmpty (i ∈ s) := ⟨hi⟩
      rw [Real.iSup_of_isEmpty]; exact h0
  have hbdd : BddAbove (Set.range (fun i => ⨆ (_ : i ∈ s), f i)) :=
    ⟨s.sup' hs f, by rintro y ⟨i, rfl⟩; exact hbranch i⟩
  refine le_antisymm (Real.iSup_le hbranch h0) ?_
  obtain ⟨j, hj, hje⟩ := Finset.exists_mem_eq_sup' hs f
  rw [hje]
  exact le_ciSup_of_le hbdd j (le_of_eq (ciSup_pos (f := fun _ => f j) hj).symm)

/-- Conversion between the set-bounded supremum `⨆ i ∈ s, f i` and
`Finset.sup'`, nonnegative-family form (the shape every `|·|`-valued chaining
call site consumes, supplied uniformly as `fun i _ => abs_nonneg _`). See
`biSup_finset_eq_sup'_of_sup'_nonneg` for the sharp hypothesis and the
junk-value discussion. -/
lemma biSup_finset_eq_sup' {ι : Type*} {s : Finset ι}
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined and the real biSup
    -- is not junk; no book content
    (hs : s.Nonempty) (f : ι → ℝ)
    -- LEAN-ONLY: nonnegative family — junk-value guard (statement fix at the
    -- debt gate: for i ∉ s the inner sup is junk 0, so the unguarded identity
    -- is FALSE for negative values); no book content
    (h0 : ∀ i ∈ s, 0 ≤ f i) :
    (⨆ i ∈ s, f i) = s.sup' hs f := by
  obtain ⟨i₀, hi₀⟩ := id hs
  exact biSup_finset_eq_sup'_of_sup'_nonneg hs f
    ((h0 i₀ hi₀).trans (Finset.le_sup' f hi₀))

/-- A member value is dominated by the set-bounded supremum, unconditionally:
the junk branches only push the real biSup *up*
(`⨆ i ∈ s, f i = max (s.sup' _ f) 0` for `ι ⊋ s`), so no nonnegativity is
needed for the `≤` direction. -/
lemma le_biSup_finset {ι : Type*} {s : Finset ι} (f : ι → ℝ) {i : ι}
    (hi : i ∈ s) : f i ≤ ⨆ j ∈ s, f j := by
  classical
  have hs : s.Nonempty := ⟨i, hi⟩
  have hbdd : BddAbove (Set.range (fun j => ⨆ (_ : j ∈ s), f j)) := by
    refine ⟨max (s.sup' hs f) 0, ?_⟩
    rintro y ⟨j, rfl⟩
    dsimp only
    by_cases hj : j ∈ s
    · rw [ciSup_pos hj]; exact le_max_of_le_left (Finset.le_sup' f hj)
    · haveI : IsEmpty (j ∈ s) := ⟨hj⟩
      rw [Real.iSup_of_isEmpty]; exact le_max_right _ _
  exact le_ciSup_of_le hbdd i (le_of_eq (ciSup_pos (f := fun _ => f i) hi).symm)

/-- Integrability of the pointwise `Finset.sup'` of finitely many integrable
functions (junk-free twin of `integrable_biSup_finset`; the engine behind the
`sup'`-carried chaining level suprema). -/
lemma integrable_sup'_finset {ι : Type*} {s : Finset ι}
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined; no book content
    (hs : s.Nonempty) {X : ι → Ω → ℝ}
    -- LEAN-ONLY: per-index integrability, dominates the finite sup; HDP §8.1
    (hint : ∀ i ∈ s, MeasureTheory.Integrable (X i) μ) :
    MeasureTheory.Integrable (fun ω => s.sup' hs (fun i => X i ω)) μ := by
  classical
  revert hint
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      intro hint
      -- `sup'_singleton` is `rfl`, so the goal is defeq to `Integrable (X a) μ`.
      exact hint a (by simp)
  | cons a t ha ht ih =>
      intro hint
      -- `sup'_cons` needs the tail's nonemptiness `ht` supplied (RHS-only arg).
      simp only [Finset.sup'_cons ht]
      exact (hint a (by simp)).sup (ih (fun i hi => hint i (by simp [hi])))

set_option maxHeartbeats 1000000 in
/-- The pointwise supremum over a nonempty finite index set of integrable
functions is integrable (public Finset twin of the private domination helper
in `Maximal/FiniteMaximal.lean`). -/
lemma integrable_biSup_finset {ι : Type*} {s : Finset ι}
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value; HDP §8.1
    (hs : s.Nonempty) {X : ι → Ω → ℝ}
    -- LEAN-ONLY: per-index integrability, dominates the finite sup; HDP §8.1
    (hint : ∀ i ∈ s, MeasureTheory.Integrable (X i) μ) :
    MeasureTheory.Integrable (fun ω => ⨆ i ∈ s, X i ω) μ := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  -- pointwise domination by the sum of absolute values
  have hbdd : ∀ ω, BddAbove (Set.range (fun i => ⨆ (_ : i ∈ s), X i ω)) := by
    intro ω
    refine ⟨∑ i ∈ s, |X i ω|, ?_⟩
    rintro y ⟨i, rfl⟩
    dsimp only
    by_cases hi : i ∈ s
    · rw [ciSup_pos hi]
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |X i ω|) (fun i _ => abs_nonneg (X i ω)) hi)
    · haveI : IsEmpty (i ∈ s) := ⟨hi⟩
      rw [Real.iSup_of_isEmpty]
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hmeas : AEMeasurable (fun ω => ⨆ i ∈ s, X i ω) μ :=
    AEMeasurable.biSup (↑s) s.countable_toSet
      (fun i hi => (hint i (Finset.mem_coe.mp hi)).aemeasurable)
  refine MeasureTheory.Integrable.mono' (g := fun ω => ∑ i ∈ s, |X i ω|)
    (MeasureTheory.integrable_finset_sum s (fun i hi => (hint i hi).abs))
    hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- lower bound: `-∑ ≤ ⨆`
    have hi₀le : X i₀ ω ≤ ⨆ i ∈ s, X i ω :=
      le_ciSup_of_le (hbdd ω) i₀ (le_of_eq (ciSup_pos (f := fun _ => X i₀ ω) hi₀).symm)
    have : -(∑ i ∈ s, |X i ω|) ≤ X i₀ ω := by
      have h1 : -|X i₀ ω| ≤ X i₀ ω := neg_abs_le _
      have h2 : |X i₀ ω| ≤ ∑ i ∈ s, |X i ω| :=
        Finset.single_le_sum (f := fun i => |X i ω|) (fun i _ => abs_nonneg (X i ω)) hi₀
      linarith
    linarith
  · -- upper bound: `⨆ ≤ ∑`
    refine Real.iSup_le (fun i => ?_) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    by_cases hi : i ∈ s
    · rw [ciSup_pos hi]
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |X i ω|) (fun i _ => abs_nonneg (X i ω)) hi)
    · haveI : IsEmpty (i ∈ s) := ⟨hi⟩
      rw [Real.iSup_of_isEmpty]
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- **Finset maximal inequality — tail bound** (Lu-BDA §6.2, Theorem 6.2 /
HDP §2.5, Eq. (2.22)): Finset reindex of `tail_max_le` via `s.equivFin`. -/
theorem tail_max_finset_le {ι : Type*} {s : Finset ι}
    -- LEAN-ONLY: nonemptiness (reindex target `Fin s.card` must be nonempty)
    (hs : s.Nonempty) {σ2 : ℝ≥0} {X : ι → Ω → ℝ}
    -- USER-INPUT: E[X_i] = 0; Lu-BDA §6.2, Theorem 6.2
    (hcenter : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: X_i sub-Gaussian with variance proxy σ²; Lu-BDA §6.2
    (hX : ∀ i ∈ s, IsSubGaussian (X i) σ2 μ)
    -- USER-INPUT: 0 ≤ t (book: t > 0, ours strictly stronger); Lu-BDA §6.2
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < ⨆ i ∈ s, X i ω}
      ≤ ENNReal.ofReal ((s.card : ℝ) * Real.exp (-t ^ 2 / (2 * σ2))) := by
  classical
  -- the max exceeds `t ≥ 0` only if some coordinate does (the biSup junk value
  -- `0` never exceeds `t ≥ 0`, so it drops out of the event)
  have hsub : {ω | t < ⨆ i ∈ s, X i ω} ⊆ ⋃ i ∈ s, {ω | t < X i ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    have hle : (⨆ i ∈ s, X i ω) ≤ t := by
      refine Real.iSup_le (fun i => ?_) ht
      by_cases hi : i ∈ s
      · rw [ciSup_pos hi]; exact hcon i hi
      · haveI : IsEmpty (i ∈ s) := ⟨hi⟩
        rw [Real.iSup_of_isEmpty]; exact ht
    exact absurd hω (not_lt.mpr hle)
  calc μ {ω | t < ⨆ i ∈ s, X i ω}
      ≤ μ (⋃ i ∈ s, {ω | t < X i ω}) := measure_mono hsub
    _ ≤ ∑ i ∈ s, μ {ω | t < X i ω} := measure_biUnion_finset_le s _
    _ ≤ ∑ _i ∈ s, ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * σ2))) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have h := (hX i hi).measure_sub_integral_lt_le ht
        simp only [hcenter i hi, sub_zero] at h
        exact h
    _ = ENNReal.ofReal ((s.card : ℝ) * Real.exp (-t ^ 2 / (2 * σ2))) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- **Finset maximal inequality — expectation bound** (Lu-BDA §6.2, Theorem
6.2 / HDP §2.5, Eq. (2.22)): Finset reindex of `expectation_max_le` via
`s.equivFin`; the per-level engine of HDP §8.1, Eq. (8.11).

Carrier note (statement fix at the debt gate). The conclusion is stated with
the junk-free `Finset.sup'` maximum, exactly mirroring the proven
`Fin`-indexed `expectation_max_le`. The old set-bounded `⨆ i ∈ s, X i ω` form
was **false**: over a general index type `ι ⊋ s` that biSup equals
`(s.sup' _ (X · ω))⁺`, and at `|s| = 1` the RHS is `√σ² · √(2 log 1) = 0`
while `∫ (X_{i₀})⁺` is strictly positive for any non-degenerate centered
sub-Gaussian `X_{i₀}` — a counterexample. Consumers carry the same `sup'`
form (see `discrete_dudley`). -/
theorem expectation_max_finset_le {ι : Type*}
    -- USER-INPUT: probability-space context; Lu-BDA §6.2, Theorem 6.2
    [IsProbabilityMeasure μ] {s : Finset ι}
    -- LEAN-ONLY: nonemptiness (reindex target `Fin s.card` must be nonempty)
    (hs : s.Nonempty) {σ2 : ℝ≥0} {X : ι → Ω → ℝ}
    -- USER-INPUT: E[X_i] = 0; Lu-BDA §6.2, Theorem 6.2
    (hcenter : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: X_i sub-Gaussian with variance proxy σ²; Lu-BDA §6.2
    (hX : ∀ i ∈ s, IsSubGaussian (X i) σ2 μ) :
    -- Statement fix at the debt gate: the conclusion is stated with
    -- `Finset.sup'` (junk-free), exactly mirroring the proven Fin-indexed
    -- `expectation_max_le`; the old biSup form was FALSE at |s| = 1.
    ∫ ω, s.sup' hs (fun i => X i ω) ∂μ
      ≤ Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log s.card) := by
  classical
  -- Reindex `s` to `Fin s.card` via `s.equivFin` and transport the proven
  -- `Fin`-indexed `expectation_max_le`.
  haveI : NeZero s.card := ⟨hs.card_pos.ne'⟩
  set e := s.equivFin with he
  set Y : Fin s.card → Ω → ℝ := fun j ω => X ((e.symm j : ι)) ω with hY
  have hcenterY : ∀ j, ∫ ω, Y j ω ∂μ = 0 := fun j => hcenter _ (e.symm j).2
  have hXY : ∀ j, IsSubGaussian (Y j) σ2 μ := fun j => hX _ (e.symm j).2
  have hbound := expectation_max_le (μ := μ) (X := Y) hcenterY hXY
  -- Pointwise identification of the two maxima carriers.
  have hpt : ∀ ω, s.sup' hs (fun i => X i ω) = ⨆ j : Fin s.card, Y j ω := by
    intro ω
    apply le_antisymm
    · refine Finset.sup'_le hs _ (fun i hi => ?_)
      have hbA : BddAbove (Set.range (fun j : Fin s.card => Y j ω)) :=
        (Set.finite_range _).bddAbove
      refine le_ciSup_of_le hbA (e ⟨i, hi⟩) ?_
      simp [hY, Equiv.symm_apply_apply]
    · refine ciSup_le (fun j => ?_)
      exact Finset.le_sup' (fun i => X i ω) (e.symm j).2
  calc ∫ ω, s.sup' hs (fun i => X i ω) ∂μ
      = ∫ ω, ⨆ j : Fin s.card, Y j ω ∂μ := by simp_rw [hpt]
    _ ≤ Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log s.card) := hbound

end StatLean.ConcentrationInequalities
