module
public import StatLean.StatisticalModels.Survival.CumulativeHazard
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-!
# Right censoring — the random censorship model and crude = net hazard

The observation side of survival analysis. Full datum `(T, C)` — event time and censoring
time — is observed as `(T ∧ C, 1{T ≤ C})`:

* `censorObserve` — the coarsening map;
* `censoredLaw μT μC` — the observed-data law under **independent censoring** (the random
  censorship model: the product joint law made structural);
* `observedTimeLaw P` / `uncensoredSubLaw P` — the law of the observed time `T̃` and the
  `Δ = 1` sub-distribution `P(T̃ ∈ ·, Δ = 1)` of an arbitrary observed-data law `P`;
* `crudeCumHazard P` — the crude (observable) cumulative hazard: `Δ = 1` event increments
  over the at-risk denominator `P(T̃ ≥ t)`.

**Headline (S2.3, `crudeCumHazard_censoredLaw`).** Under independent censoring the crude
hazard **is** the net hazard of `T` on the region where censoring survives:
$$\tilde\Lambda(dt) = \Lambda_T(dt)\quad\text{on } \{t : S_C(t^-) > 0\}.$$
This is the identifiability theorem licensing Nelson–Aalen/Kaplan–Meier estimation from
censored data, in exact measure form — no continuity, no atomlessness. Its engine is the
fully general sub-distribution formula (S2.2): `P(T̃ ∈ dt, Δ = 1) = S_C(t^-)\,dF_T(t)`.

**Reference.** ABGK §III.2 (random censorship, the observed intensities) (verify §);
E. L. Kaplan and P. Meier, *J. Amer. Statist. Assoc.* **53** (1958), 457–481, §2 (the
crude-vs-net identification) (`KM58 §2`); the nonidentifiability of the joint law without
independence: A. Tsiatis, "A nonidentifiability aspect of the problem of competing risks,"
*Proc. Nat. Acad. Sci.* **72** (1975), 20–22 (`Tsiatis75`) — documented as a non-theorem
here; the dependent-censoring counterexample construction is a named future debt.

**Proof formalization notes.** Tie convention `Δ = decide (T ≤ C)` (ties count as events) —
*Book vs Lean:* ABGK assume `P(T = C) = 0`, making the convention immaterial there. S2.2 is
`Measure.prod` + Fubini section computation (`{c | t ≤ c} = Ici t`) — the β-reduction gotcha
of `Measure.prod_apply` applies (use `simp_rw`/`change`). S2.3 merges the two `withDensity`
layers and cancels `S_C(t^-) · (S_T(t^-) S_C(t^-))⁻¹ = S_T(t^-)⁻¹` in `ℝ≥0∞`; on
`{S_C(t^-) = 0}` the ENNReal convention `0 · ∞ = 0` makes the crude side vanish — that region
is exactly what the `restrict` in the statement removes.

**Bibliographic comments.** The random censorship model is Gilbert's 1962 thesis and
Breslow–Crowley, *Ann. Statist.* **2** (1974), 437–453; the measure-level crude/net calculus
follows ABGK §III.2.
-/

open MeasureTheory Set
open scoped ENNReal

namespace StatLean.StatisticalModels.Survival

/-- The right-censoring coarsening map `(t, c) ↦ (t ∧ c, 1{t ≤ c})`
(tie convention: ties are events; KM58 §2). -/
noncomputable def censorObserve : ℝ × ℝ → ℝ × Bool :=
  fun p => (min p.1 p.2, decide (p.1 ≤ p.2))

/-- The coarsening map is measurable (LEAN-ONLY plumbing). -/
theorem measurable_censorObserve : Measurable censorObserve := by
  refine (measurable_fst.min measurable_snd).prodMk (measurable_to_bool ?_)
  have hset : (fun p : ℝ × ℝ => decide (p.1 ≤ p.2)) ⁻¹' {true} = {p : ℝ × ℝ | p.1 ≤ p.2} := by
    ext p; simp
  rw [hset]
  exact measurableSet_le measurable_fst measurable_snd

/-- The **random censorship model**: the observed-data law under independent censoring —
the product joint `(T, C) ∼ μT ⊗ μC` pushed through `censorObserve` (ABGK §III.2;
Breslow–Crowley 1974). Independence is structural here, not a hypothesis. -/
noncomputable def censoredLaw (μT μC : Measure ℝ) : Measure (ℝ × Bool) :=
  (μT.prod μC).map censorObserve

instance (μT μC : Measure ℝ) [IsProbabilityMeasure μT] [IsProbabilityMeasure μC] :
    IsProbabilityMeasure (censoredLaw μT μC) :=
  Measure.isProbabilityMeasure_map measurable_censorObserve.aemeasurable

/-- The law of the observed time `T̃` of an observed-data law. -/
noncomputable def observedTimeLaw (P : Measure (ℝ × Bool)) : Measure ℝ :=
  P.map Prod.fst

/-- The `Δ = 1` (uncensored) **sub-distribution** `P(T̃ ∈ ·, Δ = 1)`. -/
noncomputable def uncensoredSubLaw (P : Measure (ℝ × Bool)) : Measure ℝ :=
  (P.restrict {p | p.2 = true}).map Prod.fst

/-- The **crude cumulative hazard** of an observed-data law: uncensored event increments
over the at-risk probability `P(T̃ ≥ t)` (ABGK §III.2). -/
noncomputable def crudeCumHazard (P : Measure (ℝ × Bool)) : Measure ℝ :=
  (uncensoredSubLaw P).withDensity fun t => (observedTimeLaw P (Ici t))⁻¹

/-- LEAN-ONLY: the observed time is the pushforward of the joint law under `min`
(`Prod.fst ∘ censorObserve = min`, collapsed by `Measure.map_map`). -/
private theorem observedTimeLaw_censoredLaw_eq (μT μC : Measure ℝ) :
    observedTimeLaw (censoredLaw μT μC) = (μT.prod μC).map fun p => min p.1 p.2 := by
  rw [observedTimeLaw, censoredLaw, Measure.map_map measurable_fst measurable_censorObserve]
  rfl

/-- **S2.1 (observed survival factorizes, `Ioi` form)**: under independent censoring
`P(T̃ > t) = S_T(t) · S_C(t)` (ABGK §III.2). -/
theorem observedTimeLaw_censoredLaw_Ioi (μT μC : Measure ℝ) [IsProbabilityMeasure μT]
    [IsProbabilityMeasure μC] (t : ℝ) :
    observedTimeLaw (censoredLaw μT μC) (Ioi t) = μT (Ioi t) * μC (Ioi t) := by
  rw [observedTimeLaw_censoredLaw_eq,
    Measure.map_apply (measurable_fst.min measurable_snd) measurableSet_Ioi]
  have hpre : (fun p : ℝ × ℝ => min p.1 p.2) ⁻¹' Ioi t = Ioi t ×ˢ Ioi t := by
    ext p; simp
  rw [hpre, Measure.prod_prod]

/-- **S2.1 (`Ici` form)**: `P(T̃ ≥ t) = S_T(t^-) · S_C(t^-)`. -/
theorem observedTimeLaw_censoredLaw_Ici (μT μC : Measure ℝ) [IsProbabilityMeasure μT]
    [IsProbabilityMeasure μC] (t : ℝ) :
    observedTimeLaw (censoredLaw μT μC) (Ici t) = μT (Ici t) * μC (Ici t) := by
  rw [observedTimeLaw_censoredLaw_eq,
    Measure.map_apply (measurable_fst.min measurable_snd) measurableSet_Ici]
  have hpre : (fun p : ℝ × ℝ => min p.1 p.2) ⁻¹' Ici t = Ici t ×ˢ Ici t := by
    ext p; simp [Prod.le_def]
  rw [hpre, Measure.prod_prod]

/-- **S2.2 (sub-distribution formula, fully general)**: under independent censoring,
`P(T̃ ∈ dt, Δ = 1) = S_C(t^-)\,dF_T(t)` — exactly, for arbitrary (atomic or not) laws
(ABGK §III.2; KM58 §2). -/
theorem uncensoredSubLaw_censoredLaw (μT μC : Measure ℝ) [IsProbabilityMeasure μT]
    [IsProbabilityMeasure μC] :
    uncensoredSubLaw (censoredLaw μT μC) = μT.withDensity fun t => μC (Ici t) := by
  refine Measure.ext fun A hA => ?_
  have hE : MeasurableSet {p : ℝ × Bool | p.2 = true} :=
    measurable_snd (measurableSet_singleton true)
  have hle : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hS : MeasurableSet (Prod.fst ⁻¹' A ∩ {p : ℝ × ℝ | p.1 ≤ p.2}) :=
    (measurable_fst hA).inter hle
  -- The `Δ = 1` event pulls back to `{p | p.1 ∈ A ∧ p.1 ≤ p.2}`, where `min p.1 p.2 = p.1`.
  have hpre : censorObserve ⁻¹' (Prod.fst ⁻¹' A ∩ {p : ℝ × Bool | p.2 = true})
      = Prod.fst ⁻¹' A ∩ {p : ℝ × ℝ | p.1 ≤ p.2} := by
    ext p
    simp only [censorObserve, mem_preimage, mem_inter_iff, mem_setOf_eq, decide_eq_true_eq]
    constructor
    · exact fun ⟨h1, h2⟩ => ⟨by rwa [min_eq_left h2] at h1, h2⟩
    · exact fun ⟨h1, h2⟩ => ⟨by rwa [min_eq_left h2], h2⟩
  rw [uncensoredSubLaw, Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (measurable_fst hA), censoredLaw,
    Measure.map_apply measurable_censorObserve ((measurable_fst hA).inter hE), hpre,
    Measure.prod_apply hS, withDensity_apply _ hA]
  -- Fubini section: `{c | t ≤ c} = Ici t` on `A`, empty off `A`.
  have hsec : ∀ x : ℝ, μC (Prod.mk x ⁻¹' (Prod.fst ⁻¹' A ∩ {p : ℝ × ℝ | p.1 ≤ p.2}))
      = A.indicator (fun t => μC (Ici t)) x := by
    intro x
    by_cases hx : x ∈ A
    · have : Prod.mk x ⁻¹' (Prod.fst ⁻¹' A ∩ {p : ℝ × ℝ | p.1 ≤ p.2}) = Ici x := by
        ext y; simp [hx]
      rw [this, indicator_of_mem hx]
    · have : Prod.mk x ⁻¹' (Prod.fst ⁻¹' A ∩ {p : ℝ × ℝ | p.1 ≤ p.2}) = (∅ : Set ℝ) := by
        ext y; simp [hx]
      rw [this, indicator_of_notMem hx, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator hA]

/-- **S2.3, HEADLINE (crude = net hazard)**: under independent censoring the crude cumulative
hazard of the observed data equals the net cumulative hazard of the event-time law, restricted
to the region where censoring survives — the exact identifiability theorem licensing
Nelson–Aalen/Kaplan–Meier from censored data (ABGK §III.2; KM58 §2; positively resolving the
region where `Tsiatis75` nonidentifiability cannot bite). -/
theorem crudeCumHazard_censoredLaw (μT μC : Measure ℝ) [IsProbabilityMeasure μT]
    [IsProbabilityMeasure μC] :
    crudeCumHazard (censoredLaw μT μC) = (cumHazard μT).restrict {t | 0 < μC (Ici t)} := by
  have hmC : Measurable fun t : ℝ => μC (Ici t) :=
    Antitone.measurable fun _ _ hab => measure_mono (Ici_subset_Ici.2 hab)
  have hmT : Measurable fun t : ℝ => μT (Ici t) :=
    Antitone.measurable fun _ _ hab => measure_mono (Ici_subset_Ici.2 hab)
  have hS : MeasurableSet {t : ℝ | 0 < μC (Ici t)} := hmC measurableSet_Ioi
  -- Right-hand side: restrict-of-`withDensity` is `withDensity` of the indicator density.
  rw [cumHazard, restrict_withDensity hS, ← withDensity_indicator hS]
  -- Left-hand side: S2.2 for the sub-law, S2.1 (`Ici`) for the at-risk denominator, then
  -- merge the two `withDensity` layers.
  rw [crudeCumHazard]
  simp only [observedTimeLaw_censoredLaw_Ici]
  rw [uncensoredSubLaw_censoredLaw, ← withDensity_mul _ hmC (hmT.fun_mul hmC).fun_inv]
  congr 1
  funext t
  -- Pointwise: `a · (b·a)⁻¹ = b⁻¹` when `a ≠ 0`, and `= 0` when `a = 0` (`0 · ∞ = 0`).
  rcases eq_or_ne (μC (Ici t)) 0 with h0 | h0
  · rw [Pi.mul_apply, h0, zero_mul, indicator_of_notMem]
    simp [h0]
  · have htop : μC (Ici t) ≠ ⊤ := measure_ne_top μC _
    rw [Pi.mul_apply, indicator_of_mem (by exact pos_iff_ne_zero.2 h0),
      ENNReal.mul_inv (Or.inr htop) (Or.inr h0), ← mul_assoc, mul_comm (μC (Ici t)),
      mul_assoc, ENNReal.mul_inv_cancel h0 htop, mul_one]

/-- The uncensored sub-law is dominated by the observed-time law (LEAN-ONLY; the
restrict-monotonicity workhorse for S2.3). -/
-- LEAN-ONLY: measurability of the event; standard regularity
theorem uncensoredSubLaw_le (P : Measure (ℝ × Bool)) {A : Set ℝ} (hA : MeasurableSet A) :
    uncensoredSubLaw P A ≤ observedTimeLaw P A := by
  rw [uncensoredSubLaw, observedTimeLaw, Measure.map_apply measurable_fst hA,
    Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
  exact measure_mono inter_subset_left

end StatLean.StatisticalModels.Survival
