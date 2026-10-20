module
public import StatLean.StatisticalModels.Survival.Censoring

@[expose] public section

/-!
# Competing risks — cause-specific hazards and cumulative incidence

Marked event-history observations `(T̃, κ) : ℝ × Option (Fin k)` — `none` = censored,
`some j` = failure from cause `j` (the `k = 1` case subsumes the `ℝ × Bool` censoring
carrier through `toBoolObs`):

* `causeSubLaw P j` — the cause-`j` sub-distribution `P(T̃ ∈ ·, κ = j)`; `cumIncidence` —
  the cumulative incidence function `F_j(t)`;
* `causeSpecificCumHazard P j` — cause-`j` event increments over the all-cause at-risk
  probability (`ABGK §IV.4`-style crude cause-specific hazard);
* **`sum_causeSpecificCumHazard` (S6.1)** — cause-specific hazards add up to the all-cause
  hazard;
* **`causeSubLaw_eq_withDensity` (S6.2)** — the exact CIF identity
  `F_j(dt) = S(t^-)\,Λ_j(dt)` in measure form;
* **`causeSpecificCumHazard_crLaw₂` (S6.3)** — for two *independent* latent cause times,
  the crude cause-specific hazard equals the net hazard of that cause where the other
  survives — the competing-risks mirror of the censoring headline (S2.3), positively
  resolving the identifiable region of Tsiatis's nonidentifiability;
* `graySubCumHazard` — Gray's subdistribution hazard, with its comparison to the
  cause-specific hazard.

`k`-cause crude=net and Aalen–Johansen/multistate are named future debts (D-S6, D-S1).

**Reference.** ABGK §IV.4 (competing risks, cause-specific quantities) (verify §);
R. L. Prentice et al., "The analysis of failure times in the presence of competing risks,"
*Biometrics* **34** (1978), 541–554; A. Tsiatis, *Proc. Nat. Acad. Sci.* **72** (1975),
20–22 (`Tsiatis75`); R. J. Gray, "A class of K-sample tests for comparing the cumulative
incidence of a competing risk," *Ann. Statist.* **16** (1988), 1141–1154 (`Gray88`);
J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a
competing risk," *JASA* **94** (1999), 496–509 (defs only).

**Proof formalization notes.** All identities are `restrict`/`withDensity`/`map`
bookkeeping under the `withDensity`-merge and `0·∞ = 0` conventions; S6.1 is countable
additivity of `restrict` over the
disjoint cause slices; S6.3 replays the S2.3 density-merge with the roles of the two laws
symmetrized. Tie convention in `crObserve₂`: ties go to cause `0` (*Book vs Lean:* the
references assume no ties a.s.).

**Bibliographic comments.** Cause-specific hazards and their sum rule are classical
(Prentice et al. 1978); the CIF-vs-hazard identity is the competing-risks form of the
product-limit relation; the subdistribution hazard is Gray's (1988).
-/

open MeasureTheory Set Finset
open scoped ENNReal

namespace StatLean.StatisticalModels.Survival

variable {k : ℕ}

/-- The mark space carries the discrete σ-algebra (LEAN-ONLY: the pin has no
`MeasurableSpace (Option _)` instance; on a finite type `⊤` is the correct one — it is
exactly what `Bool` carries on the censoring carrier). -/
instance : MeasurableSpace (Option (Fin k)) := ⊤

/-- The observed-time law of a marked observation. -/
noncomputable def observedTimeLawCR (P : Measure (ℝ × Option (Fin k))) : Measure ℝ :=
  P.map Prod.fst

/-- The cause-`j` **sub-distribution** `P(T̃ ∈ ·, κ = j)` (ABGK §IV.4). -/
noncomputable def causeSubLaw (P : Measure (ℝ × Option (Fin k))) (j : Fin k) : Measure ℝ :=
  (P.restrict {p | p.2 = some j}).map Prod.fst

/-- The all-cause (uncensored) sub-distribution `P(T̃ ∈ ·, κ ≠ none)`. -/
noncomputable def allCauseSubLaw (P : Measure (ℝ × Option (Fin k))) : Measure ℝ :=
  (P.restrict {p | p.2 ≠ none}).map Prod.fst

/-- The **cumulative incidence function** `F_j(t) = P(T̃ ≤ t, κ = j)` (Prentice et al.
1978). -/
noncomputable def cumIncidence (P : Measure (ℝ × Option (Fin k))) (j : Fin k) (t : ℝ) :
    ℝ≥0∞ :=
  causeSubLaw P j (Iic t)

/-- The crude **cause-specific cumulative hazard**: cause-`j` increments over the all-cause
at-risk probability (ABGK §IV.4). -/
noncomputable def causeSpecificCumHazard (P : Measure (ℝ × Option (Fin k))) (j : Fin k) :
    Measure ℝ :=
  (causeSubLaw P j).withDensity fun t => (observedTimeLawCR P (Ici t))⁻¹

/-- The all-cause crude cumulative hazard. -/
noncomputable def allCauseCumHazard (P : Measure (ℝ × Option (Fin k))) : Measure ℝ :=
  (allCauseSubLaw P).withDensity fun t => (observedTimeLawCR P (Ici t))⁻¹

/-- **Gray's subdistribution cumulative hazard** (`Gray88`): cause-`j` increments over the
subdistribution at-risk mass `P(Ω) − F_j(t^-)`. -/
noncomputable def graySubCumHazard (P : Measure (ℝ × Option (Fin k))) (j : Fin k) :
    Measure ℝ :=
  (causeSubLaw P j).withDensity fun t => (P univ - causeSubLaw P j (Iio t))⁻¹

/-- The `k = 1` marked carrier collapses to the censoring carrier. -/
def toBoolObs : ℝ × Option (Fin 1) → ℝ × Bool :=
  fun p => (p.1, p.2.isSome)

/-- LEAN-ONLY: every subset of the mark space is measurable (the `⊤` instance above). -/
private theorem measurableSet_mark (s : Set (Option (Fin k))) : MeasurableSet s := trivial

/-- LEAN-ONLY: every map out of the mark space is measurable (the `⊤` instance above). -/
private theorem measurable_mark {α : Type*} [MeasurableSpace α] (g : Option (Fin k) → α) :
    Measurable g := fun _ _ => trivial

/-- LEAN-ONLY: the mark-collapsing map `(t, κ) ↦ (t, g κ)` onto the censoring carrier;
`toBoolObs` is the instance `g = Option.isSome`. -/
private def markObs (g : Option (Fin k) → Bool) : ℝ × Option (Fin k) → ℝ × Bool :=
  fun p => (p.1, g p.2)

/-- LEAN-ONLY: the mark-collapsing map is measurable. -/
private theorem measurable_markObs (g : Option (Fin k) → Bool) : Measurable (markObs g) :=
  measurable_fst.prodMk ((measurable_mark g).comp measurable_snd)

/-- LEAN-ONLY: collapsing the mark does not change the observed-time law. -/
private theorem observedTimeLawCR_markObs (P : Measure (ℝ × Option (Fin k)))
    (g : Option (Fin k) → Bool) :
    observedTimeLawCR P = observedTimeLaw (P.map (markObs g)) := by
  rw [observedTimeLaw, Measure.map_map measurable_fst (measurable_markObs g)]
  rfl

/-- LEAN-ONLY: if `g` is the indicator of the mark `some j`, the cause-`j` sub-law is the
uncensored sub-law of the collapsed observation. -/
private theorem causeSubLaw_markObs (P : Measure (ℝ × Option (Fin k))) (j : Fin k)
    (g : Option (Fin k) → Bool) (hg : ∀ x, g x = true ↔ x = some j) :
    causeSubLaw P j = uncensoredSubLaw (P.map (markObs g)) := by
  have hE : MeasurableSet {q : ℝ × Bool | q.2 = true} :=
    measurable_snd (measurableSet_singleton true)
  have hpre : markObs g ⁻¹' {q : ℝ × Bool | q.2 = true}
      = {p : ℝ × Option (Fin k) | p.2 = some j} := by
    ext p
    simpa [markObs] using hg p.2
  rw [uncensoredSubLaw, Measure.restrict_map (measurable_markObs g) hE, hpre,
    Measure.map_map measurable_fst (measurable_markObs g)]
  rfl

/-- Bridge: the single-cause sub-law is the uncensored sub-law of the collapsed
observation. -/
theorem causeSubLaw_eq_uncensoredSubLaw (P : Measure (ℝ × Option (Fin 1)))
    [IsFiniteMeasure P] (j : Fin 1) :
    causeSubLaw P j = uncensoredSubLaw (P.map toBoolObs) := by
  refine causeSubLaw_markObs P j Option.isSome fun x => ?_
  cases x with
  | none => simp
  | some i => simp [Subsingleton.elim i j]

/-- Sub-laws are dominated by the observed-time law (the restrict-monotonicity
workhorse). -/
theorem causeSubLaw_le (P : Measure (ℝ × Option (Fin k))) (j : Fin k) {A : Set ℝ}
    -- LEAN-ONLY: measurability of the event; standard regularity
    (hA : MeasurableSet A) :
    causeSubLaw P j A ≤ observedTimeLawCR P A := by
  rw [causeSubLaw, observedTimeLawCR, Measure.map_apply measurable_fst hA,
    Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
  exact measure_mono inter_subset_left

/-- **S6.1, hazard additivity** (Prentice et al. 1978; ABGK §IV.4): the cause-specific
cumulative hazards sum to the all-cause crude hazard. -/
theorem sum_causeSpecificCumHazard (P : Measure (ℝ × Option (Fin k))) [IsFiniteMeasure P] :
    ∑ j : Fin k, causeSpecificCumHazard P j = allCauseCumHazard P := by
  -- The cause slices are disjoint and exhaust `{κ ≠ none}`, so the sub-laws add up.
  have hsub : ∑ j : Fin k, causeSubLaw P j = allCauseSubLaw P := by
    refine Measure.ext fun A hA => ?_
    have hAm : MeasurableSet ((Prod.fst : ℝ × Option (Fin k) → ℝ) ⁻¹' A) := measurable_fst hA
    have hSm : ∀ j : Fin k,
        MeasurableSet (Prod.fst ⁻¹' A ∩ {p : ℝ × Option (Fin k) | p.2 = some j}) := fun j =>
      hAm.inter (measurable_snd (measurableSet_mark {some j}))
    have hunion : ⋃ j ∈ (Finset.univ : Finset (Fin k)),
        (Prod.fst ⁻¹' A ∩ {p : ℝ × Option (Fin k) | p.2 = some j})
        = Prod.fst ⁻¹' A ∩ {p : ℝ × Option (Fin k) | p.2 ≠ none} := by
      ext p
      simp only [mem_iUnion, Finset.mem_univ, iUnion_true, mem_inter_iff, mem_setOf_eq,
        Set.mem_preimage]
      exact ⟨fun ⟨j, h1, h2⟩ => ⟨h1, by simp [h2]⟩,
        fun ⟨h1, h2⟩ => by obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 h2; exact ⟨j, h1, hj⟩⟩
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k)) : Set (Fin k))
        fun j => Prod.fst ⁻¹' A ∩ {p : ℝ × Option (Fin k) | p.2 = some j} := by
      intro i _ j _ hij
      refine Set.disjoint_left.2 fun p hp hq => hij ?_
      have : (some i : Option (Fin k)) = some j := hp.2 ▸ hq.2
      exact Option.some_injective _ this
    rw [Measure.finset_sum_apply, allCauseSubLaw, Measure.map_apply measurable_fst hA,
      Measure.restrict_apply hAm, ← hunion, measure_biUnion_finset hdisj fun j _ => hSm j]
    exact Finset.sum_congr rfl fun j _ => by
      rw [causeSubLaw, Measure.map_apply measurable_fst hA, Measure.restrict_apply hAm]
  -- `withDensity` is additive in the base measure; the density is the same for every cause.
  have hwd : ∀ (s : Finset (Fin k)) (f : ℝ → ℝ≥0∞),
      (∑ j ∈ s, causeSubLaw P j).withDensity f = ∑ j ∈ s, (causeSubLaw P j).withDensity f := by
    intro s f
    induction s using Finset.induction with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, withDensity_add_measure, ih]
  rw [allCauseCumHazard, ← hsub, hwd]
  rfl

/-- **S6.2, the exact CIF identity** `F_j(dt) = S(t^-) Λ_j(dt)` in measure form
(ABGK §IV.4): recovering the sub-distribution from its cause-specific hazard. -/
theorem causeSubLaw_eq_withDensity (P : Measure (ℝ × Option (Fin k))) [IsFiniteMeasure P]
    (j : Fin k) :
    causeSubLaw P j
      = (causeSpecificCumHazard P j).withDensity fun t => observedTimeLawCR P (Ici t) := by
  have hm : Measurable fun t : ℝ => observedTimeLawCR P (Ici t) :=
    Antitone.measurable fun _ _ hab => measure_mono (Ici_subset_Ici.2 hab)
  haveI : IsFiniteMeasure (observedTimeLawCR P) :=
    Measure.isFiniteMeasure_map P Prod.fst
  -- The at-risk denominator is `causeSubLaw`-a.e. nonzero (hygiene lemma via domination).
  have hnull : causeSubLaw P j {t : ℝ | observedTimeLawCR P (Ici t) = 0} = 0 :=
    le_antisymm ((causeSubLaw_le P j (hm (measurableSet_singleton 0))).trans_eq
      (measure_survivalLeft_zero _)) (zero_le)
  have hae : ∀ᵐ t ∂causeSubLaw P j, observedTimeLawCR P (Ici t) ≠ 0 := by
    rw [ae_iff]
    simpa using hnull
  -- Merge the two `withDensity` layers; the merged density is a.e. `1`.
  rw [causeSpecificCumHazard, ← withDensity_mul _ hm.fun_inv hm]
  refine (Eq.trans (withDensity_congr_ae ?_) withDensity_one).symm
  filter_upwards [hae] with t ht
  simpa using ENNReal.inv_mul_cancel ht (measure_ne_top _ _)

/-- Two independent latent cause times observed as (first failure, cause); ties to cause 0
(*Book vs Lean* note in module docstring). -/
noncomputable def crObserve₂ : ℝ × ℝ → ℝ × Option (Fin 2) :=
  fun p => (min p.1 p.2, if p.1 ≤ p.2 then some 0 else some 1)

/-- The two-cause independent competing-risks law. -/
noncomputable def crLaw₂ (μ₁ μ₂ : Measure ℝ) : Measure (ℝ × Option (Fin 2)) :=
  (μ₁.prod μ₂).map crObserve₂

/-- LEAN-ONLY: the two-cause observation map is measurable. -/
private theorem measurable_crObserve₂ : Measurable crObserve₂ :=
  (measurable_fst.min measurable_snd).prodMk
    (Measurable.ite (measurableSet_le measurable_fst measurable_snd) measurable_const
      measurable_const)

/-- LEAN-ONLY: collapsing the mark to `κ = 0` turns the two-cause observation into the
right-censoring observation — ties go to cause `0` on the left and to `Δ = 1` on the right,
so the two tie conventions agree. -/
private theorem markObs_comp_crObserve₂ :
    markObs (fun x : Option (Fin 2) => decide (x = some 0)) ∘ crObserve₂ = censorObserve := by
  funext p
  by_cases h : p.1 ≤ p.2 <;> simp [markObs, crObserve₂, censorObserve, h]

/-- LEAN-ONLY: the collapsed two-cause law is the random-censorship law. -/
private theorem map_crLaw₂ (μ₁ μ₂ : Measure ℝ) :
    (crLaw₂ μ₁ μ₂).map (markObs fun x : Option (Fin 2) => decide (x = some 0))
      = censoredLaw μ₁ μ₂ := by
  rw [crLaw₂, Measure.map_map (measurable_markObs _) measurable_crObserve₂,
    markObs_comp_crObserve₂, censoredLaw]

/-- **S6.3, crude = net for independent competing risks** (`Tsiatis75` positively resolved
on the identifiable region; the S2.3 mirror): the crude cause-0 hazard is the net hazard of
`T₁` where `T₂` survives. -/
theorem causeSpecificCumHazard_crLaw₂ (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] :
    causeSpecificCumHazard (crLaw₂ μ₁ μ₂) 0
      = (cumHazard μ₁).restrict {t | 0 < μ₂ (Ici t)} := by
  have hg : ∀ x : Option (Fin 2), decide (x = some 0) = true ↔ x = some 0 := by
    intro x; simp
  rw [causeSpecificCumHazard, causeSubLaw_markObs _ 0 _ hg,
    observedTimeLawCR_markObs _ (fun x : Option (Fin 2) => decide (x = some 0)),
    map_crLaw₂]
  exact crudeCumHazard_censoredLaw μ₁ μ₂

/-- **S6.4, Gray vs cause-specific** (`Gray88`): the subdistribution at-risk mass dominates
the all-cause at-risk mass, so the Gray hazard is dominated by the cause-specific hazard. -/
theorem graySubCumHazard_le (P : Measure (ℝ × Option (Fin k))) [IsProbabilityMeasure P]
    -- LEAN-ONLY: measurability of the event; standard regularity
    (j : Fin k) {A : Set ℝ} (hA : MeasurableSet A) :
    graySubCumHazard P j A ≤ causeSpecificCumHazard P j A := by
  haveI : IsFiniteMeasure (observedTimeLawCR P) := Measure.isFiniteMeasure_map P Prod.fst
  have huniv : observedTimeLawCR P univ = P univ := by
    rw [observedTimeLawCR, Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
  rw [graySubCumHazard, causeSpecificCumHazard, withDensity_apply _ hA, withDensity_apply _ hA]
  refine lintegral_mono fun t => ENNReal.inv_le_inv.2 ?_
  -- The subdistribution at-risk mass dominates the all-cause at-risk mass.
  have h1 : causeSubLaw P j (Iio t) ≤ observedTimeLawCR P (Iio t) :=
    causeSubLaw_le P j measurableSet_Iio
  have h2 : observedTimeLawCR P (Iio t) + observedTimeLawCR P (Ici t) = P univ := by
    rw [← huniv, ← compl_Iio (a := t)]
    exact measure_add_measure_compl measurableSet_Iio
  have h3 : observedTimeLawCR P (Ici t) = P univ - observedTimeLawCR P (Iio t) :=
    ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) (by rw [add_comm]; exact h2)
  exact h3.trans_le (tsub_le_tsub_left h1 _)

end StatLean.StatisticalModels.Survival
