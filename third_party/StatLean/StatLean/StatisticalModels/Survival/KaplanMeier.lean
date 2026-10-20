module
public import StatLean.StatisticalModels.Survival.CumulativeHazard

@[expose] public section

/-!
# Kaplan–Meier and Nelson–Aalen — the finite-sample product-limit layer

The nonparametric estimators on right-censored data `d : Fin n → ℝ × Bool` (observed time,
event indicator):

* `atRisk d t` — the size of the risk set `#{i : t ≤ T̃ᵢ}`;
* `eventCount d t` / `eventTimes d` — event multiplicities and the (finite) set of event
  times;
* `naJump d s = ΔN(s)/Y(s)` — the Nelson–Aalen increment;
* `nelsonAalen d t = ∑_{s ≤ t} ΔN(s)/Y(s)` — the Nelson–Aalen estimator (Nelson 1969;
  Aalen 1978);
* `kaplanMeier d t = ∏_{s ≤ t} (1 − ΔN(s)/Y(s))` — the Kaplan–Meier product-limit
  estimator, **defined** as the product of one-minus-NA-jumps, so the classical relation
  `KM = ∏(1 − ΔNA)` is structural; the content lemma `nelsonAalen_eq_partial_add_jump`
  identifies `naJump` as the genuine jump of `nelsonAalen`;
* `kaplanMeierSF` / `kaplanMeierMeasure` — Kaplan–Meier as a bona fide (sub-probability)
  law via a Stieltjes function — the classic defect: mass is lost iff the largest
  observation is censored.

Exact finite-sample results only (consistency/Greenwood are designated future milestones):
range, monotonicity, piecewise constancy, the no-censoring reduction to the empirical
survival function, and the self-consistency identity `ΔΛ_{KM}(s) = ΔN(s)/Y(s)`.

**Reference.** E. L. Kaplan and P. Meier, "Nonparametric estimation from incomplete
observations," *J. Amer. Statist. Assoc.* **53** (1958), 457–481, §1–2 (`KM58`); W. Nelson,
"Hazard plotting for incomplete failure data," *J. Qual. Tech.* **1** (1969), 27–52
(`Nelson69`); O. O. Aalen, "Nonparametric inference for a family of counting processes,"
*Ann. Statist.* **6** (1978), 701–726 (`Aalen78`); ABGK §IV.1 (Nelson–Aalen) and §IV.3
(Kaplan–Meier) (verify §).

**Proof formalization notes.** Everything is `Finset` combinatorics over the finitely many
event times; no measure theory except the Stieltjes packaging. The no-censoring reduction is
the one genuinely fiddly telescoping induction (sorted event times; `Y(s_{k+1}) = Y(s_k) −
ΔN(s_k)` holds exactly because nothing is censored between events). Degenerate-input
conventions: `naJump` junk-values by real division (`0/0 = 0`); the empty dataset is excluded
only where it genuinely breaks a statement (`hn : n ≠ 0`, LEAN-ONLY).

**Bibliographic comments.** The product-limit idea is KM58's; the hazard-increment view and
the KM–NA jump relation are Nelson69/Aalen78, unified by the counting-process synthesis of
ABGK.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace StatLean.StatisticalModels.Survival

variable {n : ℕ}

/-- The **risk-set size** `Y(t) = #{i : t ≤ T̃ᵢ}` (ABGK §IV.1). -/
noncomputable def atRisk (d : Fin n → ℝ × Bool) (t : ℝ) : ℕ :=
  (univ.filter fun i => t ≤ (d i).1).card

/-- The **event multiplicity** `ΔN(t) = #{i : T̃ᵢ = t, Δᵢ = 1}`. -/
noncomputable def eventCount (d : Fin n → ℝ × Bool) (t : ℝ) : ℕ :=
  (univ.filter fun i => (d i).1 = t ∧ (d i).2 = true).card

/-- The (finite) set of observed **event times**. -/
noncomputable def eventTimes (d : Fin n → ℝ × Bool) : Finset ℝ :=
  (univ.filter fun i => (d i).2 = true).image fun i => (d i).1

/-- The **Nelson–Aalen increment** `ΔN(s)/Y(s)` (junk `0/0 = 0` off the event times). -/
noncomputable def naJump (d : Fin n → ℝ × Bool) (s : ℝ) : ℝ :=
  (eventCount d s : ℝ) / (atRisk d s : ℝ)

/-- The **Nelson–Aalen estimator** `Λ̂(t) = ∑_{s ≤ t} ΔN(s)/Y(s)` (`Nelson69`; `Aalen78`;
ABGK §IV.1). -/
noncomputable def nelsonAalen (d : Fin n → ℝ × Bool) (t : ℝ) : ℝ :=
  ∑ s ∈ (eventTimes d).filter (· ≤ t), naJump d s

/-- The **Kaplan–Meier product-limit estimator** `Ŝ(t) = ∏_{s ≤ t} (1 − ΔN(s)/Y(s))`
(`KM58`), defined as the product of one-minus-Nelson–Aalen-jumps — the classical relation
`KM = ∏(1 − ΔNA)` is thereby structural. -/
noncomputable def kaplanMeier (d : Fin n → ℝ × Bool) (t : ℝ) : ℝ :=
  ∏ s ∈ (eventTimes d).filter (· ≤ t), (1 - naJump d s)

/-- Risk sets shrink in time. -/
theorem atRisk_antitone (d : Fin n → ℝ × Bool) : Antitone fun t => atRisk d t := by
  intro a b hab
  refine Finset.card_le_card fun i hi => ?_
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hab.trans hi

/-- Events at `s` are at risk at `s`. -/
theorem eventCount_le_atRisk (d : Fin n → ℝ × Bool) (s : ℝ) :
    eventCount d s ≤ atRisk d s := by
  refine Finset.card_le_card fun i hi => ?_
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hi.1.ge

/-- Membership in `eventTimes` unpacks to an observation which is an event at that time. -/
private lemma exists_of_mem_eventTimes {d : Fin n → ℝ × Bool} {s : ℝ}
    (hs : s ∈ eventTimes d) : ∃ i, (d i).1 = s ∧ (d i).2 = true := by
  rw [eventTimes, Finset.mem_image] at hs
  obtain ⟨i, hi, hval⟩ := hs
  exact ⟨i, hval, (Finset.mem_filter.1 hi).2⟩

/-- At an event time the risk set is nonempty. -/
theorem atRisk_pos_of_mem_eventTimes {d : Fin n → ℝ × Bool} {s : ℝ}
    -- LEAN-ONLY: statement scoping (s is an observed event time); no scope change
    (hs : s ∈ eventTimes d) : 0 < atRisk d s := by
  obtain ⟨i, hval, -⟩ := exists_of_mem_eventTimes hs
  exact Finset.card_pos.2 ⟨i, by simp [hval]⟩

/-- At an event time there is at least one event. -/
theorem eventCount_pos_of_mem_eventTimes {d : Fin n → ℝ × Bool} {s : ℝ}
    -- LEAN-ONLY: statement scoping (s is an observed event time); no scope change
    (hs : s ∈ eventTimes d) : 0 < eventCount d s := by
  obtain ⟨i, hval, hdel⟩ := exists_of_mem_eventTimes hs
  exact Finset.card_pos.2 ⟨i, by simp [hval, hdel]⟩

/-- The Nelson–Aalen increment lies in `[0, 1]`. -/
theorem naJump_mem_Icc (d : Fin n → ℝ × Bool) (s : ℝ) : naJump d s ∈ Set.Icc 0 1 := by
  rcases Nat.eq_zero_or_pos (atRisk d s) with h0 | hpos
  · simp [naJump, h0]
  · refine Set.mem_Icc.2 ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
    rw [naJump, div_le_one (by exact_mod_cast hpos : (0 : ℝ) < (atRisk d s : ℝ))]
    exact_mod_cast eventCount_le_atRisk d s

/-- The Kaplan–Meier factors lie in `[0, 1]`. -/
private lemma one_sub_naJump_mem_Icc (d : Fin n → ℝ × Bool) (s : ℝ) :
    0 ≤ 1 - naJump d s ∧ 1 - naJump d s ≤ 1 := by
  obtain ⟨h0, h1⟩ := Set.mem_Icc.1 (naJump_mem_Icc d s)
  constructor <;> linarith

/-- Any product of Kaplan–Meier factors lies in `[0, 1]`. -/
private lemma prod_one_sub_naJump_mem_Icc (d : Fin n → ℝ × Bool) (F : Finset ℝ) :
    0 ≤ ∏ s ∈ F, (1 - naJump d s) ∧ ∏ s ∈ F, (1 - naJump d s) ≤ 1 :=
  ⟨Finset.prod_nonneg fun s _ => (one_sub_naJump_mem_Icc d s).1,
    Finset.prod_le_one (fun s _ => (one_sub_naJump_mem_Icc d s).1)
      fun s _ => (one_sub_naJump_mem_Icc d s).2⟩

/-- At an event time the truncated set of event times splits off its top point. -/
private lemma filter_le_eq_insert {d : Fin n → ℝ × Bool} {s : ℝ} (hs : s ∈ eventTimes d) :
    (eventTimes d).filter (· ≤ s) = insert s ((eventTimes d).filter (· < s)) := by
  ext u
  simp only [Finset.mem_insert, Finset.mem_filter]
  constructor
  · rintro ⟨hu, hle⟩
    rcases lt_or_eq_of_le hle with h | h
    · exact Or.inr ⟨hu, h⟩
    · exact Or.inl h
  · rintro (rfl | ⟨hu, hlt⟩)
    · exact ⟨hs, le_rfl⟩
    · exact ⟨hu, hlt.le⟩

/-- **`naJump` is the genuine jump of `nelsonAalen`** at an event time: the estimator at `s`
is its strict-past partial sum plus the increment (the content behind `KM = ∏(1 − ΔNA)`;
ABGK §IV.1 vs §IV.3). -/
theorem nelsonAalen_eq_partial_add_jump {d : Fin n → ℝ × Bool} {s : ℝ}
    -- LEAN-ONLY: statement scoping (s is an observed event time); no scope change
    (hs : s ∈ eventTimes d) :
    nelsonAalen d s = (∑ u ∈ (eventTimes d).filter (· < s), naJump d u) + naJump d s := by
  rw [nelsonAalen, filter_le_eq_insert hs,
    Finset.sum_insert (by simp), add_comm]

/-- Kaplan–Meier takes values in `[0, 1]` (`KM58`). -/
theorem kaplanMeier_mem_Icc (d : Fin n → ℝ × Bool) (t : ℝ) :
    kaplanMeier d t ∈ Set.Icc 0 1 :=
  Set.mem_Icc.2 (prod_one_sub_naJump_mem_Icc d _)

/-- Kaplan–Meier is antitone (`KM58`). -/
theorem antitone_kaplanMeier (d : Fin n → ℝ × Bool) : Antitone (kaplanMeier d) := by
  intro a b hab
  have hsub : (eventTimes d).filter (· ≤ a) ⊆ (eventTimes d).filter (· ≤ b) := by
    intro u hu
    simp only [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, hu.2.trans hab⟩
  have h := Finset.prod_sdiff (f := fun s => 1 - naJump d s) hsub
  simp only [kaplanMeier]
  rw [← h]
  exact mul_le_of_le_one_left (prod_one_sub_naJump_mem_Icc d _).1
    (prod_one_sub_naJump_mem_Icc d _).2

/-- Kaplan–Meier only sees the event times through the truncation `{s ∈ eventTimes | s ≤ ·}`. -/
private lemma kaplanMeier_eq_prod_of_filter_eq {d : Fin n → ℝ × Bool} {u : ℝ} {F : Finset ℝ}
    (h : (eventTimes d).filter (· ≤ u) = F) :
    kaplanMeier d u = ∏ s ∈ F, (1 - naJump d s) := by
  simp only [kaplanMeier, h]

/-- Kaplan–Meier is right-locally constant (piecewise constancy between event times; whence
right-continuity without any filter bookkeeping). -/
theorem kaplanMeier_eventually_constant_right (d : Fin n → ℝ × Bool) (t : ℝ) :
    ∃ ε > 0, ∀ u ∈ Set.Ico t (t + ε), kaplanMeier d u = kaplanMeier d t := by
  have key : ∀ (ε : ℝ), 0 < ε → (∀ v ∈ eventTimes d, t < v → t + ε ≤ v) →
      ∀ u ∈ Set.Ico t (t + ε), kaplanMeier d u = kaplanMeier d t := by
    intro ε _ hgap u hu
    refine kaplanMeier_eq_prod_of_filter_eq (F := (eventTimes d).filter (· ≤ t)) ?_
    ext v
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hv
    refine ⟨fun hvu => ?_, fun hvt => hvt.trans hu.1⟩
    by_contra hc
    exact absurd (hvu.trans_lt hu.2) (not_lt.2 (hgap v hv (not_le.1 hc)))
  rcases ((eventTimes d).filter (t < ·)).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, key 1 one_pos fun v hv hvt => ?_⟩
    exact absurd (Finset.mem_filter.2 ⟨hv, hvt⟩) (by simp [hemp])
  · have hmem := Finset.min'_mem _ hne
    have hmt : t < ((eventTimes d).filter (t < ·)).min' hne := (Finset.mem_filter.1 hmem).2
    refine ⟨((eventTimes d).filter (t < ·)).min' hne - t, by linarith,
      key _ (by linarith) fun v hv hvt => ?_⟩
    have := Finset.min'_le _ v (Finset.mem_filter.2 ⟨hv, hvt⟩)
    linarith

/-- Kaplan–Meier as a Stieltjes function: `t ↦ 1 − Ŝ(t)` (monotone by
`antitone_kaplanMeier`, right-continuous by piecewise constancy). -/
noncomputable def kaplanMeierSF (d : Fin n → ℝ × Bool) : StieltjesFunction ℝ where
  toFun t := 1 - kaplanMeier d t
  mono' a b hab := by have := antitone_kaplanMeier d hab; linarith
  right_continuous' t := by
    obtain ⟨ε, hε, hcon⟩ := kaplanMeier_eventually_constant_right d t
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ico_mem_nhdsGE (show t < t + ε by linarith)] with u hu
    rw [hcon u hu]

@[simp]
theorem kaplanMeierSF_apply (d : Fin n → ℝ × Bool) (t : ℝ) :
    kaplanMeierSF d t = 1 - kaplanMeier d t := rfl

/-- Kaplan–Meier is left-locally constant, with the strict-past product as its value. -/
private lemma kaplanMeier_eventually_constant_left (d : Fin n → ℝ × Bool) (t : ℝ) :
    ∃ ε > 0, ∀ u ∈ Set.Ioo (t - ε) t,
      kaplanMeier d u = ∏ s ∈ (eventTimes d).filter (· < t), (1 - naJump d s) := by
  have key : ∀ ε : ℝ, 0 < ε → (∀ v ∈ eventTimes d, v < t → v ≤ t - ε) →
      ∀ u ∈ Set.Ioo (t - ε) t,
        kaplanMeier d u = ∏ s ∈ (eventTimes d).filter (· < t), (1 - naJump d s) := by
    intro ε _ hgap u hu
    refine kaplanMeier_eq_prod_of_filter_eq ?_
    ext v
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hv
    exact ⟨fun hvu => hvu.trans_lt hu.2, fun hvt => (hgap v hv hvt).trans hu.1.le⟩
  rcases ((eventTimes d).filter (· < t)).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, key 1 one_pos fun v hv hvt => ?_⟩
    exact absurd (Finset.mem_filter.2 ⟨hv, hvt⟩ :
      v ∈ (eventTimes d).filter (· < t)) (by simp [hemp])
  · have hmem := Finset.max'_mem _ hne
    have hMt : ((eventTimes d).filter (· < t)).max' hne < t := (Finset.mem_filter.1 hmem).2
    refine ⟨t - ((eventTimes d).filter (· < t)).max' hne, by linarith,
      key _ (by linarith) fun v hv hvt => ?_⟩
    have := Finset.le_max' _ v (Finset.mem_filter.2 ⟨hv, hvt⟩ :
      v ∈ (eventTimes d).filter (· < t))
    linarith

/-- The left limit of the Kaplan–Meier Stieltjes function is `1 − Ŝ(t−)`. -/
private lemma leftLim_kaplanMeierSF (d : Fin n → ℝ × Bool) (t : ℝ) :
    Function.leftLim (kaplanMeierSF d) t
      = 1 - ∏ s ∈ (eventTimes d).filter (· < t), (1 - naJump d s) := by
  obtain ⟨ε, hε, hcon⟩ := kaplanMeier_eventually_constant_left d t
  refine leftLim_eq_of_tendsto (h := nhdsLT_neBot t) ?_
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsLT (show t - ε < t by linarith)] with u hu
  rw [kaplanMeierSF_apply, hcon u hu]

/-- Below every event time Kaplan–Meier is still one. -/
private lemma kaplanMeier_eq_one_of_lt {d : Fin n → ℝ × Bool} {t : ℝ}
    (h : ∀ s ∈ eventTimes d, t < s) : kaplanMeier d t = 1 := by
  rw [kaplanMeier_eq_prod_of_filter_eq (F := ∅) ?_, Finset.prod_empty]
  exact Finset.filter_eq_empty_iff.2 fun v hv => not_le.2 (h v hv)

/-- The full product of Kaplan–Meier factors — the terminal value `Ŝ(∞)`; the Kaplan–Meier
law is defective (carries cure mass) exactly when this is positive, which happens exactly
when the largest observation is censored (`KM58 §1`). -/
noncomputable def kmLimit (d : Fin n → ℝ × Bool) : ℝ :=
  ∏ s ∈ eventTimes d, (1 - naJump d s)

private lemma tendsto_kaplanMeierSF_atBot (d : Fin n → ℝ × Bool) :
    Filter.Tendsto (kaplanMeierSF d) Filter.atBot (nhds 0) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∀ s ∈ eventTimes d, a < s := by
    rcases (eventTimes d).eq_empty_or_nonempty with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨(eventTimes d).min' h - 1, fun s hs => by
        have := (eventTimes d).min'_le s hs; linarith⟩
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_le_atBot a] with t ht
  rw [kaplanMeierSF_apply, kaplanMeier_eq_one_of_lt fun s hs => lt_of_le_of_lt ht (ha s hs),
    sub_self]

private lemma tendsto_kaplanMeierSF_atTop (d : Fin n → ℝ × Bool) :
    Filter.Tendsto (kaplanMeierSF d) Filter.atTop (nhds (1 - kmLimit d)) := by
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ s ∈ eventTimes d, s ≤ b := by
    rcases (eventTimes d).eq_empty_or_nonempty with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨(eventTimes d).max' h, fun s hs => (eventTimes d).le_max' s hs⟩
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop b] with t ht
  rw [kaplanMeierSF_apply,
    kaplanMeier_eq_prod_of_filter_eq (F := eventTimes d)
      (Finset.filter_true_of_mem fun v hv => (hb v hv).trans ht)]
  rfl

/-- **Kaplan–Meier as a law**: the Stieltjes measure of `1 − Ŝ` (`KM58` — the product-limit
estimate *is* a distribution, possibly defective). -/
noncomputable def kaplanMeierMeasure (d : Fin n → ℝ × Bool) : Measure ℝ :=
  (kaplanMeierSF d).measure

/-- The Kaplan–Meier law is a sub-event-time law on nonnegative data — total mass at most
one (the classic defect: mass is lost exactly when the largest observation is censored). -/
theorem isSubEventTimeLaw_kaplanMeierMeasure (d : Fin n → ℝ × Bool)
    -- USER-INPUT: observation times are nonnegative; KM58 §1
    (hd : ∀ i, 0 ≤ (d i).1) :
    IsSubEventTimeLaw (kaplanMeierMeasure d) := by
  have hEvent : ∀ s ∈ eventTimes d, 0 ≤ s := by
    intro s hs
    obtain ⟨i, hval, -⟩ := exists_of_mem_eventTimes hs
    exact hval ▸ hd i
  constructor
  · rw [kaplanMeierMeasure,
      StieltjesFunction.measure_univ _ (tendsto_kaplanMeierSF_atBot d)
        (tendsto_kaplanMeierSF_atTop d)]
    refine ENNReal.ofReal_le_one.2 ?_
    have hlim : (0 : ℝ) ≤ kmLimit d := (prod_one_sub_naJump_mem_Icc d (eventTimes d)).1
    linarith
  · rw [kaplanMeierMeasure,
      StieltjesFunction.measure_Iio _ (tendsto_kaplanMeierSF_atBot d) 0,
      leftLim_kaplanMeierSF d 0]
    rw [Finset.filter_eq_empty_iff.2 fun v hv => not_lt.2 (hEvent v hv)]
    simp

/-- Under no censoring the risk set at `s` splits into the events at `s` and the strict
future of `s`. -/
private lemma atRisk_eq_add_of_no_censoring {d : Fin n → ℝ × Bool}
    (hall : ∀ i, (d i).2 = true) (s : ℝ) :
    atRisk d s = eventCount d s + (univ.filter fun i => s < (d i).1).card := by
  rw [atRisk, eventCount]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hall i,
      and_true]
    exact ⟨fun h => (lt_or_eq_of_le h).symm.imp Eq.symm id, fun h => h.elim (fun h => h.ge)
      le_of_lt⟩
  · refine Finset.disjoint_left.2 fun i hi hi' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    exact absurd hi.1 (ne_of_gt hi')

/-- **Telescoping** (`KM58 §1`): under no censoring, the product of Kaplan–Meier factors over
any down-closed set `F` of event times is `#{i : T̃ᵢ ∉ F}/n`. -/
private lemma prod_one_sub_naJump_of_no_censoring {d : Fin n → ℝ × Bool}
    (hall : ∀ i, (d i).2 = true) (hn : n ≠ 0) :
    ∀ (k : ℕ) (F : Finset ℝ), F.card = k → F ⊆ eventTimes d →
      (∀ u ∈ eventTimes d, ∀ v ∈ F, u ≤ v → u ∈ F) →
      ∏ s ∈ F, (1 - naJump d s) = ((univ.filter fun i => (d i).1 ∉ F).card : ℝ) / n := by
  have hmemE : ∀ i, (d i).1 ∈ eventTimes d := fun i =>
    Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hall i⟩, rfl⟩
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  intro k
  induction k with
  | zero =>
    intro F hcard _ _
    rw [Finset.card_eq_zero] at hcard
    subst hcard
    rw [Finset.prod_empty, Finset.filter_true_of_mem (fun i _ => Finset.notMem_empty _),
      Finset.card_univ, Fintype.card_fin]
    field_simp
  | succ k ih =>
    intro F hcard hsub hdc
    have hne : F.Nonempty := Finset.card_pos.1 (by omega)
    set s := F.max' hne with hs
    have hsF : s ∈ F := F.max'_mem hne
    have hsE : s ∈ eventTimes d := hsub hsF
    -- the erased set is again down-closed, with one element fewer
    have hcard' : (F.erase s).card = k := by
      rw [Finset.card_erase_of_mem hsF, hcard]; rfl
    have hsub' : F.erase s ⊆ eventTimes d := (Finset.erase_subset _ _).trans hsub
    have hdc' : ∀ u ∈ eventTimes d, ∀ v ∈ F.erase s, u ≤ v → u ∈ F.erase s := by
      intro u hu v hv huv
      have hvF : v ∈ F := Finset.mem_of_mem_erase hv
      have hvs : v < s := lt_of_le_of_ne (F.le_max' v hvF) (Finset.ne_of_mem_erase hv)
      exact Finset.mem_erase.2 ⟨ne_of_lt (huv.trans_lt hvs), hdc u hu v hvF huv⟩
    -- membership in `F` / `F.erase s` is the position relative to `s`
    have hnotF : ∀ i, ((d i).1 ∉ F ↔ s < (d i).1) := by
      intro i
      constructor
      · intro h
        by_contra hc
        exact h (hdc _ (hmemE i) s hsF (not_lt.1 hc))
      · intro h hmem
        exact absurd (F.le_max' _ hmem) (not_le.2 h)
    have hnotF' : ∀ i, ((d i).1 ∉ F.erase s ↔ s ≤ (d i).1) := by
      intro i
      rw [Finset.mem_erase, not_and_or, not_not]
      constructor
      · rintro (h | h)
        · exact h.ge
        · exact ((hnotF i).1 h).le
      · intro h
        rcases eq_or_lt_of_le h with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr ((hnotF i).2 h')
    -- the two counts, in terms of the risk set and the event multiplicity at `s`
    have hcount' : (univ.filter fun i => (d i).1 ∉ F.erase s).card = atRisk d s := by
      rw [atRisk]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hnotF' i
    have hcount : (univ.filter fun i => (d i).1 ∉ F).card
        = atRisk d s - eventCount d s := by
      have hrw : (univ.filter fun i => (d i).1 ∉ F).card
          = (univ.filter fun i => s < (d i).1).card := by
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hnotF i
      rw [hrw, atRisk_eq_add_of_no_censoring hall s]
      omega
    -- telescope
    have hY : (0 : ℝ) < (atRisk d s : ℝ) := by
      exact_mod_cast atRisk_pos_of_mem_eventTimes hsE
    have hNY : eventCount d s ≤ atRisk d s := eventCount_le_atRisk d s
    rw [← Finset.prod_erase_mul F _ hsF, ih _ hcard' hsub' hdc', hcount, hcount',
      naJump, Nat.cast_sub hNY]
    field_simp

/-- **No-censoring reduction** (`KM58 §1`): with every observation an event, Kaplan–Meier is
the empirical survival function `#{i : t < T̃ᵢ}/n`. -/
theorem kaplanMeier_of_no_censoring {d : Fin n → ℝ × Bool}
    -- USER-INPUT: no censoring; KM58 §1
    (hall : ∀ i, (d i).2 = true)
    -- LEAN-ONLY: nonempty dataset (0/0 junk breaks the n = 0 corner)
    (hn : n ≠ 0) (t : ℝ) :
    kaplanMeier d t = ((univ.filter fun i => t < (d i).1).card : ℝ) / n := by
  have hmemE : ∀ i, (d i).1 ∈ eventTimes d := fun i =>
    Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hall i⟩, rfl⟩
  have hkey := prod_one_sub_naJump_of_no_censoring hall hn
    ((eventTimes d).filter (· ≤ t)).card ((eventTimes d).filter (· ≤ t)) rfl
    (Finset.filter_subset _ _)
    (fun u hu v hv huv => Finset.mem_filter.2 ⟨hu, huv.trans (Finset.mem_filter.1 hv).2⟩)
  have hcard : (univ.filter fun i => (d i).1 ∉ (eventTimes d).filter (· ≤ t)).card
      = (univ.filter fun i => t < (d i).1).card := by
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le]
    exact ⟨fun h => h (hmemE i), fun h _ => h⟩
  rw [kaplanMeier, hkey, hcard]

/-- The atom of the Kaplan–Meier law: `μ{s} = Ŝ(s−) − Ŝ(s)`. -/
private lemma kaplanMeierMeasure_singleton (d : Fin n → ℝ × Bool) (s : ℝ) :
    kaplanMeierMeasure d {s}
      = ENNReal.ofReal ((∏ u ∈ (eventTimes d).filter (· < s), (1 - naJump d u))
          - kaplanMeier d s) := by
  rw [kaplanMeierMeasure, StieltjesFunction.measure_singleton, leftLim_kaplanMeierSF,
    kaplanMeierSF_apply]
  congr 1
  ring

/-- The upper tail of the Kaplan–Meier law: `μ[s, ∞) = Ŝ(s−) − Ŝ(∞)` — note the **defect**
`Ŝ(∞) = kmLimit d`, which is `0` exactly when the largest observation is an event. -/
private lemma kaplanMeierMeasure_Ici (d : Fin n → ℝ × Bool) (s : ℝ) :
    kaplanMeierMeasure d (Set.Ici s)
      = ENNReal.ofReal ((∏ u ∈ (eventTimes d).filter (· < s), (1 - naJump d u))
          - kmLimit d) := by
  rw [kaplanMeierMeasure, StieltjesFunction.measure_Ici _ (tendsto_kaplanMeierSF_atTop d),
    leftLim_kaplanMeierSF]
  congr 1
  ring

/-- Kaplan–Meier peels its top factor at an event time. -/
private lemma kaplanMeier_eq_prod_lt_mul {d : Fin n → ℝ × Bool} {s : ℝ}
    (hs : s ∈ eventTimes d) :
    kaplanMeier d s
      = (∏ u ∈ (eventTimes d).filter (· < s), (1 - naJump d u)) * (1 - naJump d s) := by
  rw [kaplanMeier, filter_le_eq_insert hs, Finset.prod_insert (by simp), mul_comm]

/-- **Self-consistency, repaired** (ABGK §IV.3 (verify §)): the hazard jump of the
Kaplan–Meier law at an event time inside its support is the Nelson–Aalen increment — provided
the law is **not defective** (`kmLimit d = 0`, i.e. the largest observation is an event).
Without that hypothesis the identity is false: see `cex_cumHazardJump_ne` below. -/
private lemma cumHazardJump_kaplanMeierMeasure_of_kmLimit_zero {d : Fin n → ℝ × Bool} {s : ℝ}
    (hs : s ∈ eventTimes d)
    (hpos : 0 < ∏ u ∈ (eventTimes d).filter (· < s), (1 - naJump d u))
    (hdefect : kmLimit d = 0) :
    cumHazardJump (kaplanMeierMeasure d) s = ENNReal.ofReal (naJump d s) := by
  set P := ∏ u ∈ (eventTimes d).filter (· < s), (1 - naJump d u) with hP
  have hIci : kaplanMeierMeasure d (Set.Ici s) = ENNReal.ofReal P := by
    rw [kaplanMeierMeasure_Ici, hdefect, sub_zero]
  have hpt : kaplanMeierMeasure d {s} = ENNReal.ofReal (P * naJump d s) := by
    rw [kaplanMeierMeasure_singleton, kaplanMeier_eq_prod_lt_mul hs]
    congr 1
    ring
  have hPne : ENNReal.ofReal P ≠ 0 := by
    simpa using hpos
  rw [cumHazardJump_eq _ (hIci ▸ hPne), hpt, hIci, ← ENNReal.ofReal_div_of_pos hpos]
  congr 1
  field_simp

/-- **Self-consistency** (ABGK §IV.3 (verify §)): the hazard jump of the Kaplan–Meier law at
an event time inside its support is the Nelson–Aalen increment — the estimator solves the
model's own hazard identity. -/
theorem cumHazardJump_kaplanMeierMeasure {d : Fin n → ℝ × Bool} {s : ℝ}
    -- LEAN-ONLY: statement scoping (s is an observed event time); no scope change
    (hs : s ∈ eventTimes d)
    -- USER-INPUT: the left limit of KM at s is positive (inside the support); ABGK §IV.3
    (hpos : 0 < ∏ u ∈ (eventTimes d).filter (· < s), (1 - naJump d u))
    -- USER-INPUT: non-defective Kaplan–Meier (largest observation an event — no cure mass;
    -- required: the defective case is FALSE, machine-checked in `cex_cumHazardJump_ne`);
    -- KM58 §1, ABGK §IV.3
    (hdefect : kmLimit d = 0) :
    cumHazardJump (kaplanMeierMeasure d) s = ENNReal.ofReal (naJump d s) :=
  cumHazardJump_kaplanMeierMeasure_of_kmLimit_zero hs hpos hdefect

/-! ### A counterexample to `cumHazardJump_kaplanMeierMeasure` as frozen

The dataset `T̃ = (1, 2)`, `Δ = (1, 0)` — one event at `1`, one observation censored at `2`.
Here `Y(1) = 2`, `ΔN(1) = 1`, so `ΔN(1)/Y(1) = 1/2`, and `Ŝ(1−) = 1 > 0` (so the frozen
hypothesis `hpos` holds), while `Ŝ(∞) = 1/2`: the Kaplan–Meier law is **defective**, with
total mass `1/2`, all of it the atom at `1`. Hence `μ{1} = μ[1, ∞) = 1/2` and
`ΔΛ(1) = μ{1}/μ[1,∞) = 1 ≠ 1/2 = ΔN(1)/Y(1)`.

The frozen statement is therefore true only when `kmLimit d = 0`, i.e. when the largest
observation is an event; the slice's `cumHazard` divides by `μ[s, ∞)`, which under a defect
is **strictly smaller** than the survival value `Ŝ(s−)` that the classical identity uses. -/

private noncomputable def cexData : Fin 2 → ℝ × Bool := ![(1, true), (2, false)]

private lemma cex_eventTimes : eventTimes cexData = {1} := by
  ext x
  simp only [eventTimes, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    fin_cases i <;> simp_all [cexData]
  · rintro rfl
    exact ⟨0, by simp [cexData], by simp [cexData]⟩

private lemma cex_atRisk : atRisk cexData 1 = 2 := by
  rw [atRisk, Finset.filter_true_of_mem fun i _ => by fin_cases i <;> norm_num [cexData],
    Finset.card_univ, Fintype.card_fin]

private lemma cex_eventCount : eventCount cexData 1 = 1 := by
  rw [eventCount, show (univ.filter fun i => (cexData i).1 = (1 : ℝ) ∧ (cexData i).2 = true)
    = {0} from by ext i; fin_cases i <;> (rw [Finset.mem_filter]; simp [cexData])]
  rfl

private lemma cex_naJump : naJump cexData 1 = 1 / 2 := by
  rw [naJump, cex_atRisk, cex_eventCount]
  norm_num

private lemma cex_prod_lt : ∏ u ∈ (eventTimes cexData).filter (· < 1), (1 - naJump cexData u)
    = 1 := by
  rw [cex_eventTimes, Finset.filter_singleton, if_neg (lt_irrefl (1 : ℝ)), Finset.prod_empty]

private lemma cex_kaplanMeier : kaplanMeier cexData 1 = 1 / 2 := by
  rw [kaplanMeier, cex_eventTimes, Finset.filter_singleton, if_pos le_rfl,
    Finset.prod_singleton, cex_naJump]
  norm_num

private lemma cex_kmLimit : kmLimit cexData = 1 / 2 := by
  rw [kmLimit, cex_eventTimes, Finset.prod_singleton, cex_naJump]
  norm_num

/-- **The frozen `cumHazardJump_kaplanMeierMeasure` is FALSE**: on `cexData` its hypotheses
hold at `s = 1` but its conclusion fails (`1 ≠ 1/2`). -/
private theorem cex_cumHazardJump_ne :
    (1 : ℝ) ∈ eventTimes cexData ∧
      0 < ∏ u ∈ (eventTimes cexData).filter (· < (1 : ℝ)), (1 - naJump cexData u) ∧
      cumHazardJump (kaplanMeierMeasure cexData) 1
        ≠ ENNReal.ofReal (naJump cexData 1) := by
  have hIci : kaplanMeierMeasure cexData (Set.Ici 1) = ENNReal.ofReal (1 / 2) := by
    rw [kaplanMeierMeasure_Ici, cex_prod_lt, cex_kmLimit]
    norm_num
  have hpt : kaplanMeierMeasure cexData {(1 : ℝ)} = ENNReal.ofReal (1 / 2) := by
    rw [kaplanMeierMeasure_singleton, cex_prod_lt, cex_kaplanMeier]
    norm_num
  have hne : ENNReal.ofReal (1 / 2 : ℝ) ≠ 0 := by simp
  have hjump : cumHazardJump (kaplanMeierMeasure cexData) 1 = 1 := by
    rw [cumHazardJump_eq _ (hIci ▸ hne), hpt, hIci,
      ENNReal.div_self hne (by simp)]
  refine ⟨by simp [cex_eventTimes], by rw [cex_prod_lt]; norm_num, ?_⟩
  rw [hjump, cex_naJump]
  intro h
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp] at h
  have := (ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)).1 h
  norm_num at this

end StatLean.StatisticalModels.Survival
