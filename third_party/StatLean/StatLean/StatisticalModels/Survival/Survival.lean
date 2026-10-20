module
public import StatLean.StatisticalModels.Survival.Defs
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.LeftRightLim

@[expose] public section

/-!
# The survival function — monotonicity, limits, CDF bridge

Basic analytic facts about `survival`/`survivalLeft` of an event-time law: monotonicity, range,
tail behavior, behavior on the negative half-line, the bridge to Mathlib's `ProbabilityTheory.cdf`
(whence right-continuity for free from the `StieltjesFunction` API), and the reconciliation of
the *defined* left limit `survivalLeft` with the topological left limit `Function.leftLim`.

**Reference.** ABGK §II.1 (verify §): the survival function and its regularity. CDF duality:
any probability text, e.g. TPE2 §1.2 (verify §).

**Proof formalization notes.** Everything here is measure monotonicity and continuity from
above/below (`measure_mono`, `tendsto_measure_iInter_atTop`-family) plus the `cdf` API
(`ProbabilityTheory.cdf` is a `StieltjesFunction`, so monotone + right-continuous are free).
`survivalLeft_eq_leftLim` is the one genuinely topological statement; it is a *bridge lemma* —
by design nothing downstream depends on it (the definition `S(t−) := μ [t, ∞)` is what the
Survival slice consumes).

**Bibliographic comments.** The identification of `P(T ≥ t)` with the left limit of
`P(T > ·)` is classical real analysis of monotone functions (Lebesgue); we record it only to
certify that the definitional choice agrees with the books' limit reading.
-/

open MeasureTheory Set Filter Topology

namespace StatLean.StatisticalModels.Survival

variable {μ : Measure ℝ}

/-- The survival function is antitone. -/
theorem antitone_survival (μ : Measure ℝ) : Antitone (survival μ) :=
  fun _ _ hab => measure_mono (Ioi_subset_Ioi hab)

/-- The left-limit survival function is antitone. -/
theorem antitone_survivalLeft (μ : Measure ℝ) : Antitone (survivalLeft μ) :=
  fun _ _ hab => measure_mono (Ici_subset_Ici.2 hab)

/-- `S(t) ≤ S(t−)`. -/
theorem survival_le_survivalLeft (μ : Measure ℝ) (t : ℝ) :
    survival μ t ≤ survivalLeft μ t :=
  measure_mono Ioi_subset_Ici_self

/-- The survival function of a probability law is bounded by one. -/
theorem survival_le_one [IsProbabilityMeasure μ] (t : ℝ) : survival μ t ≤ 1 :=
  prob_le_one

/-- `S(t−) − S(t) = μ{t}`: the survival drop at `t` is the atom mass. -/
theorem survivalLeft_sub_survival (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    survivalLeft μ t = survival μ t + μ {t} := by
  have hdisj : Disjoint (Ioi t) ({t} : Set ℝ) :=
    Set.disjoint_singleton_right.2 (lt_irrefl t)
  have : μ (Ioi t ∪ {t}) = μ (Ioi t) + μ {t} :=
    measure_union hdisj (measurableSet_singleton t)
  rw [Set.Ioi_union_left] at this
  exact this

/-- The survival function of a finite law vanishes at infinity. -/
theorem tendsto_survival_atTop (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (survival μ) atTop (𝓝 0) := by
  have hempty : (⋂ a : ℝ, Ioi a) = (∅ : Set ℝ) := by
    ext x
    simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
    exact ⟨x, le_rfl⟩
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun a : ℝ => Ioi a)
    (fun _ => measurableSet_Ioi.nullMeasurableSet) (fun _ _ hab => Ioi_subset_Ioi hab)
    ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at h
  exact h

/-- An event-time law has full survival on the negative half-line. -/
theorem survival_of_neg
    -- USER-INPUT: event-time law (probability, supported on [0, ∞)); ABGK §II.1
    -- LEAN-ONLY: statement scoping (negative time); no scope change
    (h : IsEventTimeLaw μ) {t : ℝ} (ht : t < 0) :
    survival μ t = 1 := by
  haveI := h.1
  have hIic : μ (Iic t) = 0 :=
    measure_mono_null (fun x hx => lt_of_le_of_lt hx ht) h.2
  have : μ (Iic t)ᶜ = 1 - μ (Iic t) := prob_compl_eq_one_sub measurableSet_Iic
  rw [Set.compl_Iic, hIic, tsub_zero] at this
  exact this

/-- **CDF bridge**: `S(t) = 1 − F(t)` in real form; right-continuity of `survivalReal` then
comes free from the `StieltjesFunction` API of `ProbabilityTheory.cdf`. -/
theorem survivalReal_eq_one_sub_cdf [IsProbabilityMeasure μ] (t : ℝ) :
    survivalReal μ t = 1 - ProbabilityTheory.cdf μ t := by
  have hsum : μ.real (Iic t) + μ.real (Iic t)ᶜ = 1 :=
    probReal_add_probReal_compl measurableSet_Iic
  have hcompl : survivalReal μ t = μ.real (Iic t)ᶜ := by
    rw [Set.compl_Iic]; rfl
  rw [ProbabilityTheory.cdf_eq_real, hcompl]
  linarith

/-- Bridge lemma: the *defined* left limit `S(t−) = μ [t, ∞)` agrees with the topological
left limit of the survival function. Nothing downstream depends on this — it certifies the
definitional choice against the books' limit reading. -/
theorem survivalLeft_eq_leftLim (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    survivalLeft μ t = Function.leftLim (survival μ) t := by
  have hL : Function.leftLim (survival μ) t = sInf (survival μ '' Iio t) :=
    leftLim_eq_of_tendsto (h := nhdsLT_neBot t)
      ((antitone_survival μ).tendsto_nhdsLT t)
  rw [hL]
  refine le_antisymm (le_sInf ?_) ?_
  · rintro b ⟨s, hs, rfl⟩
    exact measure_mono (Ici_subset_Ioi.2 hs)
  · have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
    have hset : (⋂ n : ℕ, Ioi (t - 1 / (n + 1))) = Ici t := by
      ext x
      simp only [mem_iInter, mem_Ioi, mem_Ici]
      refine ⟨fun hx => ?_, fun hx n => by linarith [hpos n]⟩
      by_contra hcon
      replace hcon := not_le.1 hcon
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < t - x by linarith)
      linarith [hx n]
    have hanti : Antitone fun n : ℕ => Ioi (t - 1 / ((n : ℝ) + 1)) := by
      intro a b hab
      refine Ioi_subset_Ioi ?_
      have hab' : ((a : ℝ) + 1) ≤ (b : ℝ) + 1 := by
        have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.2 hab
        linarith
      have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (a : ℝ) + 1) hab'
      linarith
    have htend : Tendsto (fun n : ℕ => μ (Ioi (t - 1 / ((n : ℝ) + 1)))) atTop
        (𝓝 (μ (Ici t))) := by
      have h := tendsto_measure_iInter_atTop (μ := μ)
        (s := fun n : ℕ => Ioi (t - 1 / ((n : ℝ) + 1)))
        (fun _ => measurableSet_Ioi.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
      rwa [hset] at h
    refine ge_of_tendsto htend (Filter.Eventually.of_forall fun n => ?_)
    exact sInf_le ⟨t - 1 / ((n : ℝ) + 1), by simpa using hpos n, rfl⟩

end StatLean.StatisticalModels.Survival
