module
public import StatLean.StatisticalModels.Survival.Survival

@[expose] public section

/-!
# The cumulative-hazard measure — hygiene and atom calculus

The load-bearing facts about `cumHazard μ = μ.withDensity (t ↦ (μ [t,∞))⁻¹)`:

* **the hygiene lemma** `measure_survivalLeft_zero` — the set where `S(t−) = 0` is `μ`-null,
  so the ENNReal inverse in the hazard density is a.e. finite and the `0⁻¹ = ∞` junk never
  carries mass (proved FIRST; every later hazard argument in the slice cites it);
* the evaluation formula `cumHazard_apply`;
* the **atom formula** `ΔΛ(t) = μ{t} / S(t−)` and its unconditional bound `ΔΛ(t) ≤ 1`;
* local finiteness of `Λ` on `{S(t−) > 0}`;
* vanishing on the negative half-line for event-time laws.

**Reference.** ABGK §II.1 (verify §): `Λ(t) = ∫₀ᵗ dF/S(s−)`, `ΔΛ = ΔF/S(−) ≤ 1`, finiteness
of `Λ` before the endpoint of the support.

**Proof formalization notes.** The hygiene lemma: `{t | μ [t,∞) = 0}` is an up-set, hence an
interval `(a, ∞)` or `[a, ∞)`; its measure is the decreasing limit of `μ [tₙ, ∞) = 0` by
continuity of measure — 10–20 lines of order-topology care, no atomlessness. The atom formula
is `withDensity_apply` on a singleton; the `≤ 1` bound holds *unconditionally* — where
`S(t−) = 0` monotonicity forces `μ{t} = 0` and the ENNReal convention `0 · ∞ = 0` gives
`ΔΛ = 0` (consciously exploited, documented here once). Local finiteness bounds the density on
`(-∞, t]` by antitonicity.

**Bibliographic comments.** Aalen 1978 (*Ann. Statist.* **6**, 701–726) for the cumulative
hazard as compensator; the `ΔΛ ≤ 1` normalization is the discrete-hazard bound underlying the
product-limit construction (Kaplan–Meier 1958).
-/

open MeasureTheory Set

namespace StatLean.StatisticalModels.Survival

variable {μ : Measure ℝ}

/-- The hazard-density integrand is measurable (antitone set function of the endpoint). -/
theorem measurable_survivalLeft_inv (μ : Measure ℝ) :
    Measurable fun t => (μ (Ici t))⁻¹ :=
  (Antitone.measurable fun _ _ hab => measure_mono (Ici_subset_Ici.2 hab)).inv

/-- **Hygiene lemma** (LEAN-ONLY; no book analogue): the region where the left-limit survival
vanishes is null for the law itself. Consequently the hazard density is `μ`-a.e. finite and
every downstream `0⁻¹ = ∞` corner is measure-theoretically invisible. -/
theorem measure_survivalLeft_zero (μ : Measure ℝ) :
    μ {t | μ (Ici t) = 0} = 0 := by
  set Z : Set ℝ := {t | μ (Ici t) = 0} with hZdef
  have hup : ∀ {s t : ℝ}, s ≤ t → s ∈ Z → t ∈ Z := fun hst hs =>
    measure_mono_null (Ici_subset_Ici.2 hst) hs
  by_cases hnomin : ∀ z ∈ Z, ∃ z' ∈ Z, z' < z
  · -- `Z` has no least element: it is the countable union of the `[q, ∞)` for rational `q ∈ Z`.
    have hcov : Z ⊆ ⋃ q : {q : ℚ // ((q : ℚ) : ℝ) ∈ Z}, Ici ((q : ℚ) : ℝ) := by
      intro t ht
      obtain ⟨z, hzZ, hzt⟩ := hnomin t ht
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hzt
      exact mem_iUnion.2 ⟨⟨q, hup hq1.le hzZ⟩, hq2.le⟩
    exact measure_mono_null hcov (measure_iUnion_null fun q => q.2)
  · -- `Z` has a least element `z`, and `Z ⊆ [z, ∞)` which is already null.
    obtain ⟨z, hzZ, hz⟩ : ∃ z ∈ Z, ∀ z' ∈ Z, z ≤ z' := by
      by_contra hcon
      refine hnomin fun z hz => ?_
      by_contra hcon'
      exact hcon ⟨z, hz, fun z' hz' => not_lt.1 fun hlt => hcon' ⟨z', hz', hlt⟩⟩
    exact measure_mono_null (fun x hx => hz x hx) hzZ

/-- A.e. finiteness of the hazard density (the usable form of the hygiene lemma). -/
theorem ae_inv_survivalLeft_lt_top (μ : Measure ℝ) :
    ∀ᵐ t ∂μ, (μ (Ici t))⁻¹ < ⊤ := by
  rw [ae_iff]
  refine measure_mono_null (fun t ht => ?_) (measure_survivalLeft_zero μ)
  simpa only [not_lt, top_le_iff, ENNReal.inv_eq_top] using ht

/-- Evaluation of the cumulative-hazard measure. -/
theorem cumHazard_apply (μ : Measure ℝ) {A : Set ℝ}
    -- LEAN-ONLY: the evaluation set is measurable (withDensity_apply)
    (hA : MeasurableSet A) :
    cumHazard μ A = ∫⁻ t in A, (μ (Ici t))⁻¹ ∂μ :=
  withDensity_apply _ hA

-- The hypothesis `ht` below is not needed for the identity: where `μ [t, ∞) = 0`
-- monotonicity forces `μ {t} = 0`, and both sides are then `0` (`∞ * 0 = 0`, `0 / 0 = 0`).
-- It is kept because the statement is frozen; the linter is silenced for that binder only.
set_option linter.unusedVariables false in
/-- **Atom formula** `ΔΛ(t) = μ{t}/S(t−)` where the denominator does not vanish
(ABGK §II.1: `ΔΛ = ΔF/S(−)`). -/
theorem cumHazardJump_eq (μ : Measure ℝ) {t : ℝ}
    -- USER-INPUT: the left-limit survival is positive at t (inside the support);
    -- ABGK §II.1
    (ht : μ (Ici t) ≠ 0) :
    cumHazardJump μ t = μ {t} / μ (Ici t) := by
  have hval : cumHazardJump μ t = (μ (Ici t))⁻¹ * μ {t} := by
    rw [cumHazardJump, cumHazard_apply μ (measurableSet_singleton t), lintegral_singleton]
  rw [hval, ENNReal.div_eq_inv_mul]

/-- The hazard jump is at most one, **unconditionally**: where `S(t−) = 0`, monotonicity
forces `μ{t} = 0` and `0 · ∞ = 0` (the one place the ENNReal convention is load-bearing). -/
theorem cumHazardJump_le_one (μ : Measure ℝ) (t : ℝ) :
    cumHazardJump μ t ≤ 1 := by
  have hval : cumHazardJump μ t = (μ (Ici t))⁻¹ * μ {t} := by
    rw [cumHazardJump, cumHazard_apply μ (measurableSet_singleton t), lintegral_singleton]
  have hsub : μ {t} ≤ μ (Ici t) := measure_mono (singleton_subset_iff.2 self_mem_Ici)
  rw [hval]
  rcases eq_or_ne (μ (Ici t)) 0 with h0 | h0
  · simp [le_antisymm (h0 ▸ hsub) (zero_le)]
  · rcases eq_or_ne (μ (Ici t)) ⊤ with htop | htop
    · simp [htop]
    · calc (μ (Ici t))⁻¹ * μ {t} ≤ (μ (Ici t))⁻¹ * μ (Ici t) := by gcongr
        _ = 1 := ENNReal.inv_mul_cancel h0 htop

/-- Local finiteness: up to any time with positive left-limit survival, the cumulative hazard
is bounded by `S(t−)⁻¹` (ABGK §II.1: `Λ` finite before the support endpoint). -/
theorem cumHazard_Iic_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    cumHazard μ (Iic t) ≤ (μ (Ici t))⁻¹ := by
  rw [cumHazard_apply μ measurableSet_Iic]
  calc ∫⁻ s in Iic t, (μ (Ici s))⁻¹ ∂μ
      ≤ ∫⁻ _ in Iic t, (μ (Ici t))⁻¹ ∂μ :=
        setLIntegral_mono' measurableSet_Iic fun s hs =>
          ENNReal.inv_le_inv' (measure_mono (Ici_subset_Ici.2 hs))
    _ = (μ (Ici t))⁻¹ * μ (Iic t) := setLIntegral_const _ _
    _ ≤ (μ (Ici t))⁻¹ * 1 := by gcongr; exact prob_le_one
    _ = (μ (Ici t))⁻¹ := mul_one _

/-- Event-time laws accumulate no hazard on the negative half-line. -/
theorem cumHazard_Iio_zero
    -- USER-INPUT: event-time law; ABGK §II.1
    (h : IsEventTimeLaw μ) :
    cumHazard μ (Iio 0) = 0 := by
  rw [cumHazard_apply μ measurableSet_Iio]
  exact setLIntegral_measure_zero _ _ h.2

end StatLean.StatisticalModels.Survival
