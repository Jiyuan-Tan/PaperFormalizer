module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChangingClassUniform

@[expose] public section

/-!
# Finite approximations of changing-class empirical processes

This file constructs finite metric approximations of the index set and bounds
the resulting process projection error by a local empirical-process supremum.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open scoped ENNReal

/-- Evaluation of the bounded changing-class process is the corresponding
empirical-process coordinate. -/
@[simp] theorem changingClassEmpiricalProcessLinf_apply
    {Ω T : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → T → Ω → ℝ) (Φ : ℕ → Ω → ℝ)
    (hΦ : ChangingEnvelope f Φ) (hLin : ChangingLindeberg P Φ)
    (hf_meas : ∀ n t, Measurable (f n t))
    (hΦmeas : ∀ n, Measurable (Φ n))
    (n : ℕ) (sample : Fin n → Ω) (t : T) :
    changingClassEmpiricalProcessLinf
      P f Φ hΦ hLin hf_meas hΦmeas n sample t =
      empiricalProcess P n sample (f n t) := by
  rfl

/-- A totally bounded pseudometric index set admits a finite approximation
whose representative of every cell lies within the prescribed radius. -/
theorem exists_finiteApproximation_dist_lt
    {T : Type*} [PseudoMetricSpace T]
    (hTB : TotallyBounded (Set.univ : Set T))
    {r : ℝ} (hr : 0 < r) :
    ∃ a : FiniteApproximation T,
      ∀ t : T, dist t (a.rep (a.cell t)) < r := by
  obtain ⟨s, -, hs_fin, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded hTB r hr
  letI : Fintype s := hs_fin.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  have hnear : ∀ t : T, ∃ u : s, dist t u.1 < r := by
    intro t
    have ht := hcover (Set.mem_univ t)
    simp only [Set.mem_iUnion, Metric.mem_ball] at ht
    obtain ⟨u, hu, htu⟩ := ht
    exact ⟨⟨u, hu⟩, htu⟩
  let center : T → s := fun t => Classical.choose (hnear t)
  let a : FiniteApproximation T :=
    { k := Fintype.card s
      cell := fun t => e (center t)
      rep := fun i => (e.symm i).1 }
  refine ⟨a, fun t => ?_⟩
  change dist t ((e.symm (e (center t))).1) < r
  simpa only [Equiv.symm_apply_apply] using Classical.choose_spec (hnear t)

/-- Projecting a changing-class empirical-process path to nearby
representatives costs at most its supremum over local row increments. -/
theorem ofReal_norm_changingClass_sub_project_le
    {Ω T : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → T → Ω → ℝ) (Φ : ℕ → Ω → ℝ)
    (hΦ : ChangingEnvelope f Φ) (hLin : ChangingLindeberg P Φ)
    (hf_meas : ∀ n t, Measurable (f n t))
    (hΦmeas : ∀ n, Measurable (Φ n))
    {r : ℝ} (a : FiniteApproximation T)
    (ha : ∀ t : T, dist t (a.rep (a.cell t)) < r)
    (n : ℕ) (sample : Fin n → Ω) :
    ENNReal.ofReal ‖
      changingClassEmpiricalProcessLinf
          P f Φ hΦ hLin hf_meas hΦmeas n sample -
        a.project
          (changingClassEmpiricalProcessLinf
            P f Φ hΦ hLin hf_meas hΦmeas n sample)‖ ≤
      supNormOver (changingLocalDifferenceClass f n r)
        (empiricalProcess P n sample) := by
  let B := supNormOver (changingLocalDifferenceClass f n r)
    (empiricalProcess P n sample)
  by_cases hB : B = ⊤
  · simp only [B] at hB ⊢
    rw [hB]
    exact le_top
  rw [ENNReal.ofReal_le_iff_le_toReal hB]
  apply lp.norm_le_of_forall_le ENNReal.toReal_nonneg
  intro t
  have hf_int : ∀ u : T, Integrable (f n u) P := by
    intro u
    have hfu : MemLp (f n u) 2 P :=
      MemLp.mono' (hLin.envelope_memLp_two hΦmeas n)
        (hf_meas n u).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          have hΦnonneg : 0 ≤ Φ n x :=
            (abs_nonneg (f n u x)).trans (hΦ n u x)
          simpa only [Real.norm_eq_abs, abs_of_nonneg hΦnonneg] using hΦ n u x)
    exact hfu.integrable (by norm_num)
  have hmem : (fun x => f n t x - f n (a.rep (a.cell t)) x) ∈
      changingLocalDifferenceClass f n r :=
    ⟨t, a.rep (a.cell t), ha t, rfl⟩
  have hcoord := le_supNormOver
    (z := empiricalProcess P n sample) hmem
  change ENNReal.ofReal
      |empiricalProcess P n sample (fun x =>
        f n t x - f n (a.rep (a.cell t)) x)| ≤ B at hcoord
  rw [ENNReal.ofReal_le_iff_le_toReal hB] at hcoord
  simp only [lp.coeFn_sub, Pi.sub_apply,
    changingClassEmpiricalProcessLinf_apply,
    FiniteApproximation.project_apply, Real.norm_eq_abs]
  rw [← empiricalProcess_sub P n sample _ _ (hf_int t)
    (hf_int (a.rep (a.cell t)))]
  exact hcoord

end AsymptoticStatistics.EmpiricalProcess
