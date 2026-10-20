module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.PointwiseDense
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringRademacher
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

namespace AsymptoticStatistics.EmpiricalProcess
open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable def ghostDifferenceSup {Ω : Type*}
    (F : Set (Ω → ℝ)) (n : ℕ) (x y : Fin n → Ω) : ℝ≥0∞ :=
  supNormOver F (fun f =>
    (Real.sqrt n)⁻¹ * ∑ i, (f (x i) - f (y i)))

@[simp] theorem ghostDifferenceSup_zero_sample {Ω : Type*}
    (F : Set (Ω → ℝ)) (x y : Fin 0 → Ω) :
    ghostDifferenceSup F 0 x y = 0 := by
  simp [ghostDifferenceSup, supNormOver]

theorem supNormOver_eq_of_pointwiseDense
    {Ω : Type*} {F F' : Set (Ω → ℝ)}
    (hsub : F' ⊆ F)
    (hApprox : ∀ f ∈ F, ∃ φ : ℕ → (Ω → ℝ),
      (∀ m, φ m ∈ F') ∧
        ∀ x, Tendsto (fun m => φ m x) atTop (𝓝 (f x)))
    (z : (Ω → ℝ) → ℝ)
    (hz : ∀ f ∈ F, ∀ φ : ℕ → (Ω → ℝ),
      (∀ x, Tendsto (fun m => φ m x) atTop (𝓝 (f x))) →
        Tendsto (fun m => z (φ m)) atTop (𝓝 (z f))) :
    supNormOver F z = supNormOver F' z := by
  apply le_antisymm
  · refine iSup₂_le fun f hf => ?_
    obtain ⟨φ, hφmem, hφlim⟩ := hApprox f hf
    have htend : Tendsto (fun m => ENNReal.ofReal |z (φ m)|) atTop
        (𝓝 (ENNReal.ofReal |z f|)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        ((continuous_abs.tendsto _).comp (hz f hf φ hφlim))
    refine le_of_tendsto' htend fun m => ?_
    exact le_supNormOver (hφmem m)
  · exact supNormOver_mono hsub z

theorem ghostDifferenceSup_eq_of_pointwiseDense
    {Ω : Type*} {F F' : Set (Ω → ℝ)}
    (hsub : F' ⊆ F)
    (hApprox : ∀ f ∈ F, ∃ φ : ℕ → (Ω → ℝ),
      (∀ m, φ m ∈ F') ∧
        ∀ x, Tendsto (fun m => φ m x) atTop (𝓝 (f x)))
    (n : ℕ) (x y : Fin n → Ω) :
    ghostDifferenceSup F n x y = ghostDifferenceSup F' n x y := by
  apply supNormOver_eq_of_pointwiseDense hsub hApprox
  intro f _ φ hφ
  apply tendsto_const_nhds.mul
  exact tendsto_finset_sum Finset.univ fun i _ =>
    (hφ (x i)).sub (hφ (y i))

theorem rademacherSup_eq_of_pointwiseDense
    {Ω : Type*} {F F' : Set (Ω → ℝ)}
    (hsub : F' ⊆ F)
    (hApprox : ∀ f ∈ F, ∃ φ : ℕ → (Ω → ℝ),
      (∀ m, φ m ∈ F') ∧
        ∀ x, Tendsto (fun m => φ m x) atTop (𝓝 (f x)))
    (n : ℕ) (x : Fin n → Ω) (ε : Fin n → Bool) :
    rademacherSup F n x ε = rademacherSup F' n x ε := by
  apply supNormOver_eq_of_pointwiseDense hsub hApprox
  intro f _ φ hφ
  apply tendsto_const_nhds.mul
  exact tendsto_finset_sum Finset.univ fun i _ =>
    tendsto_const_nhds.mul (hφ (x i))

theorem measurable_empiricalProcessSup_dense
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hF_meas : ∀ f ∈ F, Measurable f) (n : ℕ) :
    Measurable (fun ξ : Ξ =>
      supNormOver F
        (empiricalProcess P n (fun i : Fin n => X i.val ξ))) := by
  obtain ⟨F', hsub, hct, hApprox, Φ, hΦint, hΦdom⟩ := hDense
  have hDense' : EmpProcPointwiseDense F P :=
    ⟨F', hsub, hct, hApprox, Φ, hΦint, hΦdom⟩
  have hbound : Integrable (fun x => (Φ x + |(0 : ℝ)|) * |(1 : ℝ)|) P := by
    simpa using hΦint
  simpa [supNormOver, transformedEmpProcess] using
    measurable_biSup_ofReal_abs_transformedEmpProcess_dense
      hDense' hX_meas hF_meas measurable_const measurable_const hΦdom hbound n

theorem measurable_ghostDifferenceSup_dense
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f) (n : ℕ) :
    Measurable (fun z : (Fin n → Ω) × (Fin n → Ω) =>
      ghostDifferenceSup F n z.1 z.2) := by
  obtain ⟨F', hsub, hct, hApprox, _⟩ := hDense
  have heq : (fun z : (Fin n → Ω) × (Fin n → Ω) =>
      ghostDifferenceSup F n z.1 z.2) =
      fun z => ghostDifferenceSup F' n z.1 z.2 := by
    funext z
    exact ghostDifferenceSup_eq_of_pointwiseDense hsub hApprox n z.1 z.2
  rw [heq]
  unfold ghostDifferenceSup supNormOver
  refine Measurable.biSup F' hct fun f hf => ?_
  have hfmeas : Measurable f := hF_meas f (hsub hf)
  have hval : Measurable (fun z : (Fin n → Ω) × (Fin n → Ω) =>
      (Real.sqrt n)⁻¹ * ∑ i, (f (z.1 i) - f (z.2 i))) := by
    apply measurable_const.mul
    exact Finset.measurable_sum Finset.univ fun i _ =>
      (hfmeas.comp ((measurable_pi_apply i).comp measurable_fst)).sub
        (hfmeas.comp ((measurable_pi_apply i).comp measurable_snd))
  simpa [Real.norm_eq_abs] using hval.norm.ennreal_ofReal

theorem measurable_rademacherSup_dense
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f) (n : ℕ) :
    Measurable (fun z : (Fin n → Ω) × (Fin n → Bool) =>
      rademacherSup F n z.1 z.2) := by
  obtain ⟨F', hsub, hct, hApprox, _⟩ := hDense
  have heq : (fun z : (Fin n → Ω) × (Fin n → Bool) =>
      rademacherSup F n z.1 z.2) =
      fun z => rademacherSup F' n z.1 z.2 := by
    funext z
    exact rademacherSup_eq_of_pointwiseDense hsub hApprox n z.1 z.2
  rw [heq]
  unfold rademacherSup supNormOver rademacherAverage
  refine Measurable.biSup F' hct fun f hf => ?_
  have hfmeas : Measurable f := hF_meas f (hsub hf)
  have hval : Measurable (fun z : (Fin n → Ω) × (Fin n → Bool) =>
      (Real.sqrt n)⁻¹ *
        ∑ i, ProbabilityTheory.rademacherSign (z.2 i) * f (z.1 i)) := by
    apply measurable_const.mul
    exact Finset.measurable_sum Finset.univ fun i _ =>
      ((measurable_of_finite
        (fun ε : Fin n → Bool => ProbabilityTheory.rademacherSign (ε i))).comp
          measurable_snd).mul
        (hfmeas.comp ((measurable_pi_apply i).comp measurable_fst))
  simpa [Real.norm_eq_abs] using hval.norm.ennreal_ofReal

theorem measurable_conditionalRademacherSup_dense
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f) (n : ℕ) :
    Measurable (fun x : Fin n → Ω =>
      conditionalRademacherSup F n x) := by
  exact (measurable_rademacherSup_dense P F hDense hF_meas n).lintegral_prod_right'

theorem measurable_canonicalEmpiricalProcessSup_dense
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f) (n : ℕ) :
    Measurable (fun x : Fin n → Ω =>
      supNormOver F (empiricalProcess P n x)) := by
  cases n with
  | zero =>
      simp [supNormOver]
  | succ k =>
      let X : ℕ → (Fin (k + 1) → Ω) → Ω := fun j x =>
        x ⟨j % (k + 1), Nat.mod_lt j (by omega)⟩
      have hX_meas : ∀ j, Measurable (X j) := fun j => by
        simpa only [X] using
          (measurable_pi_apply
            (⟨j % (k + 1), Nat.mod_lt j (by omega)⟩ : Fin (k + 1)))
      have hX_fin (x : Fin (k + 1) → Ω) :
          (fun i : Fin (k + 1) => X i.val x) = x := by
        funext i
        apply congrArg x
        apply Fin.ext
        exact Nat.mod_eq_of_lt i.isLt
      have hmeas := measurable_empiricalProcessSup_dense
        P F hDense X hX_meas hF_meas (k + 1)
      have heq :
          (fun x : Fin (k + 1) → Ω => supNormOver F
            (empiricalProcess P (k + 1)
              (fun i : Fin (k + 1) => X i.val x))) =
          fun x => supNormOver F (empiricalProcess P (k + 1) x) := by
        funext x
        rw [hX_fin x]
      rw [← heq]
      exact hmeas

theorem measurable_empiricalL2Seminorm
    {Ω : Type*} [MeasurableSpace Ω]
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ) (n : ℕ) :
    Measurable (fun x : Fin n → Ω => empiricalL2Seminorm n x Φ) := by
  unfold empiricalL2Seminorm empiricalAvg
  apply Measurable.sqrt
  apply measurable_const.mul
  exact Finset.measurable_sum Finset.univ fun i _ =>
    ((hΦ_meas.comp (measurable_pi_apply i)).abs.pow_const 2)

theorem tendsto_empiricalL2Seminorm_of_pointwise
    {Ω : Type*} {φ : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hφ : ∀ x, Tendsto (fun m => φ m x) atTop (𝓝 (f x)))
    (n : ℕ) (X : Fin n → Ω) :
    Tendsto (fun m => empiricalL2Seminorm n X (φ m))
      atTop (𝓝 (empiricalL2Seminorm n X f)) := by
  unfold empiricalL2Seminorm empiricalAvg
  apply Real.continuous_sqrt.continuousAt.tendsto.comp
  apply tendsto_const_nhds.mul
  exact tendsto_finset_sum Finset.univ fun i _ =>
    ((continuous_abs.tendsto _).comp (hφ (X i))).pow 2

theorem empiricalRelativeRadius_eq_of_pointwiseDense
    {Ω : Type*} {F F' : Set (Ω → ℝ)}
    (hsub : F' ⊆ F)
    (hApprox : ∀ f ∈ F, ∃ φ : ℕ → (Ω → ℝ),
      (∀ m, φ m ∈ F') ∧ ∀ x, Tendsto (fun m => φ m x) atTop (𝓝 (f x)))
    (Φ : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) :
    empiricalRelativeRadius F Φ n X = empiricalRelativeRadius F' Φ n X := by
  by_cases hzero : empiricalL2Seminorm n X Φ = 0
  · simp [empiricalRelativeRadius, hzero]
  rw [empiricalRelativeRadius, if_neg hzero,
    empiricalRelativeRadius, if_neg hzero]
  apply le_antisymm
  · refine iSup₂_le fun f hf => ?_
    obtain ⟨φ, hφmem, hφlim⟩ := hApprox f hf
    have htend : Tendsto (fun m => ENNReal.ofReal
        (empiricalL2Seminorm n X (φ m) / empiricalL2Seminorm n X Φ)) atTop
        (𝓝 (ENNReal.ofReal
          (empiricalL2Seminorm n X f / empiricalL2Seminorm n X Φ))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        ((tendsto_empiricalL2Seminorm_of_pointwise hφlim n X).div_const _)
    refine le_of_tendsto' htend fun m => ?_
    exact le_iSup_of_le (φ m) (le_iSup_of_le (hφmem m) le_rfl)
  · refine iSup₂_le fun f hf => ?_
    exact le_iSup_of_le f (le_iSup_of_le (hsub hf) le_rfl)

theorem measurable_empiricalRelativeRadius_of_countable
    {Ω : Type*} [MeasurableSpace Ω]
    (F : Set (Ω → ℝ)) (hF_countable : F.Countable)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ) (n : ℕ) :
    Measurable (fun X : Fin n → Ω => empiricalRelativeRadius F Φ n X) := by
  unfold empiricalRelativeRadius
  have hden : Measurable (fun X : Fin n → Ω =>
      empiricalL2Seminorm n X Φ) :=
    measurable_empiricalL2Seminorm Φ hΦ_meas n
  apply Measurable.ite (hden (measurableSet_singleton 0)) measurable_const
  refine Measurable.biSup F hF_countable fun f hf => ?_
  exact ((measurable_empiricalL2Seminorm f (hF_meas f hf) n).div hden).ennreal_ofReal

theorem measurable_empiricalRelativeRadius_of_pointwiseDense
    {Ω : Type*} [MeasurableSpace Ω] {F F' : Set (Ω → ℝ)}
    (hsub : F' ⊆ F) (hF'_countable : F'.Countable)
    (hApprox : ∀ f ∈ F, ∃ φ : ℕ → (Ω → ℝ),
      (∀ m, φ m ∈ F') ∧ ∀ x, Tendsto (fun m => φ m x) atTop (𝓝 (f x)))
    (hF'_meas : ∀ f ∈ F', Measurable f)
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ) (n : ℕ) :
    Measurable (fun X : Fin n → Ω => empiricalRelativeRadius F Φ n X) := by
  have heq : (fun X : Fin n → Ω => empiricalRelativeRadius F Φ n X) =
      fun X => empiricalRelativeRadius F' Φ n X := by
    funext X
    exact empiricalRelativeRadius_eq_of_pointwiseDense hsub hApprox Φ n X
  rw [heq]
  exact measurable_empiricalRelativeRadius_of_countable
    F' hF'_countable hF'_meas Φ hΦ_meas n

theorem measurable_empiricalRelativeRadiusReal_of_pointwiseDense
    {Ω : Type*} [MeasurableSpace Ω] {F F' : Set (Ω → ℝ)}
    (hsub : F' ⊆ F) (hF'_countable : F'.Countable)
    (hApprox : ∀ f ∈ F, ∃ φ : ℕ → (Ω → ℝ),
      (∀ m, φ m ∈ F') ∧ ∀ x, Tendsto (fun m => φ m x) atTop (𝓝 (f x)))
    (hF'_meas : ∀ f ∈ F', Measurable f)
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ) (n : ℕ) :
    Measurable (fun X : Fin n → Ω => empiricalRelativeRadiusReal F Φ n X) := by
  simpa only [empiricalRelativeRadiusReal] using
    (measurable_empiricalRelativeRadius_of_pointwiseDense hsub hF'_countable
      hApprox hF'_meas Φ hΦ_meas n).ennreal_toReal

end AsymptoticStatistics.EmpiricalProcess
