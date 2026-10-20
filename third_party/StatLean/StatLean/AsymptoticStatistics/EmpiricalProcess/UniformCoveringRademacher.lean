module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringExtraction
public import StatLean.AsymptoticStatistics.ForMathlib.Probability.Rademacher
public import StatLean.AsymptoticStatistics.ForMathlib.Probability.GaussianMaximal
public import StatLean.AsymptoticStatistics.ForMathlib.Probability.SubgaussianGaussian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finset.Prod

@[expose] public section

/-!
# Empirical `L²` geometry for conditional Rademacher sums

This file records the realized empirical seminorm and its induced
semidistance, including the finite-discrete readout used by conditional
Rademacher chaining.
-/

namespace AsymptoticStatistics.EmpiricalProcess
open scoped ENNReal InnerProductSpace NNReal
open MeasureTheory ProbabilityTheory
variable {Ω : Type*}

/-- The realized empirical `L²` seminorm of a function.

This is the sample geometry used in the conditional chaining argument for
vdV Lemma 19.38. Edge behavior: the empty sample has seminorm zero. -/
noncomputable def empiricalL2Seminorm
    (n : ℕ) (X : Fin n → Ω) (f : Ω → ℝ) : ℝ :=
  Real.sqrt (empiricalAvg (fun y => |f y| ^ 2) n X)

/-- The semidistance induced by the realized empirical `L²` seminorm.

Edge behavior: the empty sample gives distance zero. -/
noncomputable def empiricalL2Dist
    (n : ℕ) (X : Fin n → Ω) (f g : Ω → ℝ) : ℝ :=
  empiricalL2Seminorm n X (f - g)

theorem empiricalL2Seminorm_nonneg (n : ℕ) (X : Fin n → Ω) (f : Ω → ℝ) :
    0 ≤ empiricalL2Seminorm n X f :=
  Real.sqrt_nonneg _

@[simp] theorem empiricalL2Seminorm_zero (X : Fin 0 → Ω) (f : Ω → ℝ) :
    empiricalL2Seminorm 0 X f = 0 := by
  simp [empiricalL2Seminorm]

@[simp] theorem empiricalL2Dist_zero (X : Fin 0 → Ω) (f g : Ω → ℝ) :
    empiricalL2Dist 0 X f g = 0 := by
  simp [empiricalL2Dist]

theorem empiricalL2Seminorm_mono_on_sample (n : ℕ) (X : Fin n → Ω)
    (f g : Ω → ℝ) (h : ∀ i, |f (X i)| ≤ |g (X i)|) :
    empiricalL2Seminorm n X f ≤ empiricalL2Seminorm n X g := by
  unfold empiricalL2Seminorm empiricalAvg
  apply Real.sqrt_le_sqrt
  gcongr with i
  nlinarith [abs_nonneg (f (X i)), abs_nonneg (g (X i)), h i]

theorem finiteDiscrete_distL2_eq_empiricalL2Dist
    (Q : FiniteDiscreteProbability Ω) (n : ℕ) (X : Fin n → Ω)
    (hQ : ∀ h, Q.l2Seminorm h = empiricalL2Seminorm n X h)
    (f g : Ω → ℝ) :
    Q.distL2 f g = empiricalL2Dist n X f g := by
  exact hQ (f - g)

/-- The realized relative `L²` radius of a class with respect to an envelope.

This is the radius in vdV Lemma 19.38 for a fixed sample. Edge behavior: a
zero empirical envelope seminorm gives radius zero. -/
noncomputable def empiricalRelativeRadius {Ω : Type*}
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) : ℝ≥0∞ :=
  if empiricalL2Seminorm n X Φ = 0 then 0 else
    ⨆ f ∈ F, ENNReal.ofReal
      (empiricalL2Seminorm n X f / empiricalL2Seminorm n X Φ)

/-- The real-valued readout of the realized relative radius.

Edge behavior follows `ENNReal.toReal`: in particular, zero remains zero. -/
noncomputable def empiricalRelativeRadiusReal {Ω : Type*}
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) : ℝ :=
  (empiricalRelativeRadius F Φ n X).toReal

@[simp] theorem empiricalRelativeRadius_of_empiricalL2Seminorm_eq_zero
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω)
    (hΦ : empiricalL2Seminorm n X Φ = 0) :
    empiricalRelativeRadius F Φ n X = 0 := by
  simp [empiricalRelativeRadius, hΦ]

@[simp] theorem empiricalRelativeRadiusReal_of_empiricalL2Seminorm_eq_zero
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω)
    (hΦ : empiricalL2Seminorm n X Φ = 0) :
    empiricalRelativeRadiusReal F Φ n X = 0 := by
  simp [empiricalRelativeRadiusReal, hΦ]

@[simp] theorem empiricalRelativeRadius_zero
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (X : Fin 0 → Ω) :
    empiricalRelativeRadius F Φ 0 X = 0 := by
  simp

@[simp] theorem empiricalRelativeRadiusReal_zero
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (X : Fin 0 → Ω) :
    empiricalRelativeRadiusReal F Φ 0 X = 0 := by
  simp [empiricalRelativeRadiusReal]

@[simp] theorem empiricalRelativeRadius_empty
    {Ω : Type*} (Φ : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) :
    empiricalRelativeRadius (∅ : Set (Ω → ℝ)) Φ n X = 0 := by
  simp [empiricalRelativeRadius]

@[simp] theorem empiricalRelativeRadiusReal_empty
    {Ω : Type*} (Φ : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) :
    empiricalRelativeRadiusReal (∅ : Set (Ω → ℝ)) Φ n X = 0 := by
  simp [empiricalRelativeRadiusReal]

theorem empiricalL2Seminorm_le_envelope
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (hΦ : IsEnvelope F Φ)
    (f : Ω → ℝ) (hf : f ∈ F) :
    empiricalL2Seminorm n X f ≤ empiricalL2Seminorm n X Φ := by
  apply empiricalL2Seminorm_mono_on_sample
  intro i
  exact (hΦ f hf (X i)).trans (le_abs_self (Φ (X i)))

theorem empiricalRelativeRadius_le_one_of_isEnvelope
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (hΦ : IsEnvelope F Φ) :
    empiricalRelativeRadius F Φ n X ≤ 1 := by
  by_cases hzero : empiricalL2Seminorm n X Φ = 0
  · simp [empiricalRelativeRadius, hzero]
  · rw [empiricalRelativeRadius, if_neg hzero]
    refine iSup_le fun f => iSup_le fun hf => ?_
    rw [ENNReal.ofReal_le_one]
    apply (div_le_one ?_).2
    · exact empiricalL2Seminorm_le_envelope F Φ n X hΦ f hf
    · exact lt_of_le_of_ne (empiricalL2Seminorm_nonneg n X Φ) (Ne.symm hzero)

theorem empiricalRelativeRadiusReal_le_one_of_isEnvelope
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (hΦ : IsEnvelope F Φ) :
    empiricalRelativeRadiusReal F Φ n X ≤ 1 := by
  unfold empiricalRelativeRadiusReal
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top
      (empiricalRelativeRadius_le_one_of_isEnvelope F Φ n X hΦ)

theorem empiricalRelativeRadius_lt_top_of_isEnvelope
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (hΦ : IsEnvelope F Φ) :
    empiricalRelativeRadius F Φ n X < ⊤ :=
  (empiricalRelativeRadius_le_one_of_isEnvelope F Φ n X hΦ).trans_lt
    ENNReal.one_lt_top

theorem ofReal_empiricalRelativeRadiusReal_of_isEnvelope
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (hΦ : IsEnvelope F Φ) :
    ENNReal.ofReal (empiricalRelativeRadiusReal F Φ n X) =
      empiricalRelativeRadius F Φ n X := by
  apply ENNReal.ofReal_toReal
  exact ne_of_lt (empiricalRelativeRadius_lt_top_of_isEnvelope F Φ n X hΦ)

theorem finiteDiscreteRelativeRadius_eq_empiricalRelativeRadius
    {Ω : Type*} (Q : FiniteDiscreteProbability Ω)
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω)
    (hQ : ∀ h : Ω → ℝ,
      Q.l2Seminorm h = empiricalL2Seminorm n X h) :
    finiteDiscreteRelativeRadius Q F Φ =
      empiricalRelativeRadius F Φ n X := by
  by_cases hzero : empiricalL2Seminorm n X Φ = 0
  · simp [finiteDiscreteRelativeRadius, empiricalRelativeRadius, hQ, hzero]
  · simp [finiteDiscreteRelativeRadius, empiricalRelativeRadius, hQ, hzero]

noncomputable def rademacherAverage {Ω : Type*}
    (n : ℕ) (X : Fin n → Ω) (ε : Fin n → Bool)
    (f : Ω → ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ *
    ∑ i, rademacherSign (ε i) * f (X i)

@[simp] theorem rademacherAverage_zero_sample
    {Ω : Type*} (X : Fin 0 → Ω) (ε : Fin 0 → Bool)
    (f : Ω → ℝ) :
    rademacherAverage 0 X ε f = 0 := by
  simp [rademacherAverage]

@[simp] theorem rademacherAverage_zero_function
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (ε : Fin n → Bool) :
    rademacherAverage n X ε (fun _ : Ω => 0) = 0 := by
  simp [rademacherAverage]

theorem rademacherAverage_sub
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (ε : Fin n → Bool) (f g : Ω → ℝ) :
    rademacherAverage n X ε (f - g) =
      rademacherAverage n X ε f -
        rademacherAverage n X ε g := by
  simp [rademacherAverage, mul_sub, Finset.sum_sub_distrib]

theorem rademacherAverage_eq_rademacherSum
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (ε : Fin n → Bool) (f : Ω → ℝ) :
    rademacherAverage n X ε f =
      rademacherSum
        (fun i => (Real.sqrt n)⁻¹ * f (X i)) ε := by
  unfold rademacherAverage rademacherSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rademacherAverage_proxy_eq_empiricalL2Seminorm_sq
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (f : Ω → ℝ) :
    (∑ i, (⟨((Real.sqrt n)⁻¹ * f (X i)) ^ 2,
      sq_nonneg ((Real.sqrt n)⁻¹ * f (X i))⟩ : ℝ≥0)) =
    (⟨empiricalL2Seminorm n X f ^ 2,
      sq_nonneg (empiricalL2Seminorm n X f)⟩ : ℝ≥0) := by
  have hreal :
      (∑ i, ((Real.sqrt n)⁻¹ * f (X i)) ^ 2) =
        empiricalL2Seminorm n X f ^ 2 := by
    by_cases hn : n = 0
    · subst n
      simp
    · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have havg_nonneg :
          0 ≤ empiricalAvg (fun y => |f y| ^ 2) n X := by
        unfold empiricalAvg
        positivity
      rw [empiricalL2Seminorm, Real.sq_sqrt havg_nonneg]
      unfold empiricalAvg
      calc
        ∑ i, ((Real.sqrt n)⁻¹ * f (X i)) ^ 2 =
            (Real.sqrt n)⁻¹ ^ 2 * ∑ i, f (X i) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [mul_pow]
        _ = (n : ℝ)⁻¹ * ∑ i, f (X i) ^ 2 := by
          rw [inv_pow, Real.sq_sqrt hnpos.le]
        _ = (n : ℝ)⁻¹ * ∑ i, |f (X i)| ^ 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact (sq_abs (f (X i))).symm
  apply NNReal.eq
  calc
    (↑(∑ i, (⟨((Real.sqrt n)⁻¹ * f (X i)) ^ 2,
        sq_nonneg ((Real.sqrt n)⁻¹ * f (X i))⟩ : ℝ≥0)) : ℝ) =
        ∑ i, ((Real.sqrt n)⁻¹ * f (X i)) ^ 2 := by
      exact NNReal.coe_sum _ _
    _ = empiricalL2Seminorm n X f ^ 2 := hreal
    _ = (↑(⟨empiricalL2Seminorm n X f ^ 2,
        sq_nonneg (empiricalL2Seminorm n X f)⟩ : ℝ≥0) : ℝ) := rfl

theorem rademacherAverage_hasSubgaussianMGF
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (f : Ω → ℝ) :
    HasSubgaussianMGF
      (fun ε : Fin n → Bool => rademacherAverage n X ε f)
      ⟨empiricalL2Seminorm n X f ^ 2,
        sq_nonneg (empiricalL2Seminorm n X f)⟩
      (rademacherCube n) := by
  have hfun :
      (fun ε : Fin n → Bool => rademacherAverage n X ε f) =
        rademacherSum (fun i => (Real.sqrt n)⁻¹ * f (X i)) := by
    funext ε
    exact rademacherAverage_eq_rademacherSum n X ε f
  rw [hfun, ← rademacherAverage_proxy_eq_empiricalL2Seminorm_sq n X f]
  exact rademacherSum_hasSubgaussianMGF _

theorem rademacherAverage_sub_hasSubgaussianMGF
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (f g : Ω → ℝ) :
    HasSubgaussianMGF
      (fun ε : Fin n → Bool =>
        rademacherAverage n X ε f -
          rademacherAverage n X ε g)
      ⟨empiricalL2Dist n X f g ^ 2,
        sq_nonneg (empiricalL2Dist n X f g)⟩
      (rademacherCube n) := by
  simpa [empiricalL2Dist, rademacherAverage_sub] using
    rademacherAverage_hasSubgaussianMGF n X (f - g)

noncomputable def rademacherSup {Ω : Type*}
    (F : Set (Ω → ℝ)) (n : ℕ) (X : Fin n → Ω)
    (ε : Fin n → Bool) : ℝ≥0∞ :=
  supNormOver F (fun f => rademacherAverage n X ε f)

noncomputable def conditionalRademacherSup {Ω : Type*}
    (F : Set (Ω → ℝ)) (n : ℕ) (X : Fin n → Ω) : ℝ≥0∞ :=
  ∫⁻ ε, rademacherSup F n X ε ∂rademacherCube n

theorem measurable_rademacherSup
    {Ω : Type*} (F : Set (Ω → ℝ)) (n : ℕ) (X : Fin n → Ω) :
    Measurable (fun ε : Fin n → Bool => rademacherSup F n X ε) :=
  measurable_of_finite _

@[simp] theorem rademacherSup_empty
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω) (ε : Fin n → Bool) :
    rademacherSup (∅ : Set (Ω → ℝ)) n X ε = 0 := by
  simp [rademacherSup, supNormOver]

@[simp] theorem conditionalRademacherSup_empty
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω) :
    conditionalRademacherSup (∅ : Set (Ω → ℝ)) n X = 0 := by
  simp [conditionalRademacherSup]

@[simp] theorem rademacherSup_zero_sample
    {Ω : Type*} (F : Set (Ω → ℝ))
    (X : Fin 0 → Ω) (ε : Fin 0 → Bool) :
    rademacherSup F 0 X ε = 0 := by
  simp [rademacherSup, supNormOver]

@[simp] theorem conditionalRademacherSup_zero_sample
    {Ω : Type*} (F : Set (Ω → ℝ)) (X : Fin 0 → Ω) :
    conditionalRademacherSup F 0 X = 0 := by
  simp [conditionalRademacherSup]

theorem integral_iSup_abs_rademacherAverage_le
    {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ℕ) (X : Fin n → Ω) (u : ι → Ω → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hu : ∀ i, empiricalL2Seminorm n X (u i) ≤ ρ) :
    ∫ ε, ⨆ i, |rademacherAverage n X ε (u i)|
        ∂rademacherCube n ≤
      Real.sqrt
        (2 * ρ ^ 2 * Real.log (2 * (Fintype.card ι : ℝ))) := by
  let c : ℝ≥0 := ⟨ρ ^ 2, sq_nonneg ρ⟩
  have hc : 0 < c := by
    rw [← NNReal.coe_pos]
    exact pow_pos hρ 2
  have hZ (i : ι) :
      HasSubgaussianMGF
        (fun ε : Fin n → Bool => rademacherAverage n X ε (u i)) c
        (rademacherCube n) := by
    apply (rademacherAverage_hasSubgaussianMGF n X (u i)).mono_proxy
    refine NNReal.coe_le_coe.mp ?_
    change empiricalL2Seminorm n X (u i) ^ 2 ≤ ρ ^ 2
    exact pow_le_pow_left₀ (empiricalL2Seminorm_nonneg n X (u i)) (hu i) 2
  simpa [c] using!
    (expectation_iSup_abs_le_of_subgaussian (μ := rademacherCube n) hc hZ)

theorem lintegral_iSup_ofReal_abs_rademacherAverage_le
    {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ℕ) (X : Fin n → Ω) (u : ι → Ω → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hu : ∀ i, empiricalL2Seminorm n X (u i) ≤ ρ) :
    ∫⁻ ε, ENNReal.ofReal
        (⨆ i, |rademacherAverage n X ε (u i)|)
        ∂rademacherCube n ≤
      ENNReal.ofReal
        (Real.sqrt
          (2 * ρ ^ 2 * Real.log (2 * (Fintype.card ι : ℝ)))) := by
  have hS_int : Integrable
      (fun ε : Fin n → Bool => ⨆ i, |rademacherAverage n X ε (u i)|)
      (rademacherCube n) :=
    integrable_iSup_of_forall_integrable fun i =>
      (rademacherAverage_hasSubgaussianMGF n X (u i)).integrable.abs
  have hS_nonneg : ∀ ε : Fin n → Bool,
      0 ≤ ⨆ i, |rademacherAverage n X ε (u i)| :=
    fun ε => Real.iSup_nonneg fun i => abs_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hS_int
    (Filter.Eventually.of_forall hS_nonneg)]
  exact ENNReal.ofReal_le_ofReal
    (integral_iSup_abs_rademacherAverage_le n X u ρ hρ hu)

theorem lintegral_iSup_ofReal_abs_rademacherIncrement_le
    {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ℕ) (X : Fin n → Ω)
    (f g : ι → Ω → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hfg : ∀ i, empiricalL2Dist n X (f i) (g i) ≤ ρ) :
    ∫⁻ ε, ENNReal.ofReal
        (⨆ i, |rademacherAverage n X ε (f i) -
          rademacherAverage n X ε (g i)|)
        ∂rademacherCube n ≤
      ENNReal.ofReal
        (Real.sqrt
          (2 * ρ ^ 2 * Real.log (2 * (Fintype.card ι : ℝ)))) := by
  simpa [empiricalL2Dist, rademacherAverage_sub] using
    (lintegral_iSup_ofReal_abs_rademacherAverage_le n X (f - g) ρ hρ hfg)

theorem rademacherSup_coe_finset
    {Ω : Type*} (S : Finset (Ω → ℝ)) (hS : S.Nonempty)
    (n : ℕ) (X : Fin n → Ω) (ε : Fin n → Bool) :
    rademacherSup (S : Set (Ω → ℝ)) n X ε =
      ENNReal.ofReal
        (⨆ f : {f // f ∈ S},
          |rademacherAverage n X ε f|) := by
  letI : Nonempty {f // f ∈ S} := hS.coe_sort
  unfold rademacherSup supNormOver
  apply le_antisymm
  · refine iSup_le fun f => iSup_le fun hf => ?_
    exact ENNReal.ofReal_le_ofReal
      (le_ciSup (Finite.bddAbove_range
        (fun g : {f // f ∈ S} => |rademacherAverage n X ε g|))
        (⟨f, hf⟩ : {f // f ∈ S}))
  · rw [← Finset.sup'_univ_eq_ciSup]
    obtain ⟨f, _, hf⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun f : {f // f ∈ S} => |rademacherAverage n X ε f|)
    rw [hf]
    exact le_iSup_of_le f.1 (le_iSup_of_le f.2 le_rfl)

theorem conditionalRademacherSup_finset_le
    {Ω : Type*} (S : Finset (Ω → ℝ))
    (n : ℕ) (X : Fin n → Ω)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSρ : ∀ f ∈ S, empiricalL2Seminorm n X f ≤ ρ) :
    conditionalRademacherSup (S : Set (Ω → ℝ)) n X ≤
      ENNReal.ofReal
        (Real.sqrt
          (2 * ρ ^ 2 * Real.log (2 * (S.card : ℝ)))) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · unfold conditionalRademacherSup
    letI : Nonempty {f // f ∈ S} := hS.coe_sort
    rw [show (fun ε => rademacherSup (S : Set (Ω → ℝ)) n X ε) =
        fun ε => ENNReal.ofReal
          (⨆ f : {f // f ∈ S}, |rademacherAverage n X ε f|) by
      funext ε
      exact rademacherSup_coe_finset S hS n X ε]
    simpa using
      (lintegral_iSup_ofReal_abs_rademacherAverage_le n X
        (fun f : {f // f ∈ S} => (f : Ω → ℝ)) ρ hρ
        (fun f => hSρ f f.property))

@[simp] theorem empiricalL2Seminorm_zero_function
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω) :
    empiricalL2Seminorm n X (0 : Ω → ℝ) = 0 := by
  simp [empiricalL2Seminorm, empiricalAvg]

@[simp] theorem empiricalL2Seminorm_abs
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (f : Ω → ℝ) :
    empiricalL2Seminorm n X (fun x => |f x|) =
      empiricalL2Seminorm n X f := by
  simp [empiricalL2Seminorm]

@[simp] theorem empiricalL2Seminorm_neg
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (f : Ω → ℝ) :
    empiricalL2Seminorm n X (-f) =
      empiricalL2Seminorm n X f := by
  simp [empiricalL2Seminorm]

theorem empiricalL2Seminorm_eq_euclideanNorm
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (f : Ω → ℝ) :
    empiricalL2Seminorm n X f =
      ‖(WithLp.toLp 2
          (fun i : Fin n =>
            (Real.sqrt n)⁻¹ * f (X i)) :
        EuclideanSpace ℝ (Fin n))‖ := by
  let v : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun i : Fin n => (Real.sqrt n)⁻¹ * f (X i))
  have hproxy := rademacherAverage_proxy_eq_empiricalL2Seminorm_sq n X f
  have hsum :
      (∑ i, ((Real.sqrt n)⁻¹ * f (X i)) ^ 2) =
        empiricalL2Seminorm n X f ^ 2 := by
    calc
      (∑ i, ((Real.sqrt n)⁻¹ * f (X i)) ^ 2) =
          NNReal.toReal
            (∑ i, (⟨((Real.sqrt n)⁻¹ * f (X i)) ^ 2,
              sq_nonneg ((Real.sqrt n)⁻¹ * f (X i))⟩ : ℝ≥0)) := by
        exact (NNReal.coe_sum Finset.univ fun i => (⟨((Real.sqrt n)⁻¹ * f (X i)) ^ 2, sq_nonneg _⟩ : ℝ≥0)).symm
      _ = NNReal.toReal
          (⟨empiricalL2Seminorm n X f ^ 2,
            sq_nonneg (empiricalL2Seminorm n X f)⟩ : ℝ≥0) :=
        congrArg NNReal.toReal hproxy
      _ = empiricalL2Seminorm n X f ^ 2 := rfl
  have hv : ‖v‖ ^ 2 = ∑ i, ((Real.sqrt n)⁻¹ * f (X i)) ^ 2 := by
    simpa [v] using EuclideanSpace.real_norm_sq_eq v
  apply (sq_eq_sq₀ (empiricalL2Seminorm_nonneg n X f) (norm_nonneg v)).mp
  exact hsum.symm.trans hv.symm

theorem abs_rademacherAverage_le_sqrt_mul_empiricalL2Seminorm
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (ε : Fin n → Bool) (f : Ω → ℝ) :
    |rademacherAverage n X ε f| ≤
      Real.sqrt n * empiricalL2Seminorm n X f := by
  let s : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun i => rademacherSign (ε i))
  let v : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun i => (Real.sqrt n)⁻¹ * f (X i))
  have havg : rademacherAverage n X ε f = ⟪s, v⟫_ℝ := by
    have hinner (a b : ℝ) : ⟪a, b⟫_ℝ = b * a := RCLike.inner_apply a b
    unfold rademacherAverage
    rw [PiLp.inner_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (Real.sqrt n)⁻¹ * (rademacherSign (ε i) * f (X i)) =
      ⟪rademacherSign (ε i), (Real.sqrt n)⁻¹ * f (X i)⟫_ℝ
    rw [hinner]
    ring
  have hs : ‖s‖ = Real.sqrt n := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp only [s]
    change (∑ i : Fin n, ‖rademacherSign (ε i)‖ ^ 2) = n
    simp [rademacherSign]
  rw [havg, empiricalL2Seminorm_eq_euclideanNorm]
  change |⟪s, v⟫_ℝ| ≤ Real.sqrt n * ‖v‖
  rw [← hs]
  exact abs_real_inner_le_norm s v

theorem empiricalL2Seminorm_add_le
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (f g : Ω → ℝ) :
    empiricalL2Seminorm n X (f + g) ≤
      empiricalL2Seminorm n X f +
        empiricalL2Seminorm n X g := by
  rw [empiricalL2Seminorm_eq_euclideanNorm,
    empiricalL2Seminorm_eq_euclideanNorm,
    empiricalL2Seminorm_eq_euclideanNorm]
  have hadd :
      (WithLp.toLp 2
          (fun i : Fin n => (Real.sqrt n)⁻¹ * (f + g) (X i)) :
        EuclideanSpace ℝ (Fin n)) =
      WithLp.toLp 2 (fun i : Fin n => (Real.sqrt n)⁻¹ * f (X i)) +
        WithLp.toLp 2 (fun i : Fin n => (Real.sqrt n)⁻¹ * g (X i)) := by
    ext i
    simp [Pi.add_apply, mul_add]
  rw [hadd]
  exact norm_add_le _ _

theorem empiricalL2Dist_nonneg
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (f g : Ω → ℝ) :
    0 ≤ empiricalL2Dist n X f g := by
  exact empiricalL2Seminorm_nonneg n X (f - g)

@[simp] theorem empiricalL2Dist_self
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (f : Ω → ℝ) :
    empiricalL2Dist n X f f = 0 := by
  simp [empiricalL2Dist]

theorem empiricalL2Dist_symm
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (f g : Ω → ℝ) :
    empiricalL2Dist n X f g =
      empiricalL2Dist n X g f := by
  rw [empiricalL2Dist, empiricalL2Dist]
  have hsub : f - g = -(g - f) := by
    ext x
    simp
  rw [hsub, empiricalL2Seminorm_neg]

theorem empiricalL2Dist_triangle
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (f g h : Ω → ℝ) :
    empiricalL2Dist n X f h ≤
      empiricalL2Dist n X f g +
        empiricalL2Dist n X g h := by
  rw [empiricalL2Dist, empiricalL2Dist, empiricalL2Dist]
  have hsub : f - h = (f - g) + (g - h) := by
    ext x
    simp
  rw [hsub]
  exact empiricalL2Seminorm_add_le n X (f - g) (g - h)

theorem empiricalL2Seminorm_le_add_dist
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (f g : Ω → ℝ) :
    empiricalL2Seminorm n X g ≤
      empiricalL2Seminorm n X f +
        empiricalL2Dist n X f g := by
  have hg : g = f + -(f - g) := by
    ext x
    simp
  calc
    empiricalL2Seminorm n X g =
        empiricalL2Seminorm n X (f + -(f - g)) := congrArg _ hg
    _ ≤ empiricalL2Seminorm n X f +
        empiricalL2Seminorm n X (-(f - g)) :=
      empiricalL2Seminorm_add_le n X f (-(f - g))
    _ = empiricalL2Seminorm n X f +
        empiricalL2Seminorm n X (f - g) := by
      rw [empiricalL2Seminorm_neg]
    _ = empiricalL2Seminorm n X f +
        empiricalL2Dist n X f g := rfl

theorem exists_empirical_normalizedL2Cover_card_le_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} [NeZero n] (X : Fin n → Ω)
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (ε : ℝ)
    (hΦ : empiricalL2Seminorm n X Φ ≠ 0)
    (hU : uniformL2CoveringNumber F Φ ε ≠ ⊤) :
    ∃ S : Finset (Ω → ℝ),
      (∀ f ∈ F, ∃ g ∈ S,
        empiricalL2Dist n X f g <
          ε * empiricalL2Seminorm n X Φ) ∧
      (S.card : ℕ∞) ≤
        uniformL2CoveringNumber F Φ ε := by
  obtain ⟨Q, _, hQ⟩ :=
    FiniteDiscreteProbability.exists_empirical_adapter X
  have hQemp : ∀ h : Ω → ℝ,
      Q.l2Seminorm h = empiricalL2Seminorm n X h := by
    simpa [empiricalL2Seminorm] using hQ
  have hQΦ : Q.l2Seminorm Φ ≠ 0 := by
    rw [hQemp]
    exact hΦ
  obtain ⟨S, hcover, hcard⟩ :=
    exists_normalizedL2Cover_card_le_uniform Q F Φ ε hQΦ hU
  refine ⟨S, ?_, hcard⟩
  intro f hf
  obtain ⟨g, hg, hdist⟩ := hcover f hf
  refine ⟨g, hg, ?_⟩
  rw [finiteDiscrete_distL2_eq_empiricalL2Dist Q n X hQemp,
    hQemp] at hdist
  exact hdist

theorem empiricalL2Seminorm_le_relativeRadiusReal_mul
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω)
    (hΦ : IsEnvelope F Φ)
    (f : Ω → ℝ) (hf : f ∈ F) :
    empiricalL2Seminorm n X f ≤
      empiricalRelativeRadiusReal F Φ n X *
        empiricalL2Seminorm n X Φ := by
  by_cases hzero : empiricalL2Seminorm n X Φ = 0
  · have hfzero : empiricalL2Seminorm n X f = 0 :=
      le_antisymm
        ((empiricalL2Seminorm_le_envelope F Φ n X hΦ f hf).trans hzero.le)
        (empiricalL2Seminorm_nonneg n X f)
    simp [hzero, hfzero]
  · have hΦpos : 0 < empiricalL2Seminorm n X Φ :=
      lt_of_le_of_ne (empiricalL2Seminorm_nonneg n X Φ) (Ne.symm hzero)
    have hratio : ENNReal.ofReal
          (empiricalL2Seminorm n X f / empiricalL2Seminorm n X Φ) ≤
        empiricalRelativeRadius F Φ n X := by
      rw [empiricalRelativeRadius, if_neg hzero]
      exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)
    rw [← ofReal_empiricalRelativeRadiusReal_of_isEnvelope F Φ n X hΦ] at hratio
    have hratio_real :
        empiricalL2Seminorm n X f / empiricalL2Seminorm n X Φ ≤
          empiricalRelativeRadiusReal F Φ n X :=
      (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hratio
    exact (div_le_iff₀ hΦpos).mp hratio_real

theorem ofReal_empiricalL2Seminorm_mul_relativeRadiusReal_le_supNormOver
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) :
    ENNReal.ofReal (empiricalL2Seminorm n X Φ) *
        ENNReal.ofReal (empiricalRelativeRadiusReal F Φ n X) ≤
      supNormOver F (empiricalL2Seminorm n X) := by
  by_cases hD : empiricalL2Seminorm n X Φ = 0
  · simp [hD]
  · have hDpos : 0 < empiricalL2Seminorm n X Φ :=
      lt_of_le_of_ne (empiricalL2Seminorm_nonneg n X Φ) (Ne.symm hD)
    by_cases htop : empiricalRelativeRadius F Φ n X = ⊤
    · simp [empiricalRelativeRadiusReal, htop]
    · rw [empiricalRelativeRadiusReal,
        ENNReal.ofReal_toReal htop,
        empiricalRelativeRadius, if_neg hD]
      unfold supNormOver
      rw [ENNReal.mul_iSup]
      refine iSup_le fun f => ?_
      rw [ENNReal.mul_iSup]
      refine iSup_le fun hf => ?_
      refine le_iSup_of_le f (le_iSup_of_le hf ?_)
      rw [← ENNReal.ofReal_mul (empiricalL2Seminorm_nonneg n X Φ)]
      rw [mul_div_cancel₀ _ hD,
        abs_of_nonneg (empiricalL2Seminorm_nonneg n X f)]

theorem ofReal_empiricalL2Seminorm_mul_relativeRadiusReal_eq_supNormOver
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (hΦ : IsEnvelope F Φ) :
    ENNReal.ofReal (empiricalL2Seminorm n X Φ) *
        ENNReal.ofReal (empiricalRelativeRadiusReal F Φ n X) =
      supNormOver F (empiricalL2Seminorm n X) := by
  apply le_antisymm
  · exact ofReal_empiricalL2Seminorm_mul_relativeRadiusReal_le_supNormOver
      F Φ n X
  · unfold supNormOver
    refine iSup_le fun f => iSup_le fun hf => ?_
    rw [abs_of_nonneg (empiricalL2Seminorm_nonneg n X f)]
    calc
      ENNReal.ofReal (empiricalL2Seminorm n X f) ≤
          ENNReal.ofReal
            (empiricalRelativeRadiusReal F Φ n X *
              empiricalL2Seminorm n X Φ) :=
        ENNReal.ofReal_le_ofReal
          (empiricalL2Seminorm_le_relativeRadiusReal_mul
            F Φ n X hΦ f hf)
      _ = ENNReal.ofReal (empiricalRelativeRadiusReal F Φ n X) *
          ENNReal.ofReal (empiricalL2Seminorm n X Φ) := by
        rw [ENNReal.ofReal_mul
          (show 0 ≤ empiricalRelativeRadiusReal F Φ n X from
            ENNReal.toReal_nonneg)]
      _ = ENNReal.ofReal (empiricalL2Seminorm n X Φ) *
          ENNReal.ofReal (empiricalRelativeRadiusReal F Φ n X) := mul_comm _ _

theorem ofReal_sqrt_log_two_nat_le_sqrt_two_mul_entropyWeight
    (m : ℕ) (N : ℕ∞) (hmN : (m : ℕ∞) ≤ N) :
    ENNReal.ofReal
        (Real.sqrt (Real.log (2 * (m : ℝ)))) ≤
      ENNReal.ofReal (Real.sqrt 2) * entropyWeight N := by
  rcases eq_or_ne N ⊤ with rfl | hN
  · rw [entropyWeight_top,
      ENNReal.mul_top (by positivity : ENNReal.ofReal (Real.sqrt 2) ≠ 0)]
    exact le_top
  · obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hN
    have hmn : m ≤ n := by exact_mod_cast hmN
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · rw [entropyWeight_coe,
        ← ENNReal.ofReal_mul (Real.sqrt_nonneg 2),
        ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      apply ENNReal.ofReal_le_ofReal
      apply Real.sqrt_le_sqrt
      have hmpos : (0 : ℝ) < 2 * (m : ℝ) := by positivity
      have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hmnreal : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      have hbound : (2 : ℝ) * (m : ℝ) ≤ (1 + (n : ℝ)) ^ 2 := by
        nlinarith
      calc
        Real.log (2 * (m : ℝ)) ≤
            Real.log ((1 + (n : ℝ)) ^ 2) :=
          Real.log_le_log hmpos hbound
        _ = 2 * Real.log (1 + (n : ℝ)) := by
          rw [Real.log_pow]
          norm_num

theorem exists_empirical_usedAmbientCover_card_le_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} [NeZero n] (X : Fin n → Ω)
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (η : ℝ)
    (hD : empiricalL2Seminorm n X Φ ≠ 0)
    (hU : uniformL2CoveringNumber F Φ η ≠ ⊤) :
    ∃ S : Finset (Ω → ℝ),
      (∀ f ∈ F, ∃ g ∈ S,
        empiricalL2Dist n X f g <
          η * empiricalL2Seminorm n X Φ) ∧
      (∀ g ∈ S, ∃ f ∈ F,
        empiricalL2Dist n X f g <
          η * empiricalL2Seminorm n X Φ) ∧
      (S.card : ℕ∞) ≤ uniformL2CoveringNumber F Φ η := by
  classical
  obtain ⟨S, hcover, hcard⟩ :=
    exists_empirical_normalizedL2Cover_card_le_uniform X F Φ η hD hU
  let T := S.filter fun g => ∃ f ∈ F,
    empiricalL2Dist n X f g < η * empiricalL2Seminorm n X Φ
  refine ⟨T, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨g, hg, hdist⟩ := hcover f hf
    refine ⟨g, Finset.mem_filter.mpr ⟨hg, ⟨f, hf, hdist⟩⟩, hdist⟩
  · intro g hg
    exact (Finset.mem_filter.mp hg).2
  · calc
      (T.card : ℕ∞) ≤ (S.card : ℕ∞) := by
        exact_mod_cast Finset.card_filter_le S (fun g => ∃ f ∈ F,
          empiricalL2Dist n X f g < η * empiricalL2Seminorm n X Φ)
      _ ≤ uniformL2CoveringNumber F Φ η := hcard

theorem conditionalRademacherSup_finset_le_entropyWeight
    {Ω : Type*} (S : Finset (Ω → ℝ))
    (n : ℕ) (X : Fin n → Ω)
    (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ∞)
    (hSρ : ∀ f ∈ S, empiricalL2Seminorm n X f ≤ ρ)
    (hcard : (S.card : ℕ∞) ≤ N) :
    conditionalRademacherSup (S : Set (Ω → ℝ)) n X ≤
      2 * ENNReal.ofReal ρ * entropyWeight N := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · have hlog : 0 ≤ Real.log (2 * (S.card : ℝ)) := by
      apply Real.log_nonneg
      have hcard_one : (1 : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast hS.card_pos
      linarith
    have hsqrt :
        Real.sqrt (2 * ρ ^ 2 * Real.log (2 * (S.card : ℝ))) =
          ρ * (Real.sqrt 2 * Real.sqrt (Real.log (2 * (S.card : ℝ)))) := by
      rw [show 2 * ρ ^ 2 * Real.log (2 * (S.card : ℝ)) =
          ρ ^ 2 * (2 * Real.log (2 * (S.card : ℝ))) by ring,
        Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq_eq_abs,
        abs_of_pos hρ, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrt_two :
        ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal (Real.sqrt 2) = 2 := by
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg 2),
        ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    calc
      conditionalRademacherSup (S : Set (Ω → ℝ)) n X ≤
          ENNReal.ofReal
            (Real.sqrt
              (2 * ρ ^ 2 * Real.log (2 * (S.card : ℝ)))) :=
        conditionalRademacherSup_finset_le S n X ρ hρ hSρ
      _ = ENNReal.ofReal ρ *
          (ENNReal.ofReal (Real.sqrt 2) *
            ENNReal.ofReal (Real.sqrt (Real.log (2 * (S.card : ℝ))))) := by
        rw [hsqrt, ENNReal.ofReal_mul hρ.le,
          ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
      _ ≤ ENNReal.ofReal ρ *
          (ENNReal.ofReal (Real.sqrt 2) *
            (ENNReal.ofReal (Real.sqrt 2) * entropyWeight N)) := by
        gcongr
        exact ofReal_sqrt_log_two_nat_le_sqrt_two_mul_entropyWeight
          S.card N hcard
      _ = 2 * ENNReal.ofReal ρ * entropyWeight N := by
        calc
          ENNReal.ofReal ρ *
              (ENNReal.ofReal (Real.sqrt 2) *
                (ENNReal.ofReal (Real.sqrt 2) * entropyWeight N)) =
              ENNReal.ofReal ρ *
                (ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal (Real.sqrt 2)) *
                  entropyWeight N := by ac_rfl
          _ = 2 * ENNReal.ofReal ρ * entropyWeight N := by
            rw [hsqrt_two]
            ac_rfl

theorem empiricalL2Seminorm_center_lt
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (hΦ : IsEnvelope F Φ)
    (η : ℝ) (f : Ω → ℝ) (hf : f ∈ F)
    (g : Ω → ℝ)
    (hfg : empiricalL2Dist n X f g <
      η * empiricalL2Seminorm n X Φ) :
    empiricalL2Seminorm n X g <
      (empiricalRelativeRadiusReal F Φ n X + η) *
        empiricalL2Seminorm n X Φ := by
  calc
    empiricalL2Seminorm n X g ≤
        empiricalL2Seminorm n X f + empiricalL2Dist n X f g :=
      empiricalL2Seminorm_le_add_dist n X f g
    _ < empiricalRelativeRadiusReal F Φ n X *
          empiricalL2Seminorm n X Φ +
        η * empiricalL2Seminorm n X Φ :=
      add_lt_add_of_le_of_lt
        (empiricalL2Seminorm_le_relativeRadiusReal_mul F Φ n X hΦ f hf) hfg
    _ = (empiricalRelativeRadiusReal F Φ n X + η) *
        empiricalL2Seminorm n X Φ := by ring

theorem conditionalRademacherSup_usedAmbientCover_le
    {Ω : Type*} (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (hΦ : IsEnvelope F Φ)
    (S : Finset (Ω → ℝ)) (η : ℝ) (hη : 0 < η)
    (hD : empiricalL2Seminorm n X Φ ≠ 0)
    (hused : ∀ g ∈ S, ∃ f ∈ F,
      empiricalL2Dist n X f g <
        η * empiricalL2Seminorm n X Φ)
    (hcard : (S.card : ℕ∞) ≤
      uniformL2CoveringNumber F Φ η) :
    conditionalRademacherSup (S : Set (Ω → ℝ)) n X ≤
      2 * ENNReal.ofReal
          ((empiricalRelativeRadiusReal F Φ n X + η) *
            empiricalL2Seminorm n X Φ) *
        entropyWeight (uniformL2CoveringNumber F Φ η) := by
  have hDpos : 0 < empiricalL2Seminorm n X Φ :=
    lt_of_le_of_ne (empiricalL2Seminorm_nonneg n X Φ) (Ne.symm hD)
  have hρpos : 0 <
      (empiricalRelativeRadiusReal F Φ n X + η) *
        empiricalL2Seminorm n X Φ :=
    mul_pos (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hη) hDpos
  apply conditionalRademacherSup_finset_le_entropyWeight S n X _ hρpos _ _ hcard
  intro g hg
  obtain ⟨f, hf, hfg⟩ := hused g hg
  exact (empiricalL2Seminorm_center_lt F Φ n X hΦ η f hf g hfg).le

noncomputable def empiricalClosePairDifferences {Ω : Type*}
    (n : ℕ) (X : Fin n → Ω)
    (S T : Finset (Ω → ℝ)) (r : ℝ) : Finset (Ω → ℝ) :=
  by
    classical
    exact ((S ×ˢ T).filter
      (fun p => empiricalL2Dist n X p.1 p.2 < r)).image
        (fun p => p.1 - p.2)

theorem empiricalClosePairDifferences_card_le
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (S T : Finset (Ω → ℝ)) (r : ℝ) :
    ((empiricalClosePairDifferences n X S T r).card : ℕ∞) ≤
      (S.card : ℕ∞) * (T.card : ℕ∞) := by
  classical
  unfold empiricalClosePairDifferences
  calc
    ((((S ×ˢ T).filter
          (fun p => empiricalL2Dist n X p.1 p.2 < r)).image
        (fun p => p.1 - p.2)).card : ℕ∞) ≤
        (((S ×ˢ T).filter
          (fun p => empiricalL2Dist n X p.1 p.2 < r)).card : ℕ∞) := by
      exact_mod_cast Finset.card_image_le
    _ ≤ ((S ×ˢ T).card : ℕ∞) := by
      exact_mod_cast Finset.card_filter_le (S ×ˢ T)
        (fun p => empiricalL2Dist n X p.1 p.2 < r)
    _ = (S.card : ℕ∞) * (T.card : ℕ∞) := by
      rw [Finset.card_product]
      norm_cast

theorem exists_sub_mem_empiricalClosePairDifferences_of_covers
    {Ω : Type*} (F : Set (Ω → ℝ))
    (n : ℕ) (X : Fin n → Ω)
    (S T : Finset (Ω → ℝ)) (r s : ℝ)
    (hS : ∀ f ∈ F, ∃ g ∈ S, empiricalL2Dist n X f g < r)
    (hT : ∀ f ∈ F, ∃ g ∈ T, empiricalL2Dist n X f g < s)
    (f : Ω → ℝ) (hf : f ∈ F) :
    ∃ g ∈ S, ∃ h ∈ T,
      g - h ∈ empiricalClosePairDifferences n X S T (r + s) := by
  classical
  obtain ⟨g, hgS, hfg⟩ := hS f hf
  obtain ⟨h, hhT, hfh⟩ := hT f hf
  refine ⟨g, hgS, h, hhT, ?_⟩
  unfold empiricalClosePairDifferences
  apply Finset.mem_image.mpr
  refine ⟨(g, h), Finset.mem_filter.mpr
    ⟨Finset.mk_mem_product hgS hhT, ?_⟩, rfl⟩
  calc
    empiricalL2Dist n X g h ≤
        empiricalL2Dist n X g f + empiricalL2Dist n X f h :=
      empiricalL2Dist_triangle n X g f h
    _ = empiricalL2Dist n X f g + empiricalL2Dist n X f h := by
      rw [empiricalL2Dist_symm n X g f]
    _ < r + s := add_lt_add hfg hfh

theorem conditionalRademacherSup_closePairDifferences_le
    {Ω : Type*} (n : ℕ) (X : Fin n → Ω)
    (S T : Finset (Ω → ℝ)) (r : ℝ) (hr : 0 < r)
    (N M : ℕ∞)
    (hS : (S.card : ℕ∞) ≤ N)
    (hT : (T.card : ℕ∞) ≤ M) :
    conditionalRademacherSup
        (empiricalClosePairDifferences n X S T r : Set (Ω → ℝ)) n X ≤
      2 * ENNReal.ofReal r * entropyWeight (N * M) := by
  classical
  apply conditionalRademacherSup_finset_le_entropyWeight
    (empiricalClosePairDifferences n X S T r) n X r hr (N * M)
  · intro u hu
    unfold empiricalClosePairDifferences at hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    exact (Finset.mem_filter.mp hp).2.le
  · exact (empiricalClosePairDifferences_card_le n X S T r).trans
      (mul_le_mul' hS hT)

noncomputable def empiricalDyadicRadius {Ω : Type*}
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (q : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ q * empiricalRelativeRadiusReal F Φ n X

@[simp] theorem empiricalDyadicRadius_zero {Ω : Type*}
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) :
    empiricalDyadicRadius F Φ n X 0 =
      empiricalRelativeRadiusReal F Φ n X := by
  simp [empiricalDyadicRadius]

theorem empiricalDyadicRadius_nonneg {Ω : Type*}
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (q : ℕ) :
    0 ≤ empiricalDyadicRadius F Φ n X q := by
  exact mul_nonneg (by positivity) ENNReal.toReal_nonneg

structure FiniteEmpiricalDyadicNets {Ω : Type*}
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (n : ℕ) (X : Fin n → Ω) (L : ℕ) where
  net : ℕ → Finset (Ω → ℝ)
  proj : ℕ → F → Ω → ℝ
  proj_mem :
    ∀ (q : ℕ), q ≤ L → ∀ f : F, proj q f ∈ net q
  proj_dist_lt :
    ∀ (q : ℕ), q ≤ L → ∀ f : F,
      empiricalL2Dist n X f (proj q f) <
        empiricalDyadicRadius F Φ n X q *
          empiricalL2Seminorm n X Φ
  net_used :
    ∀ (q : ℕ), q ≤ L → ∀ g ∈ net q, ∃ f : F,
      empiricalL2Dist n X f g <
        empiricalDyadicRadius F Φ n X q *
          empiricalL2Seminorm n X Φ
  card_le :
    ∀ (q : ℕ), q ≤ L →
      ((net q).card : ℕ∞) ≤
        uniformL2CoveringNumber F Φ
          (empiricalDyadicRadius F Φ n X q)

theorem finiteEmpiricalDyadicNets_nonempty
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} [NeZero n] (X : Fin n → Ω)
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (L : ℕ)
    (hD : empiricalL2Seminorm n X Φ ≠ 0)
    (hU : ∀ (q : ℕ), q ≤ L →
      uniformL2CoveringNumber F Φ
        (empiricalDyadicRadius F Φ n X q) ≠ ⊤) :
    Nonempty (FiniteEmpiricalDyadicNets F Φ n X L) := by
  classical
  have hnet : ∀ q : {q : ℕ // q ≤ L}, ∃ S : Finset (Ω → ℝ),
      (∀ f ∈ F, ∃ g ∈ S,
        empiricalL2Dist n X f g <
          empiricalDyadicRadius F Φ n X q * empiricalL2Seminorm n X Φ) ∧
      (∀ g ∈ S, ∃ f ∈ F,
        empiricalL2Dist n X f g <
          empiricalDyadicRadius F Φ n X q * empiricalL2Seminorm n X Φ) ∧
      (S.card : ℕ∞) ≤ uniformL2CoveringNumber F Φ
        (empiricalDyadicRadius F Φ n X q) := by
    intro q
    exact exists_empirical_usedAmbientCover_card_le_uniform X F Φ
      (empiricalDyadicRadius F Φ n X q) hD (hU q q.property)
  choose net hcover hused hcard using hnet
  have hproj : ∀ q : {q : ℕ // q ≤ L}, ∀ f : F,
      ∃ g ∈ net q,
        empiricalL2Dist n X f g <
          empiricalDyadicRadius F Φ n X q * empiricalL2Seminorm n X Φ := by
    intro q f
    exact hcover q f f.property
  choose proj hproj_mem hproj_dist using hproj
  let net' : ℕ → Finset (Ω → ℝ) := fun q =>
    if hq : q ≤ L then net ⟨q, hq⟩ else ∅
  let proj' : ℕ → F → Ω → ℝ := fun q f =>
    if hq : q ≤ L then proj ⟨q, hq⟩ f else f
  refine ⟨{
    net := net'
    proj := proj'
    proj_mem := ?_
    proj_dist_lt := ?_
    net_used := ?_
    card_le := ?_ }⟩
  · intro q hq f
    simp only [net', proj', dif_pos hq]
    exact hproj_mem ⟨q, hq⟩ f
  · intro q hq f
    simp only [proj', dif_pos hq]
    exact hproj_dist ⟨q, hq⟩ f
  · intro q hq g hg
    simp only [net', dif_pos hq] at hg
    obtain ⟨f, hf, hfg⟩ := hused ⟨q, hq⟩ g hg
    exact ⟨⟨f, hf⟩, hfg⟩
  · intro q hq
    simp only [net', dif_pos hq]
    exact hcard ⟨q, hq⟩

namespace FiniteEmpiricalDyadicNets

def head {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L)
    (f : F) : Ω → ℝ :=
  B.proj 0 f

def link {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L)
    (q : ℕ) (f : F) : Ω → ℝ :=
  B.proj (q + 1) f - B.proj q f

theorem head_mem {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L) (f : F) :
    B.head f ∈ B.net 0 := by
  exact B.proj_mem 0 (Nat.zero_le L) f

theorem link_mem_closePairDifferences
    {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L)
    (q : ℕ) (hq : q + 1 ≤ L) (f : F) :
    B.link q f ∈
      empiricalClosePairDifferences n X
        (B.net (q + 1)) (B.net q)
        ((empiricalDyadicRadius F Φ n X (q + 1) +
            empiricalDyadicRadius F Φ n X q) *
          empiricalL2Seminorm n X Φ) := by
  classical
  unfold link empiricalClosePairDifferences
  apply Finset.mem_image.mpr
  refine ⟨(B.proj (q + 1) f, B.proj q f),
    Finset.mem_filter.mpr ⟨Finset.mk_mem_product
      (B.proj_mem (q + 1) hq f)
      (B.proj_mem q (by omega) f), ?_⟩, rfl⟩
  calc
    empiricalL2Dist n X (B.proj (q + 1) f) (B.proj q f) ≤
        empiricalL2Dist n X (B.proj (q + 1) f) f +
          empiricalL2Dist n X f (B.proj q f) :=
      empiricalL2Dist_triangle n X (B.proj (q + 1) f) f (B.proj q f)
    _ = empiricalL2Dist n X f (B.proj (q + 1) f) +
          empiricalL2Dist n X f (B.proj q f) := by
      rw [empiricalL2Dist_symm n X (B.proj (q + 1) f) f]
    _ < empiricalDyadicRadius F Φ n X (q + 1) *
          empiricalL2Seminorm n X Φ +
        empiricalDyadicRadius F Φ n X q *
          empiricalL2Seminorm n X Φ :=
      add_lt_add (B.proj_dist_lt (q + 1) hq f)
        (B.proj_dist_lt q (by omega) f)
    _ = (empiricalDyadicRadius F Φ n X (q + 1) +
          empiricalDyadicRadius F Φ n X q) *
        empiricalL2Seminorm n X Φ := by ring

theorem rademacherAverage_proj_eq_head_add_sum_links
    {Ω : Type*} {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    {n L : ℕ} {X : Fin n → Ω}
    (B : FiniteEmpiricalDyadicNets F Φ n X L)
    (ε : Fin n → Bool) (f : F) :
    rademacherAverage n X ε (B.proj L f) =
      rademacherAverage n X ε (B.head f) +
        ∑ q ∈ Finset.range L,
          rademacherAverage n X ε (B.link q f) := by
  unfold head link
  simp_rw [rademacherAverage_sub]
  have hsum := Finset.sum_range_sub
    (fun q => rademacherAverage n X ε (B.proj q f)) L
  rw [hsum]
  ring

end FiniteEmpiricalDyadicNets

end AsymptoticStatistics.EmpiricalProcess
