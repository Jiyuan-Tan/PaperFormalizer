module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCovering
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringRademacher
public import StatLean.AsymptoticStatistics.ForMathlib.AntitoneLintegral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Count
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-!
# Book uniform covering entropy definitions

This file records the all-probability-measure definition layer for the uniform
covering entropy used by van der Vaart on p.274.  It is separate from the
finite-discrete definitions and makes no theorem-level claim.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

namespace FiniteDiscreteProbability

/-- The probability-measure subtype associated with a finite-discrete law.
Its probability property follows from the finite-discrete construction. -/
noncomputable def toProbabilityMeasure
    (Q : FiniteDiscreteProbability Ω) : ProbabilityMeasure Ω :=
  ⟨Q.measure, Q.measure_isProbability⟩

end FiniteDiscreteProbability

/-- The book-layer normalized `L²(Q)` covering number for one probability
measure, with measurable square-integrable ambient centers.

The radius is `ε ‖Φ‖_{Q,2}`.  Edge behavior: a zero envelope seminorm is
totalized to covering number `1`; otherwise the infimum is `⊤` when no
admissible finite ambient cover exists. -/
noncomputable def allProbabilityNormalizedL2CoveringNumber
    (Q : ProbabilityMeasure Ω) (F : Set (Ω → ℝ))
    (Φ : Ω → ℝ) (ε : ℝ) : ℕ∞ :=
  if eLpNorm Φ 2 (Q : Measure Ω) = 0 then 1 else
    ⨅ (S : Finset (Ω → ℝ))
      (_ : (∀ g ∈ S,
          Measurable g ∧ MemLp g 2 (Q : Measure Ω)) ∧
        ∀ f ∈ F, ∃ g ∈ S,
          eLpNorm (f - g) 2 (Q : Measure Ω) <
            ENNReal.ofReal ε * eLpNorm Φ 2 (Q : Measure Ω)),
      (S.card : ℕ∞)

/-- The book-layer uniform normalized covering number, taking the supremum
over all probability measures.  Its zero-denominator behavior is inherited
pointwise from `allProbabilityNormalizedL2CoveringNumber`. -/
noncomputable def allProbabilityUniformL2CoveringNumber
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (ε : ℝ) : ℕ∞ :=
  ⨆ Q : ProbabilityMeasure Ω,
    allProbabilityNormalizedL2CoveringNumber Q F Φ ε

/-- The book-layer unregularized weight `√(log N)` on extended natural
covering numbers.  Edge behavior: finite `0` and `1` have weight zero, while
an infinite covering number has weight `⊤`. -/
noncomputable def bookEntropyWeight (N : ℕ∞) : ℝ≥0∞ :=
  ENat.recTopCoe (⊤ : ℝ≥0∞)
    (fun n : ℕ => ENNReal.ofReal (Real.sqrt (Real.log (n : ℝ)))) N

@[simp] theorem bookEntropyWeight_top : bookEntropyWeight ⊤ = ⊤ := rfl

@[simp] theorem bookEntropyWeight_coe (n : ℕ) :
    bookEntropyWeight (n : ℕ∞) = ENNReal.ofReal (Real.sqrt (Real.log (n : ℝ))) := rfl

@[simp] theorem bookEntropyWeight_zero : bookEntropyWeight 0 = 0 := by
  simp [bookEntropyWeight]

@[simp] theorem bookEntropyWeight_one : bookEntropyWeight 1 = 0 := by
  simp [bookEntropyWeight]

/-- The all-probability covering entropy integral with regularized weight
`√(log (1+N))`.

Edge behavior is inherited from the `ENNReal` lintegral: a nonpositive upper
endpoint gives an empty interval, and an infinite integrand remains visible. -/
noncomputable def allProbabilityUniformCoveringEntropyIntegralRegularized
    (δ : ℝ) (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ε in Set.Ioc 0 δ,
    entropyWeight (allProbabilityUniformL2CoveringNumber F Φ ε) ∂volume

/-- The book-layer all-probability uniform covering entropy integral using
the unregularized weight `√(log N)`.

Edge behavior is total: a nonpositive upper endpoint gives an empty interval;
finite cover counts `0` and `1` contribute zero, while `⊤` has weight `⊤`.
This is a definition only, not a claim that a book theorem has been proved. -/
noncomputable def bookUniformCoveringEntropyIntegral
    (δ : ℝ) (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ε in Set.Ioc 0 δ,
    bookEntropyWeight (allProbabilityUniformL2CoveringNumber F Φ ε) ∂volume

/-- The explicit zero-denominator totalization in the book definition layer. -/
@[simp] theorem allProbabilityNormalizedL2CoveringNumber_of_eLpNorm_eq_zero
    (Q : ProbabilityMeasure Ω) (F : Set (Ω → ℝ))
    (Φ : Ω → ℝ) (ε : ℝ)
    (hΦ : eLpNorm Φ 2 (Q : Measure Ω) = 0) :
    allProbabilityNormalizedL2CoveringNumber Q F Φ ε = 1 := by
  simp [allProbabilityNormalizedL2CoveringNumber, hΦ]

namespace FiniteDiscreteProbability

/-- The measure realization of a finite-discrete law has the same `L²`
seminorm as its defining finite weighted sum. -/
theorem eLpNorm_toProbabilityMeasure_eq_l2Seminorm
    (Q : FiniteDiscreteProbability Ω) (f : Ω → ℝ)
    (hf : Measurable f) :
    eLpNorm f 2 (Q.toProbabilityMeasure : Measure Ω) =
      ENNReal.ofReal (Q.l2Seminorm f) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, one_div]
  change
    (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂Q.measure) ^ (2 : ℝ)⁻¹ =
      ENNReal.ofReal (Real.sqrt
        (∑ i, (Q.weight i : ℝ) * |f (Q.atom i)| ^ 2))
  rw [FiniteDiscreteProbability.measure, lintegral_finset_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]
  have hmeas : Measurable (fun x => ‖f x‖ₑ ^ (2 : ℝ)) :=
    hf.enorm.pow_const _
  simp_rw [lintegral_dirac' _ hmeas]
  have hterm (i : Fin Q.atomCount) :
      (Q.weight i : ℝ≥0∞) * ‖f (Q.atom i)‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal ((Q.weight i : ℝ) * |f (Q.atom i)| ^ 2) := by
    rw [Real.enorm_eq_ofReal_abs]
    norm_num [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow,
      ENNReal.ofReal_mul]
  rw [show (∑ i, (Q.weight i : ℝ≥0∞) * ‖f (Q.atom i)‖ₑ ^ (2 : ℝ)) =
      ENNReal.ofReal (∑ i, (Q.weight i : ℝ) * |f (Q.atom i)| ^ 2) by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · exact Finset.sum_congr rfl (fun i _ => hterm i)
    · intro i _
      positivity]
  have hsum : 0 ≤ ∑ i, (Q.weight i : ℝ) * |f (Q.atom i)| ^ 2 := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (sq_nonneg _)
  rw [Real.sqrt_eq_rpow]
  rw [ENNReal.ofReal_rpow_of_nonneg hsum (by norm_num)]
  norm_num

end FiniteDiscreteProbability

/-- Every book-layer cover for the realized finite-discrete law is a finite-discrete
cover after forgetting its extra measurable-`MemLp` center guarantees. -/
theorem normalizedL2CoveringNumber_le_allProbabilityNormalizedL2CoveringNumber
    (Q : FiniteDiscreteProbability Ω)
    (F : Set (Ω → ℝ))
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    normalizedL2CoveringNumber Q F Φ ε ≤
      allProbabilityNormalizedL2CoveringNumber
        Q.toProbabilityMeasure F Φ ε := by
  have hΦeq :=
    FiniteDiscreteProbability.eLpNorm_toProbabilityMeasure_eq_l2Seminorm
      Q Φ hΦ_meas
  by_cases hΦ : Q.l2Seminorm Φ = 0
  · simp [normalizedL2CoveringNumber, allProbabilityNormalizedL2CoveringNumber,
      hΦ, hΦeq]
  · have hΦe :
        eLpNorm Φ 2 (Q.toProbabilityMeasure : Measure Ω) ≠ 0 := by
      rw [hΦeq]
      exact ENNReal.ofReal_ne_zero_iff.mpr
        (lt_of_le_of_ne
          (FiniteDiscreteProbability.l2Seminorm_nonneg Q Φ) (Ne.symm hΦ))
    simp only [normalizedL2CoveringNumber, if_neg hΦ,
      allProbabilityNormalizedL2CoveringNumber, if_neg hΦe]
    refine le_iInf fun S => le_iInf fun hS => ?_
    refine iInf_le_of_le S (iInf_le_of_le ?_ le_rfl)
    intro f hf
    obtain ⟨g, hgS, hfg⟩ := hS.2 f hf
    refine ⟨g, hgS, ?_⟩
    have hdiff :=
      FiniteDiscreteProbability.eLpNorm_toProbabilityMeasure_eq_l2Seminorm
        Q (f - g) ((hF_meas f hf).sub (hS.1 g hgS).1)
    rw [hdiff, hΦeq, ← ENNReal.ofReal_mul hε] at hfg
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (FiniteDiscreteProbability.l2Seminorm_nonneg Q (f - g))).mp hfg

/-- The finite-discrete uniform cover is bounded by the book-layer supremum
over all probability measures. -/
theorem uniformL2CoveringNumber_le_allProbabilityUniformL2CoveringNumber
    (F : Set (Ω → ℝ))
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    uniformL2CoveringNumber F Φ ε ≤
      allProbabilityUniformL2CoveringNumber F Φ ε := by
  unfold uniformL2CoveringNumber allProbabilityUniformL2CoveringNumber
  refine iSup_le fun Q => ?_
  exact
    (normalizedL2CoveringNumber_le_allProbabilityNormalizedL2CoveringNumber
      Q F hF_meas Φ hΦ_meas hε).trans
      (le_iSup (fun Q' : ProbabilityMeasure Ω =>
        allProbabilityNormalizedL2CoveringNumber Q' F Φ ε)
        Q.toProbabilityMeasure)

/-- The finite-discrete regularized entropy integral is bounded by its
all-probability-measure counterpart. -/
theorem uniformCoveringEntropyIntegral_le_allProbabilityRegularized
    (F : Set (Ω → ℝ))
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ)
    (δ : ℝ) :
    uniformCoveringEntropyIntegral δ F Φ ≤
      allProbabilityUniformCoveringEntropyIntegralRegularized δ F Φ := by
  unfold uniformCoveringEntropyIntegral
    allProbabilityUniformCoveringEntropyIntegralRegularized
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with ε hε
  exact entropyWeight_mono
    (uniformL2CoveringNumber_le_allProbabilityUniformL2CoveringNumber
      F hF_meas Φ hΦ_meas hε.1.le)

/-- The book entropy weight is monotone in the extended covering number. -/
theorem bookEntropyWeight_mono {N M : ℕ∞} (hNM : N ≤ M) :
    bookEntropyWeight N ≤ bookEntropyWeight M := by
  rcases eq_or_ne M ⊤ with rfl | hM
  · simp
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hM
  have hN : N ≠ ⊤ := ne_top_of_le_ne_top hM hNM
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hN
  by_cases hn : n = 0
  · subst n
    simp
  rw [bookEntropyWeight_coe, bookEntropyWeight_coe]
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  apply Real.log_le_log
  · exact_mod_cast Nat.pos_of_ne_zero hn
  · exact_mod_cast hNM

/-- Increasing the normalized radius can only decrease the covering number
for a fixed probability measure. -/
theorem allProbabilityNormalizedL2CoveringNumber_antitone_eps
    (Q : ProbabilityMeasure Ω) (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    allProbabilityNormalizedL2CoveringNumber Q F Φ ε₂ ≤
      allProbabilityNormalizedL2CoveringNumber Q F Φ ε₁ := by
  by_cases hΦ : eLpNorm Φ 2 (Q : Measure Ω) = 0
  · simp [allProbabilityNormalizedL2CoveringNumber, hΦ]
  · simp only [allProbabilityNormalizedL2CoveringNumber, if_neg hΦ]
    refine le_iInf fun S => le_iInf fun hS => ?_
    refine iInf_le_of_le S (iInf_le_of_le ?_ le_rfl)
    refine ⟨hS.1, fun f hf => ?_⟩
    obtain ⟨g, hgS, hfg⟩ := hS.2 f hf
    refine ⟨g, hgS, hfg.trans_le ?_⟩
    exact mul_le_mul_left (ENNReal.ofReal_mono hε) _

/-- Increasing the normalized radius can only decrease the all-probability
uniform covering number. -/
theorem allProbabilityUniformL2CoveringNumber_antitone_eps
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    allProbabilityUniformL2CoveringNumber F Φ ε₂ ≤
      allProbabilityUniformL2CoveringNumber F Φ ε₁ := by
  unfold allProbabilityUniformL2CoveringNumber
  refine iSup_le fun Q => ?_
  exact (allProbabilityNormalizedL2CoveringNumber_antitone_eps
    Q F Φ hε).trans (le_iSup (fun Q' : ProbabilityMeasure Ω =>
      allProbabilityNormalizedL2CoveringNumber Q' F Φ ε₁) Q)

/-- The book entropy integrand is antitone in its radius argument. -/
theorem bookUniformCoveringEntropyIntegrand_antitone_eps
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    bookEntropyWeight (allProbabilityUniformL2CoveringNumber F Φ ε₂) ≤
      bookEntropyWeight (allProbabilityUniformL2CoveringNumber F Φ ε₁) := by
  exact bookEntropyWeight_mono
    (allProbabilityUniformL2CoveringNumber_antitone_eps F Φ hε)

/-- A book entropy integral at any radius is controlled by its initial segment
and a proportional copy of that segment. -/
theorem bookUniformCoveringEntropyIntegral_le_initial_add_ratio_mul_initial
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    {a t : ℝ} (ha : 0 < a) :
    bookUniformCoveringEntropyIntegral t F Φ ≤
      bookUniformCoveringEntropyIntegral a F Φ +
        ENNReal.ofReal (t / a) * bookUniformCoveringEntropyIntegral a F Φ := by
  unfold bookUniformCoveringEntropyIntegral
  exact ForMathlib.setLIntegral_Ioc_le_initial_add_ratio_mul_initial_of_antitone
    (fun ε => bookEntropyWeight
      (allProbabilityUniformL2CoveringNumber F Φ ε))
    (fun _ _ hε => bookUniformCoveringEntropyIntegrand_antitone_eps F Φ hε) ha

/-- The regularized entropy weight costs at most the fixed `√(log 2)` head
term beyond the book weight. -/
theorem entropyWeight_le_sqrtLogTwo_add_bookEntropyWeight
    (N : ℕ∞) :
    entropyWeight N ≤
      ENNReal.ofReal (Real.sqrt (Real.log 2)) +
        bookEntropyWeight N := by
  rcases eq_or_ne N ⊤ with rfl | hN
  · simp
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hN
  by_cases hn : n = 0
  · subst n
    rw [entropyWeight_coe, bookEntropyWeight_coe]
    norm_num
  rw [entropyWeight_coe, bookEntropyWeight_coe,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  calc
    Real.sqrt (Real.log (1 + (n : ℝ))) ≤
        Real.sqrt (Real.log ((2 : ℝ) * n)) := by
      apply Real.sqrt_le_sqrt
      apply Real.log_le_log
      · positivity
      · nlinarith
    _ = Real.sqrt (Real.log 2 + Real.log (n : ℝ)) := by
      rw [Real.log_mul (by norm_num) hnpos.ne']
    _ ≤ Real.sqrt (Real.log 2) + Real.sqrt (Real.log (n : ℝ)) :=
      ForMathlib.Real.sqrt_add_le (Real.log_nonneg (by norm_num)) hlogn

/-- The regularized all-probability entropy integral is bounded by the book
integral plus the integrated `√(log 2)` head term. -/
theorem allProbabilityRegularizedEntropyIntegral_le_head_add_book
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    allProbabilityUniformCoveringEntropyIntegralRegularized δ F Φ ≤
      ENNReal.ofReal δ *
          ENNReal.ofReal (Real.sqrt (Real.log 2)) +
        bookUniformCoveringEntropyIntegral δ F Φ := by
  unfold allProbabilityUniformCoveringEntropyIntegralRegularized
    bookUniformCoveringEntropyIntegral
  calc
    (∫⁻ ε in Set.Ioc 0 δ,
        entropyWeight (allProbabilityUniformL2CoveringNumber F Φ ε) ∂volume) ≤
        ∫⁻ ε in Set.Ioc 0 δ,
          (ENNReal.ofReal (Real.sqrt (Real.log 2)) +
            bookEntropyWeight
              (allProbabilityUniformL2CoveringNumber F Φ ε)) ∂volume := by
      exact lintegral_mono fun ε =>
        entropyWeight_le_sqrtLogTwo_add_bookEntropyWeight _
    _ = (∫⁻ _ in Set.Ioc 0 δ,
            ENNReal.ofReal (Real.sqrt (Real.log 2)) ∂volume) +
          ∫⁻ ε in Set.Ioc 0 δ,
            bookEntropyWeight
              (allProbabilityUniformL2CoveringNumber F Φ ε) ∂volume := by
      rw [lintegral_add_left measurable_const]
    _ = ENNReal.ofReal δ *
          ENNReal.ofReal (Real.sqrt (Real.log 2)) +
        ∫⁻ ε in Set.Ioc 0 δ,
          bookEntropyWeight
            (allProbabilityUniformL2CoveringNumber F Φ ε) ∂volume := by
      rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
        ← ENNReal.toReal_ofReal hδ, ENNReal.ofReal_toReal]
      · rw [mul_comm]
      · exact ENNReal.ofReal_ne_top

/-- The book entropy integral is monotone in its upper endpoint. -/
theorem bookUniformCoveringEntropyIntegral_mono_delta
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) :
    bookUniformCoveringEntropyIntegral δ₁ F Φ ≤
      bookUniformCoveringEntropyIntegral δ₂ F Φ := by
  unfold bookUniformCoveringEntropyIntegral
  apply lintegral_mono'
  · apply Measure.restrict_mono
    · intro x hx
      exact ⟨hx.1, hx.2.trans hδ⟩
    · exact le_rfl
  · exact le_rfl

/-- For an anchored class, the fixed `√(log 2)` head term at the empirical
radius is absorbed by twice the book entropy integral. -/
theorem empiricalRadius_head_le_two_mul_bookEntropyIntegral
    (F : Set (Ω → ℝ))
    (hzero : (fun _ : Ω => 0) ∈ F)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ)
    (n : ℕ) (x : Fin n → Ω) :
    ENNReal.ofReal (empiricalRelativeRadiusReal F Φ n x) *
        ENNReal.ofReal (Real.sqrt (Real.log 2)) ≤
      2 * bookUniformCoveringEntropyIntegral
        (empiricalRelativeRadiusReal F Φ n x) F Φ := by
  let θ := empiricalRelativeRadiusReal F Φ n x
  let D := empiricalL2Seminorm n x Φ
  have hθnonneg : 0 ≤ θ := ENNReal.toReal_nonneg
  by_cases hθzero : θ = 0
  · change ENNReal.ofReal θ * _ ≤
      2 * bookUniformCoveringEntropyIntegral θ F Φ
    simp [hθzero, bookUniformCoveringEntropyIntegral]
  have hθpos : 0 < θ := lt_of_le_of_ne hθnonneg (Ne.symm hθzero)
  have hn : n ≠ 0 := by
    intro hn
    subst n
    exact hθzero (empiricalRelativeRadiusReal_zero F Φ x)
  letI : NeZero n := ⟨hn⟩
  have hD : D ≠ 0 := by
    intro hD
    exact hθzero
      (empiricalRelativeRadiusReal_of_empiricalL2Seminorm_eq_zero
        F Φ n x hD)
  have hDpos : 0 < D :=
    lt_of_le_of_ne (empiricalL2Seminorm_nonneg n x Φ) (Ne.symm hD)
  obtain ⟨Q, _, hQ⟩ :=
    FiniteDiscreteProbability.exists_empirical_adapter x
  have hQemp : ∀ f : Ω → ℝ,
      Q.l2Seminorm f = empiricalL2Seminorm n x f := by
    simpa [empiricalL2Seminorm] using hQ
  have hQΦ : Q.l2Seminorm Φ ≠ 0 := by
    rw [hQemp]
    exact hD
  have hRadius_pos :
      0 < (empiricalRelativeRadius F Φ n x).toReal := by
    simpa [θ, empiricalRelativeRadiusReal] using hθpos
  have hRadius_ne_top : empiricalRelativeRadius F Φ n x ≠ ⊤ :=
    (ENNReal.toReal_pos_iff.mp hRadius_pos).2.ne
  have hRadius_eq :
      ENNReal.ofReal θ = empiricalRelativeRadius F Φ n x := by
    change ENNReal.ofReal (empiricalRelativeRadius F Φ n x).toReal = _
    exact ENNReal.ofReal_toReal hRadius_ne_top
  have hcover_two : ∀ ε ∈ Set.Ioo (0 : ℝ) (θ / 2),
      (2 : ℕ∞) ≤ allProbabilityUniformL2CoveringNumber F Φ ε := by
    intro ε hε
    rcases hε with ⟨hεpos, hεhalf⟩
    have h2εθ : 2 * ε < θ := by linarith
    have hlt_radius :
        ENNReal.ofReal (2 * ε) < empiricalRelativeRadius F Φ n x := by
      rw [← hRadius_eq]
      exact (ENNReal.ofReal_lt_ofReal_iff hθpos).2 h2εθ
    rw [empiricalRelativeRadius, if_neg hD, lt_iSup_iff] at hlt_radius
    obtain ⟨f, hf⟩ := hlt_radius
    rw [lt_iSup_iff] at hf
    obtain ⟨hfF, hfratio_enorm⟩ := hf
    have hfratio : 2 * ε < empiricalL2Seminorm n x f / D :=
      (ENNReal.ofReal_lt_ofReal_iff'.mp hfratio_enorm).1
    have hlarge : 2 * ε * D < empiricalL2Seminorm n x f :=
      (lt_div_iff₀ hDpos).mp hfratio
    have hfinite :
        (2 : ℕ∞) ≤ normalizedL2CoveringNumber Q F Φ ε := by
      simp only [normalizedL2CoveringNumber, if_neg hQΦ]
      refine le_iInf fun S => le_iInf fun hS => ?_
      obtain ⟨g₀, hg₀S, h0g₀⟩ := hS (0 : Ω → ℝ) hzero
      obtain ⟨gf, hgfS, hfgf⟩ := hS f hfF
      rw [finiteDiscrete_distL2_eq_empiricalL2Dist Q n x hQemp,
        hQemp] at h0g₀ hfgf
      have hgf_ne : gf ≠ g₀ := by
        intro hgf
        subst gf
        have htri := empiricalL2Dist_triangle n x f g₀ (0 : Ω → ℝ)
        have hdist_lt :
            empiricalL2Dist n x f (0 : Ω → ℝ) <
              ε * D + ε * D := by
          refine htri.trans_lt (add_lt_add hfgf ?_)
          rw [empiricalL2Dist_symm]
          exact h0g₀
        have hnorm_lt :
            empiricalL2Seminorm n x f < ε * D + ε * D := by
          simpa [empiricalL2Dist] using hdist_lt
        nlinarith
      have hcard : 1 < S.card :=
        Finset.one_lt_card.mpr ⟨gf, hgfS, g₀, hg₀S, hgf_ne⟩
      exact_mod_cast hcard
    exact hfinite.trans
      ((normalizedL2CoveringNumber_le_uniform Q F Φ ε).trans
        (uniformL2CoveringNumber_le_allProbabilityUniformL2CoveringNumber
          F hF_meas Φ hΦ_meas hεpos.le))
  have hweight : ∀ ε ∈ Set.Ioo (0 : ℝ) (θ / 2),
      ENNReal.ofReal (Real.sqrt (Real.log 2)) ≤
        bookEntropyWeight (allProbabilityUniformL2CoveringNumber F Φ ε) := by
    intro ε hε
    simpa only [bookEntropyWeight_coe] using!
      bookEntropyWeight_mono (hcover_two ε hε)
  have hhalf_subset : Set.Ioo (0 : ℝ) (θ / 2) ⊆ Set.Ioc 0 θ := by
    intro ε hε
    exact ⟨hε.1, (hε.2.trans (by linarith)).le⟩
  have hconst :
      (∫⁻ _ in Set.Ioo (0 : ℝ) (θ / 2),
          ENNReal.ofReal (Real.sqrt (Real.log 2)) ∂volume) ≤
        bookUniformCoveringEntropyIntegral θ F Φ := by
    unfold bookUniformCoveringEntropyIntegral
    calc
      (∫⁻ _ in Set.Ioo (0 : ℝ) (θ / 2),
          ENNReal.ofReal (Real.sqrt (Real.log 2)) ∂volume) ≤
          ∫⁻ ε in Set.Ioo (0 : ℝ) (θ / 2),
            bookEntropyWeight
              (allProbabilityUniformL2CoveringNumber F Φ ε) ∂volume := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with ε hε
        exact hweight ε hε
      _ ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) θ,
          bookEntropyWeight
            (allProbabilityUniformL2CoveringNumber F Φ ε) ∂volume := by
        exact lintegral_mono'
          (Measure.restrict_mono hhalf_subset le_rfl) le_rfl
  rw [setLIntegral_const, Real.volume_Ioo, sub_zero] at hconst
  have hθ_ofReal : ENNReal.ofReal θ = 2 * ENNReal.ofReal (θ / 2) := by
    rw [show θ = 2 * (θ / 2) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  calc
    ENNReal.ofReal θ * ENNReal.ofReal (Real.sqrt (Real.log 2)) =
        2 * (ENNReal.ofReal (Real.sqrt (Real.log 2)) *
          ENNReal.ofReal (θ / 2)) := by
      rw [hθ_ofReal]
      ac_rfl
    _ ≤ 2 * bookUniformCoveringEntropyIntegral θ F Φ :=
      mul_le_mul_right hconst 2

/-- At the empirical relative radius, the finite-discrete entropy integral is at
most three times the book entropy integral. -/
theorem empiricalUniformEntropyIntegral_le_three_mul_book
    {Ω : Type*} [MeasurableSpace Ω]
    (F : Set (Ω → ℝ))
    (hzero : (fun _ : Ω => 0) ∈ F)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ)
    (hΦ_meas : Measurable Φ)
    (n : ℕ) (x : Fin n → Ω) :
    uniformCoveringEntropyIntegral
        (empiricalRelativeRadiusReal F Φ n x) F Φ ≤
      3 * bookUniformCoveringEntropyIntegral
        (empiricalRelativeRadiusReal F Φ n x) F Φ := by
  let θ := empiricalRelativeRadiusReal F Φ n x
  have hθ : 0 ≤ θ := ENNReal.toReal_nonneg
  calc
    uniformCoveringEntropyIntegral θ F Φ ≤
        allProbabilityUniformCoveringEntropyIntegralRegularized θ F Φ :=
      uniformCoveringEntropyIntegral_le_allProbabilityRegularized
        F hF_meas Φ hΦ_meas θ
    _ ≤ ENNReal.ofReal θ * ENNReal.ofReal (Real.sqrt (Real.log 2)) +
        bookUniformCoveringEntropyIntegral θ F Φ :=
      allProbabilityRegularizedEntropyIntegral_le_head_add_book F Φ hθ
    _ ≤ 2 * bookUniformCoveringEntropyIntegral θ F Φ +
        bookUniformCoveringEntropyIntegral θ F Φ :=
      add_le_add
        (empiricalRadius_head_le_two_mul_bookEntropyIntegral
          F hzero hF_meas Φ hΦ_meas n x)
        le_rfl
    _ = 3 * bookUniformCoveringEntropyIntegral θ F Φ := by ring

end AsymptoticStatistics.EmpiricalProcess
