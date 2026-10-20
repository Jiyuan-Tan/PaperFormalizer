module
public import StatLean.AsymptoticStatistics.LowerBounds.GaussianConeQuantization
public import StatLean.AsymptoticStatistics.LowerBounds.BowlShapedUCApprox

@[expose] public section

/-! # Genuine-cone Gaussian-shift minimax brick -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace AsymptoticStatistics.LowerBounds.GaussianConeMinimax
open AsymptoticStatistics
open AsymptoticStatistics.LowerBounds.GaussianConePrior
open AsymptoticStatistics.LowerBounds.GaussianConeBayes
open AsymptoticStatistics.LowerBounds.GaussianConeQuantization
open AsymptoticStatistics.LowerBounds.BowlShapedUCApprox
variable {m : ℕ}

/-- Bounded-UC limit-experiment brick.

Proof idea: `exists_conePrior_bayes_lower_bound` supplies a deep/diffuse
normalized cone prior; `exists_finite_quantization` replaces it by finite
support before taking the supremum over finite subsets. -/
theorem gaussianCone_minimax_bounded
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (_h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ C)
    (_hconv : Convex ℝ C)
    (_hcone : ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t • x ∈ C)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (ℓ : ℝ → ℝ≥0∞)
    (_hbowl : BowlShaped ℓ) (_hlsc : LowerSemicontinuous ℓ)
    (_hfinite : ∀ x, ℓ x ≠ ∞)
    (_hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (_huc : UniformContinuous fun x => (ℓ x).toReal) :
    (⨆ I : {S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C},
      ⨅ T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f},
        ⨆ h ∈ (I : Finset _), ∫⁻ X, ℓ (T.1 X - A h)
          ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)))
      ≥ ∫⁻ u, ℓ u ∂(gaussianReal 0
        ⟨effectiveScale C A ^ 2, sq_nonneg _⟩) := by
  let M : ℝ≥0∞ :=
    ⨆ I : {S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C},
      ⨅ T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f},
        ⨆ h ∈ (I : Finset _), ∫⁻ X, ℓ (T.1 X - A h)
          ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ))
  change (∫⁻ u, ℓ u ∂(gaussianReal 0
    ⟨effectiveScale C A ^ 2, sq_nonneg _⟩)) ≤ M
  refine ENNReal.le_of_forall_pos_le_add fun η hη hMtop => ?_
  by_cases hηtop : η = ∞
  · rw [hηtop, add_top]
    exact le_top
  let e : ℝ≥0∞ := η / 2
  have hηE : 0 < (η : ℝ≥0∞) := by exact_mod_cast hη
  have he : 0 < e := ENNReal.half_pos hηE.ne'
  rcases exists_conePrior_bayes_lower_bound C _h0 _hconv _hcone A ℓ
    _hbowl _hlsc _hbdd e he with
    ⟨h₀, c, hc, hgauss, hz, hztop, hprob, hsupp, hbayes⟩
  let π := restrictedTranslatedGaussianPrior C h₀ c
  letI : IsProbabilityMeasure π := hprob
  rcases exists_finite_quantization C π hsupp A ℓ _hfinite _hbdd _huc e he with
    ⟨I, hIC, hquant⟩
  let J : {S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C} := ⟨I, hIC⟩
  let F : ℝ≥0∞ :=
    ⨅ T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f},
      ⨆ h ∈ I, ∫⁻ X, ℓ (T.1 X - A h) ∂(multivariateGaussian h 1)
  have hFM : F ≤ M := le_iSup_of_le J le_rfl
  calc
    ∫⁻ u, ℓ u ∂(gaussianReal 0 ⟨effectiveScale C A ^ 2, sq_nonneg _⟩) ≤
        measurableBayesRisk π A ℓ + e := hbayes
    _ ≤ (F + e) + e := add_le_add_left hquant e
    _ = F + η := by rw [add_assoc, ENNReal.add_halves]
    _ ≤ M + η := add_le_add_left hFM η

/-- Limit-experiment genuine-cone minimax brick.  This is not by itself the
full semiparametric Theorem 25.21. -/
theorem gaussianCone_minimax
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (_h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ C)
    (_hconv : Convex ℝ C)
    (_hcone : ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t • x ∈ C)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (ℓ : ℝ → ℝ≥0∞)
    (_hbowl : BowlShaped ℓ) (_hlsc : LowerSemicontinuous ℓ) :
    (⨆ I : {S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C},
      ⨅ T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f},
        ⨆ h ∈ (I : Finset _), ∫⁻ X, ℓ (T.1 X - A h)
          ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)))
      ≥ ∫⁻ u, ℓ u ∂(gaussianReal 0
        ⟨effectiveScale C A ^ 2, sq_nonneg _⟩) := by
  rcases bowlShaped_uc_approx ℓ _hbowl _hlsc with
    ⟨ℓn, hbowl, hfinite, hbdd, huc, hmono, htend⟩
  have hle (n : ℕ) (x : ℝ) : ℓn n x ≤ ℓ x := by
    apply ge_of_tendsto (htend x)
    exact Filter.eventually_atTop.2 ⟨n, fun k hk => hmono x hk⟩
  have hcont (n : ℕ) : Continuous (ℓn n) := by
    have h := ENNReal.continuous_ofReal.comp (huc n).continuous
    convert h using 1
    funext x
    exact (ENNReal.ofReal_toReal (hfinite n x)).symm
  let M : ℝ≥0∞ :=
    ⨆ I : {S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C},
      ⨅ T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f},
        ⨆ h ∈ (I : Finset _), ∫⁻ X, ℓ (T.1 X - A h)
          ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ))
  change (∫⁻ u, ℓ u ∂(gaussianReal 0
    ⟨effectiveScale C A ^ 2, sq_nonneg _⟩)) ≤ M
  have hrisk (n : ℕ) (T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f})
      (h : EuclideanSpace ℝ (Fin m)) :
      (∫⁻ X, ℓn n (T.1 X - A h) ∂(multivariateGaussian h 1)) ≤
        ∫⁻ X, ℓ (T.1 X - A h) ∂(multivariateGaussian h 1) :=
    lintegral_mono fun X => hle n _
  have hbounded (n : ℕ) :
      (∫⁻ u, ℓn n u ∂(gaussianReal 0
        ⟨effectiveScale C A ^ 2, sq_nonneg _⟩)) ≤ M := by
    have hminimax := gaussianCone_minimax_bounded C _h0 _hconv _hcone A (ℓn n)
      (hbowl n) (hcont n).lowerSemicontinuous (hfinite n) (hbdd n) (huc n)
    calc
      ∫⁻ u, ℓn n u ∂(gaussianReal 0
          ⟨effectiveScale C A ^ 2, sq_nonneg _⟩) ≤
          ⨆ I : {S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C},
            ⨅ T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f},
              ⨆ h ∈ (I : Finset _), ∫⁻ X, ℓn n (T.1 X - A h)
                ∂(multivariateGaussian h 1) := hminimax
      _ ≤ M := by
        apply iSup_le
        intro I
        have hIM :
            (⨅ T : {f : EuclideanSpace ℝ (Fin m) → ℝ // Measurable f},
              ⨆ h ∈ (I : Finset _), ∫⁻ X, ℓ (T.1 X - A h)
                ∂(multivariateGaussian h 1)) ≤ M := le_iSup_of_le I le_rfl
        refine (iInf_mono fun T => ?_).trans hIM
        apply iSup_le
        intro h
        apply iSup_le
        intro hh
        exact le_iSup_of_le h (le_iSup_of_le hh (hrisk n T h))
  have hsup (x : ℝ) : (⨆ n, ℓn n x) = ℓ x := by
    apply le_antisymm
    · exact iSup_le fun n => hle n x
    · apply le_of_tendsto (htend x)
      exact Filter.Eventually.of_forall fun n => le_iSup (fun k => ℓn k x) n
  calc
    ∫⁻ u, ℓ u ∂(gaussianReal 0 ⟨effectiveScale C A ^ 2, sq_nonneg _⟩) =
        ∫⁻ u, ⨆ n, ℓn n u ∂(gaussianReal 0
          ⟨effectiveScale C A ^ 2, sq_nonneg _⟩) := by
      apply lintegral_congr
      exact fun x => (hsup x).symm
    _ = ⨆ n, ∫⁻ u, ℓn n u ∂(gaussianReal 0
          ⟨effectiveScale C A ^ 2, sq_nonneg _⟩) := by
      rw [lintegral_iSup]
      · exact fun n => (hbowl n).measurable
      · exact fun _ _ h => fun x => hmono x h
    _ ≤ M := iSup_le hbounded

/-- Bounded-UC randomized vector Gaussian-cone minimax theorem on a cone whose
linear span is the whole parameter space.

Proof idea: combine the vector diffuse-prior Bayes bound with vector finite
quantization and absorb the arbitrary positive error. -/
theorem gaussianCone_minimax_vec_bounded_fullSpan {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (_h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ C)
    (_hconv : Convex ℝ C)
    (_hcone : ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t • x ∈ C)
    (_hspan : Submodule.span ℝ C = ⊤)
    (A : Matrix (Fin d) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (_hbowl : BowlShaped ℓ) (_hlsc : LowerSemicontinuous ℓ)
    (_hfinite : ∀ x, ℓ x ≠ ∞)
    (_hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (_huc : UniformContinuous fun x => (ℓ x).toReal) :
    (⨆ I : {S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C},
      ⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin d)),
        ⨆ h ∈ (I : Finset _), gaussianShiftKernelRiskVec A ℓ κ h) ≥
      ∫⁻ u, ℓ u ∂(multivariateGaussian 0 (A * A.transpose)) := by
  let M : ℝ≥0∞ :=
    ⨆ I : {S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C},
      ⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin d)),
        ⨆ h ∈ (I : Finset _), gaussianShiftKernelRiskVec A ℓ κ h
  change (∫⁻ u, ℓ u ∂(multivariateGaussian 0 (A * A.transpose))) ≤ M
  refine ENNReal.le_of_forall_pos_le_add fun η hη hMtop => ?_
  by_cases hηtop : η = ∞
  · rw [hηtop, add_top]
    exact le_top
  let e : ℝ≥0∞ := η / 2
  have hηE : 0 < (η : ℝ≥0∞) := by exact_mod_cast hη
  have he : 0 < e := ENNReal.half_pos hηE.ne'
  rcases exists_conePrior_bayes_lower_bound_vec C _h0 _hconv _hcone _hspan
    A ℓ _hbowl _hlsc _hbdd e he with
    ⟨h₀, c, hc, hgauss, hz, hztop, hprob, hsupp, hbayes⟩
  let π := restrictedTranslatedGaussianPrior C h₀ c
  letI : IsProbabilityMeasure π := hprob
  rcases exists_finite_quantization_vec C π hsupp A ℓ _hfinite _hbdd _huc e he with
    ⟨I, hIC, hquant⟩
  let J : {S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C} := ⟨I, hIC⟩
  let F : ℝ≥0∞ := ⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin d)),
    ⨆ h ∈ I, gaussianShiftKernelRiskVec A ℓ κ h
  have hFM : F ≤ M := by
    exact le_iSup_of_le J le_rfl
  calc
    ∫⁻ u, ℓ u ∂(multivariateGaussian 0 (A * A.transpose)) ≤
        measurableBayesRiskVec π A ℓ + e := hbayes
    _ ≤ (F + e) + e := add_le_add_left hquant e
    _ = F + η := by rw [add_assoc, ENNReal.add_halves]
    _ ≤ M + η := add_le_add_left hFM η

/-- Full randomized vector Gaussian-cone minimax theorem.  Singular
`A Aᵀ`, `d = 0`, and the zero matrix are included.

Proof idea: apply `bowlShaped_uc_approx_vec`, use the bounded theorem at each
approximation level, and pass to the monotone limit. -/
theorem gaussianCone_minimax_vec_fullSpan {d : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin m)))
    (_h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ C)
    (_hconv : Convex ℝ C)
    (_hcone : ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t • x ∈ C)
    (_hspan : Submodule.span ℝ C = ⊤)
    (A : Matrix (Fin d) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (_hbowl : BowlShaped ℓ) (_hlsc : LowerSemicontinuous ℓ) :
    (⨆ I : {S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C},
      ⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin d)),
        ⨆ h ∈ (I : Finset _), gaussianShiftKernelRiskVec A ℓ κ h) ≥
      ∫⁻ u, ℓ u ∂(multivariateGaussian 0 (A * A.transpose)) := by
  rcases bowlShaped_uc_approx_vec ℓ _hbowl _hlsc with
    ⟨ℓn, hbowl, hfinite, hbdd, huc, hmono, htend⟩
  have hle (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℓn n x ≤ ℓ x := by
    apply ge_of_tendsto (htend x)
    exact Filter.eventually_atTop.2 ⟨n, fun k hk => hmono x hk⟩
  have hcont (n : ℕ) : Continuous (ℓn n) := by
    have h := ENNReal.continuous_ofReal.comp (huc n).continuous
    convert! h using 1
    funext x
    exact (ENNReal.ofReal_toReal (hfinite n x)).symm
  let M : ℝ≥0∞ :=
    ⨆ I : {S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C},
      ⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin d)),
        ⨆ h ∈ (I : Finset _), gaussianShiftKernelRiskVec A ℓ κ h
  change (∫⁻ u, ℓ u ∂(multivariateGaussian 0 (A * A.transpose))) ≤ M
  have hrisk (n : ℕ)
      (κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin d))) (h : EuclideanSpace ℝ (Fin m)) :
      gaussianShiftKernelRiskVec A (ℓn n) κ h ≤
        gaussianShiftKernelRiskVec A ℓ κ h := by
    unfold gaussianShiftKernelRiskVec
    exact lintegral_mono fun a => hle n (a - matrixActionVec A h)
  have hbounded (n : ℕ) :
      (∫⁻ u, ℓn n u ∂(multivariateGaussian 0 (A * A.transpose))) ≤ M := by
    have hminimax := gaussianCone_minimax_vec_bounded_fullSpan C _h0 _hconv _hcone
      _hspan A (ℓn n) (hbowl n) (hcont n).lowerSemicontinuous
      (hfinite n) (hbdd n) (huc n)
    calc
      ∫⁻ u, ℓn n u ∂(multivariateGaussian 0 (A * A.transpose)) ≤
          ⨆ I : {S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C},
            ⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
                (EuclideanSpace ℝ (Fin d)),
              ⨆ h ∈ (I : Finset _), gaussianShiftKernelRiskVec A (ℓn n) κ h :=
        hminimax
      _ ≤ M := by
        apply iSup_le
        intro I
        have hIM :
            (⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
                (EuclideanSpace ℝ (Fin d)),
              ⨆ h ∈ (I : Finset _), gaussianShiftKernelRiskVec A ℓ κ h) ≤ M := by
          exact le_iSup_of_le I le_rfl
        refine (iInf_mono fun κ => ?_).trans hIM
        apply iSup_le
        intro h
        apply iSup_le
        intro hh
        exact le_iSup_of_le h (le_iSup_of_le hh (hrisk n κ h))
  have hsup (x : EuclideanSpace ℝ (Fin d)) : (⨆ n, ℓn n x) = ℓ x := by
    apply le_antisymm
    · exact iSup_le fun n => hle n x
    · apply le_of_tendsto (htend x)
      exact Filter.Eventually.of_forall fun n => le_iSup (fun k => ℓn k x) n
  calc
    ∫⁻ u, ℓ u ∂(multivariateGaussian 0 (A * A.transpose)) =
        ∫⁻ u, ⨆ n, ℓn n u ∂(multivariateGaussian 0 (A * A.transpose)) := by
      apply lintegral_congr
      exact fun x => (hsup x).symm
    _ = ⨆ n, ∫⁻ u, ℓn n u ∂(multivariateGaussian 0 (A * A.transpose)) := by
      rw [lintegral_iSup]
      · exact fun n => (hbowl n).measurable
      · exact fun _ _ h => fun x => hmono x h
    _ ≤ M := iSup_le hbounded

end AsymptoticStatistics.LowerBounds.GaussianConeMinimax
