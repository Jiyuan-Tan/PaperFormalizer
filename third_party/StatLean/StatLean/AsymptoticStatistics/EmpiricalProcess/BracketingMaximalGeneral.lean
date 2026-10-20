module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.MaximalFullChaining

@[expose] public section

/-!
# General bracketing maximal inequalities

This module proves vdV Lemma 19.34 and
Corollary 19.35 (pp.286--288).  The full-class theorem branches internally on
the empty class, `n = 0`, and an infinite entropy integral; its public surface
therefore contains no finite-cover, partition, envelope-measurability,
envelope-`L²`, density, or class-nonemptiness certificate.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal
open scoped ENNReal

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {P : Measure Ω} {μ : Measure Ξ}
variable {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}

/-- Regularized head threshold
`δ / entropyWeight(N).toReal = δ / sqrt (log (1 + N))`.

Edge behavior: finite counts `0` and `1` remain total through `log (1 + N)`;
if `N = ⊤`, Lean's total division returns `0`. This normalization is used only
for intermediate estimates; `bracketingBookCutoff` gives the exact book normalization. -/
noncomputable def bracketingThresholdRegularized (δ : ℝ) (N : ℕ∞) : ℝ :=
  δ / (entropyWeight N).toReal

/-- Exact claim-bearing cutoff `a(δ)` from vdV Lemma 19.34 (pp.286--287).

For finite `N`, this is `δ / sqrt (max 1 (log N))`.  Edge behavior: the
extended value `N = ⊤` is totalized to `0`; the main theorem handles the
infinite-entropy branch before constructing the finite chain. -/
noncomputable def bracketingBookCutoff (δ : ℝ) (N : ℕ∞) : ℝ :=
  ENat.recTopCoe 0
    (fun n : ℕ => δ / Real.sqrt (max 1 (Real.log (n : ℝ)))) N

@[simp] lemma bracketingBookCutoff_top (δ : ℝ) :
    bracketingBookCutoff δ ⊤ = 0 := rfl

@[simp] lemma bracketingBookCutoff_coe (δ : ℝ) (n : ℕ) :
    bracketingBookCutoff δ (n : ℕ∞) =
      δ / Real.sqrt (max 1 (Real.log (n : ℝ))) := rfl

private lemma sqrt_log_one_add_nat_le_two_bookLog_of_le_sq
    {m N : ℕ} (hN : 1 ≤ N) (hm : m ≤ N ^ 2) :
    Real.sqrt (Real.log (1 + (m : ℝ))) ≤
      2 * Real.sqrt (max 1 (Real.log (N : ℝ))) := by
  have hN_real : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN_pos : (0 : ℝ) < N := zero_lt_one.trans_le hN_real
  have hm_real : (m : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hm
  have harg_le : (1 : ℝ) + m ≤ 2 * (N : ℝ) ^ 2 := by nlinarith
  have hlog_le := Real.log_le_log (by positivity : (0 : ℝ) < 1 + m) harg_le
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hN_pos.ne'),
    Real.log_pow] at hlog_le
  norm_num at hlog_le
  have hlog_two_le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hone_le : (1 : ℝ) ≤ max 1 (Real.log (N : ℝ)) := le_max_left _ _
  have hlogN_le : Real.log (N : ℝ) ≤ max 1 (Real.log (N : ℝ)) := le_max_right _ _
  have hlog_bound : Real.log (1 + (m : ℝ)) ≤
      4 * max 1 (Real.log (N : ℝ)) := by nlinarith
  have hleft_nonneg : 0 ≤ Real.log (1 + (m : ℝ)) := by
    apply Real.log_nonneg
    norm_num
  have hright_nonneg : 0 ≤ max 1 (Real.log (N : ℝ)) := hone_le.trans' zero_le_one
  nlinarith [Real.sq_sqrt hleft_nonneg, Real.sq_sqrt hright_nonneg,
    Real.sqrt_nonneg (Real.log (1 + (m : ℝ))),
    Real.sqrt_nonneg (max 1 (Real.log (N : ℝ)))]

/-- A finite bracketing entropy integral up to a positive radius `δ` yields a
finite bracketing cover at every positive cutoff `ε ≤ δ`. -/
theorem hasFiniteBracketingCover_of_entropyIntegral_lt_top_at
    (hJ : bracketingEntropyIntegral δ F P < ⊤)
    (hε : 0 < ε) (hεδ : ε ≤ δ) :
    HasFiniteBracketingCover F ε 2 P := by
  rw [← bracketingNumber_lt_top_iff_HasFiniteBracketingCover]
  by_contra h_top
  rw [not_lt, top_le_iff] at h_top
  have h_integrand_top : ∀ ε' ∈ Set.Ioc (0 : ℝ) ε,
      entropyIntegrand ε' F P = ⊤ := by
    intro ε' hε'
    have h_bn_top : bracketingNumber ε' F 2 P = ⊤ :=
      top_unique (h_top ▸ bracketingNumber_antitone_eps hε'.2)
    rw [entropyIntegrand, h_bn_top, entropyWeight_top]
  have h_eq_top : bracketingEntropyIntegral δ F P = ⊤ := by
    rw [bracketingEntropyIntegral_eq_setLIntegral]
    refine top_le_iff.mp ?_
    calc (⊤ : ℝ≥0∞)
        = ∫⁻ _ε in Set.Ioc (0 : ℝ) ε, (⊤ : ℝ≥0∞) ∂volume := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
            ENNReal.top_mul (ENNReal.ofReal_ne_zero_iff.mpr hε)]
      _ = ∫⁻ ε' in Set.Ioc (0 : ℝ) ε, entropyIntegrand ε' F P ∂volume :=
          (setLIntegral_congr_fun measurableSet_Ioc h_integrand_top).symm
      _ ≤ ∫⁻ ε' in Set.Ioc (0 : ℝ) δ, entropyIntegrand ε' F P ∂volume :=
          lintegral_mono_set (Set.Ioc_subset_Ioc_right hεδ)
  rw [h_eq_top] at hJ
  exact (lt_irrefl _ hJ).elim

/-- Chosen finite full-class bracket data at an arbitrary positive head scale,
with cardinality equal to the corresponding bracketing number.  The object is
derived from entropy finiteness and is not a public hypothesis of Lemma 19.34. -/
theorem finiteBracketingData_of_entropyIntegral_lt_top
    (hJ : bracketingEntropyIntegral δ F P < ⊤)
    (hε : 0 < ε) (hεδ : ε ≤ δ) :
    ∃ cov : BracketingCoverData F ε P,
      (cov.k : ℕ∞) = bracketingNumber ε F 2 P := by
  have hcov := hasFiniteBracketingCover_of_entropyIntegral_lt_top_at hJ hε hεδ
  exact ⟨minimalCoverData ε hcov, minimalCoverData_k ε hcov⟩

/-- Outer-expectation truncation split for the full class.  The first term is
the genuine projection class `truncateClass F t`; the second is the outer
envelope tail.  No measurability of `Φ` is assumed (vdV Lemma 19.34, p.286). -/
theorem outerExpectation_supNorm_le_truncateClass_add_tail
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (hF_ne : F.Nonempty) (hF_meas : ∀ f ∈ F, Measurable f)
    {δ : ℝ}
    (hF_L2 : ∀ f ∈ F, eLpNorm f 2 P < ENNReal.ofReal δ)
    (hΦ_env : IsEnvelope F Φ)
    {X : ℕ → Ξ → Ω} (hX_meas : ∀ i, Measurable (X i))
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    outerExpectation μ (fun ξ => supNormOver F
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) ≤
      outerExpectation μ (fun ξ => supNormOver (truncateClass F t)
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) +
      2 * ENNReal.ofReal (Real.sqrt n) *
        outerExpectation P (fun x => ENNReal.ofReal
          (Φ x * Set.indicator {y | t < Φ y} (1 : Ω → ℝ) x)) := by
  classical
  have hΦ_nn : ∀ x, 0 ≤ Φ x := fun x => hΦ_env.nonneg hF_ne.choose_spec x
  set Ψ : Ω → ℝ := fun x =>
    Φ x * Set.indicator {y | t < Φ y} (1 : Ω → ℝ) x with hΨ_def
  have hΨ_nn : ∀ x, 0 ≤ Ψ x := by
    intro x
    refine mul_nonneg (hΦ_nn x) ?_
    by_cases hx : x ∈ {y | t < Φ y} <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  set 𝒢 : Set (Ω → ℝ) :=
    {g | ∃ f ∈ F, g = fun x => f x - clampFn t f x} with h𝒢_def
  have hdom : ∀ g ∈ 𝒢, ∀ x, |g x| ≤ Ψ x := by
    rintro g ⟨f, hf, rfl⟩ x
    have hfΦ : |f x| ≤ Φ x := hΦ_env f hf x
    by_cases hx : x ∈ {y | t < Φ y}
    · simp only [hΨ_def, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      have hres : |f x - clampFn t f x| ≤ |f x| := by
        unfold clampFn clampReal
        rcases le_total (f x) t with hle | hle <;>
          rcases le_total (-t) (f x) with hle2 | hle2 <;>
          rw [max_def, min_def] <;> split_ifs <;>
          rcases abs_cases (f x) with ⟨e, _⟩ | ⟨e, _⟩ <;>
          rw [e] <;> rw [abs_sub_le_iff] <;> constructor <;> linarith
      exact hres.trans hfΦ
    · simp only [hΨ_def, Set.indicator_of_notMem hx, mul_zero]
      have hΦt : Φ x ≤ t := not_lt.mp (by simpa using hx)
      have hft : |f x| ≤ t := hfΦ.trans hΦt
      have hcl : clampFn t f x = f x := by
        unfold clampFn
        exact clampReal_of_mem hft
      rw [hcl, sub_self, abs_zero]
  have hF_memLp : ∀ f ∈ F, MemLp f 2 P := fun f hf =>
    ⟨(hF_meas f hf).aestronglyMeasurable, (hF_L2 f hf).trans ENNReal.ofReal_lt_top⟩
  have h_pt : ∀ ξ : Ξ,
      supNormOver F
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ≤
        supNormOver (truncateClass F t)
            (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) +
          supNormOver 𝒢
            (fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) := by
    intro ξ
    refine iSup₂_le fun f hf => ?_
    have hf_int : Integrable f P := (hF_memLp f hf).integrable (by norm_num)
    have hclamp_mem : MemLp (clampFn t f) 2 P := clampFn_memLp ht (hF_memLp f hf)
    have hclamp_int : Integrable (clampFn t f) P := hclamp_mem.integrable (by norm_num)
    have hsplit : empiricalProcess P n (fun i : Fin n => X i.val ξ) f =
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn t f) +
          empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun x => f x - clampFn t f x) := by
      rw [← empiricalProcess_add P n _ (clampFn t f)
        (fun x => f x - clampFn t f x) hclamp_int (hf_int.sub hclamp_int)]
      congr 1
      funext x
      ring
    change ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ) f| ≤ _
    rw [hsplit]
    calc ENNReal.ofReal
          |empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn t f) +
            empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun x => f x - clampFn t f x)|
        ≤ ENNReal.ofReal
            (|empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn t f)| +
              |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => f x - clampFn t f x)|) :=
          ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ ≤ ENNReal.ofReal
            |empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn t f)| +
          ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun x => f x - clampFn t f x)| := ENNReal.ofReal_add_le
      _ ≤ supNormOver (truncateClass F t)
              (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) +
            supNormOver 𝒢
              (fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) := by
        exact add_le_add (le_supNormOver ⟨f, hf, rfl⟩)
          (le_supNormOver ⟨f, hf, rfl⟩)
  by_cases hn0 : n = 0
  · subst n
    simp [supNormOver, outerExpectation_const]
  have hn : 1 ≤ n := (Nat.one_le_iff_ne_zero).2 hn0
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  set T : ℝ≥0∞ := outerExpectation P (fun x => ENNReal.ofReal (Ψ x)) with hT_def
  have hlin_le_outer : (∫⁻ x, ENNReal.ofReal (Ψ x) ∂P) ≤ T := by
    rw [hT_def]
    unfold outerExpectation
    refine le_iInf fun V => ?_
    exact lintegral_mono V.2.2
  set U : Ξ → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal (empiricalAvg Ψ n (fun i : Fin n => X i.val ξ)) with hU_def
  have hU_outer : outerExpectation μ U ≤ T := by
    rw [hT_def]
    refine le_iInf fun V => ?_
    set W : Ξ → ℝ≥0∞ := fun ξ => ((n : ℝ≥0∞))⁻¹ *
      ∑ i : Fin n, (V : Ω → ℝ≥0∞) (X i.val ξ) with hW_def
    have hW_meas : Measurable W := by
      refine Measurable.const_mul ?_ _
      refine Finset.measurable_sum Finset.univ ?_
      intro i _
      exact V.2.1.comp (hX_meas i.val)
    have hUW : U ≤ W := by
      intro ξ
      rw [hU_def, hW_def]
      unfold empiricalAvg
      change ENNReal.ofReal ((n : ℝ)⁻¹ * ∑ i : Fin n, Ψ (X i.val ξ)) ≤ _
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
      rw [ENNReal.ofReal_inv_of_pos hn_pos, ENNReal.ofReal_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (zero_le)
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hΨ_nn _)]
      exact Finset.sum_le_sum (fun i _ => V.2.2 (X i.val ξ))
    have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    have hn_ne_zero : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn0
    have hinv_ne_top : ((n : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hn_ne_zero
    calc outerExpectation μ U ≤ outerExpectation μ W := outerExpectation_mono hUW
      _ = ∫⁻ ξ, W ξ ∂μ := outerExpectation_eq_lintegral hW_meas
      _ = ((n : ℝ≥0∞))⁻¹ *
          ∫⁻ ξ, ∑ i : Fin n, (V : Ω → ℝ≥0∞) (X i.val ξ) ∂μ := by
        rw [hW_def, lintegral_const_mul' _ _ hinv_ne_top]
      _ = ((n : ℝ≥0∞))⁻¹ *
          ∑ i : Fin n, ∫⁻ ξ, (V : Ω → ℝ≥0∞) (X i.val ξ) ∂μ := by
        congr 1
        rw [lintegral_finset_sum Finset.univ]
        intro i _
        exact V.2.1.comp (hX_meas i.val)
      _ = ((n : ℝ≥0∞))⁻¹ *
          ∑ _i : Fin n, ∫⁻ x, (V : Ω → ℝ≥0∞) x ∂P := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        have h_id : μ.map (X i.val) = P := by
          rw [← hX_law]
          exact (hX_idem i.val).map_eq
        rw [← h_id]
        exact (lintegral_map V.2.1 (hX_meas i.val)).symm
      _ = ((n : ℝ≥0∞))⁻¹ * (n : ℝ≥0∞) *
          ∫⁻ x, (V : Ω → ℝ≥0∞) x ∂P := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_assoc]
      _ = ∫⁻ x, (V : Ω → ℝ≥0∞) x ∂P := by
        rw [ENNReal.inv_mul_cancel hn_ne_zero hn_ne_top, one_mul]
  have h_excess : ∀ ξ : Ξ,
      supNormOver 𝒢
          (fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) ≤
        ENNReal.ofReal (Real.sqrt n) * (U ξ + T) := by
    intro ξ
    refine (supNormProcess_dominated_pointwise_bound
      (P := P) 𝒢 Ψ hdom n hn ξ).trans ?_
    rw [hU_def]
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hlin_le_outer) (zero_le)
  have htotal : ∀ ξ : Ξ,
      supNormOver F
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ≤
        supNormOver (truncateClass F t)
            (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) +
          ENNReal.ofReal (Real.sqrt n) * (U ξ + T) :=
    fun ξ => (h_pt ξ).trans (add_le_add le_rfl (h_excess ξ))
  have hsqrt_ne_top : ENNReal.ofReal (Real.sqrt n) ≠ ⊤ := ENNReal.ofReal_ne_top
  have htail_outer : outerExpectation μ
      (fun ξ => ENNReal.ofReal (Real.sqrt n) * (U ξ + T)) ≤
      2 * ENNReal.ofReal (Real.sqrt n) * T := by
    calc outerExpectation μ
          (fun ξ => ENNReal.ofReal (Real.sqrt n) * (U ξ + T))
        = ENNReal.ofReal (Real.sqrt n) *
            outerExpectation μ (fun ξ => U ξ + T) := by
          simpa only [Pi.smul_apply, smul_eq_mul] using!
            (outerExpectation_const_smul (μ := μ)
              (ENNReal.ofReal (Real.sqrt n)) hsqrt_ne_top (fun ξ => U ξ + T))
      _ ≤ ENNReal.ofReal (Real.sqrt n) *
            (outerExpectation μ U + outerExpectation μ (fun _ : Ξ => T)) := by
          gcongr
          exact outerExpectation_add_le U (fun _ : Ξ => T)
      _ ≤ ENNReal.ofReal (Real.sqrt n) * (T + T) := by
          exact mul_le_mul_right
            (add_le_add hU_outer (by rw [outerExpectation_const, measure_univ, mul_one])) _
      _ = 2 * ENNReal.ofReal (Real.sqrt n) * T := by ring
  calc outerExpectation μ (fun ξ => supNormOver F
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f))
      ≤ outerExpectation μ (fun ξ =>
          supNormOver (truncateClass F t)
              (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) +
            ENNReal.ofReal (Real.sqrt n) * (U ξ + T)) :=
        outerExpectation_mono htotal
    _ ≤ outerExpectation μ (fun ξ => supNormOver (truncateClass F t)
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) +
        outerExpectation μ
          (fun ξ => ENNReal.ofReal (Real.sqrt n) * (U ξ + T)) :=
      outerExpectation_add_le _ _
    _ ≤ outerExpectation μ (fun ξ => supNormOver (truncateClass F t)
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) +
        2 * ENNReal.ofReal (Real.sqrt n) * T := add_le_add le_rfl htail_outer
    _ = outerExpectation μ (fun ξ => supNormOver (truncateClass F t)
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) +
        2 * ENNReal.ofReal (Real.sqrt n) *
          outerExpectation P (fun x => ENNReal.ofReal
            (Φ x * Set.indicator {y | t < Φ y} (1 : Ω → ℝ) x)) := by
      rw [hT_def, hΨ_def]

/-- Construct the regularized full-clamped partition at the exact book
cutoff `sqrt n * bracketingBookCutoff δ Nδ`.  The scale-`8δ`,
initial-smallness, and head-visibility facts are derived proof data consumed by
the chaining module, never caller-supplied hypotheses of Lemma 19.34. -/
theorem exists_fullClampedNestedPartition
    (hJ : bracketingEntropyIntegral δ F P < ⊤) (hF_ne : F.Nonempty)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_L2 : ∀ f ∈ F, eLpNorm f 2 P < ENNReal.ofReal δ)
    (hΦ_env : IsEnvelope F Φ)
    (hδ : 0 < δ) (n : ℕ) :
    Nonempty (RegularizedFullClampedPartitionData F P Φ δ n
      (Real.sqrt n * bracketingBookCutoff δ
        (bracketingNumber δ F 2 P))) := by
  classical
  have hcovδ : HasFiniteBracketingCover F δ 2 P :=
    hasFiniteBracketingCover_of_entropyIntegral_lt_top_at hJ hδ le_rfl
  have hN_lt : bracketingNumber δ F 2 P < ⊤ :=
    bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mpr hcovδ
  set N : ℕ := (bracketingNumber δ F 2 P).toNat with hN_def
  have hN_eq : (N : ℕ∞) = bracketingNumber δ F 2 P := by
    rw [hN_def, ENat.coe_toNat hN_lt.ne]
  have hN_one : 1 ≤ N := by
    have h := one_le_bracketingNumber_of_nonempty (P := P) hF_ne δ
    rw [← hN_eq] at h
    exact_mod_cast h
  set w : ℝ := Real.sqrt (max 1 (Real.log (N : ℝ))) with hw_def
  have hw_pos : 0 < w := by
    rw [hw_def]
    exact Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hone_le_w : (1 : ℝ) ≤ w := by
    rw [hw_def, Real.one_le_sqrt]
    exact le_max_left _ _
  set tReg : ℝ := Real.sqrt n * bracketingBookCutoff δ
    (bracketingNumber δ F 2 P) with htReg_def
  have htReg_eq : tReg = Real.sqrt n * (δ / w) := by
    rw [htReg_def, ← hN_eq, bracketingBookCutoff_coe, hw_def]
  have htReg_nonneg : 0 ≤ tReg := by rw [htReg_eq]; positivity
  have hscale_pos : ∀ p : ℕ, 0 < (1 / 2 : ℝ) ^ (p - 0) * (8 * δ) := by
    intro p; positivity
  let hcov8 : ∀ p, 0 ≤ p →
      HasFiniteBracketingCover F ((1 / 2 : ℝ) ^ (p - 0) * (8 * δ)) 2 P := by
    intro p _hp
    by_cases hscale_le : (1 / 2 : ℝ) ^ (p - 0) * (8 * δ) ≤ δ
    · exact hasFiniteBracketingCover_of_entropyIntegral_lt_top_at hJ
        (hscale_pos p) hscale_le
    · obtain ⟨k, l, u, hbr, hcover⟩ := hcovδ
      exact ⟨k, l, u, fun i => (hbr i).mono_eps (le_of_not_ge hscale_le), hcover⟩
  let B : NestedBracketPartition (truncateClass F tReg) P 0 (8 * δ) :=
    nestedBracketPartition_of_finiteEntropy_clamped 0 (by positivity) tReg
      htReg_nonneg hcov8 hF_meas
  have hcover_original : ∀ {p : ℕ}, 0 ≤ p →
      (B.coverCard p : ℕ∞) ≤
        bracketingNumber ((1 / 2 : ℝ) ^ (p - 0) * (8 * δ)) F 2 P := by
    intro p hp
    exact (B.coverCard_le hp).trans (bracketingNumber_truncateClass_le htReg_nonneg)
  have hNq0_card : B.Nq 0 ≤ B.coverCard 0 := by
    simpa using B.card_le (le_rfl : 0 ≤ 0)
  have hcover0 : (B.coverCard 0 : ℕ∞) ≤ (N : ℕ∞) := by
    calc
      (B.coverCard 0 : ℕ∞)
          ≤ bracketingNumber ((1 / 2 : ℝ) ^ (0 - 0) * (8 * δ)) F 2 P :=
            hcover_original le_rfl
      _ = bracketingNumber (8 * δ) F 2 P := by norm_num
      _ ≤ bracketingNumber δ F 2 P :=
        bracketingNumber_antitone_eps (by linarith)
      _ = (N : ℕ∞) := hN_eq.symm
  have hcover1 : (B.coverCard 1 : ℕ∞) ≤ (N : ℕ∞) := by
    calc
      (B.coverCard 1 : ℕ∞)
          ≤ bracketingNumber ((1 / 2 : ℝ) ^ (1 - 0) * (8 * δ)) F 2 P :=
            hcover_original (Nat.zero_le 1)
      _ = bracketingNumber (4 * δ) F 2 P := by
        congr 1
        ring
      _ ≤ bracketingNumber δ F 2 P :=
        bracketingNumber_antitone_eps (by linarith)
      _ = (N : ℕ∞) := hN_eq.symm
  have hNq0 : (B.Nq 0 : ℕ∞) ≤ (N : ℕ∞) := by
    exact (by exact_mod_cast hNq0_card :
      (B.Nq 0 : ℕ∞) ≤ (B.coverCard 0 : ℕ∞)).trans hcover0
  have hcover0_nat : B.coverCard 0 ≤ N := by exact_mod_cast hcover0
  have hcover1_nat : B.coverCard 1 ≤ N := by exact_mod_cast hcover1
  have hNq1_card : B.Nq 1 ≤ B.coverCard 0 * B.coverCard 1 := by
    have hcard := B.card_le (Nat.zero_le 1)
    have hprod : (∏ p ∈ Finset.Icc 0 1, B.coverCard p) =
        B.coverCard 0 * B.coverCard 1 := by
      rw [Finset.prod_Icc_succ_top (Nat.zero_le 1), Finset.Icc_self,
        Finset.prod_singleton]
    rwa [hprod] at hcard
  have hNq1_nat : B.Nq 1 ≤ N ^ 2 := by
    calc
      B.Nq 1 ≤ B.coverCard 0 * B.coverCard 1 := hNq1_card
      _ ≤ N * N := Nat.mul_le_mul hcover0_nat hcover1_nat
      _ = N ^ 2 := by ring
  have hN_le_sq : N ≤ N ^ 2 := by
    calc N = N * 1 := by simp
      _ ≤ N * N := Nat.mul_le_mul_left N hN_one
      _ = N ^ 2 := by ring
  have hw0 : Real.sqrt (Real.log (1 + (B.Nq 0 : ℝ))) ≤ 2 * w := by
    rw [hw_def]
    exact sqrt_log_one_add_nat_le_two_bookLog_of_le_sq hN_one
      ((by exact_mod_cast hNq0 : B.Nq 0 ≤ N).trans hN_le_sq)
  have hw1 : Real.sqrt (Real.log (1 + (B.Nq 1 : ℝ))) ≤ 2 * w := by
    rw [hw_def]
    exact sqrt_log_one_add_nat_le_two_bookLog_of_le_sq hN_one hNq1_nat
  have hden1_le : 1 + Real.sqrt (Real.log (1 + (B.Nq 1 : ℝ))) ≤ 4 * w := by
    linarith
  have hden0_le : 1 + Real.sqrt (Real.log (1 + (B.Nq 0 : ℝ))) ≤ 8 * w := by
    linarith
  have hcore_initial : 2 * (δ / w) ≤
      (8 * δ) / (1 + Real.sqrt (Real.log (1 + (B.Nq 1 : ℝ)))) := by
    rw [show 2 * (δ / w) = (2 * δ) / w by ring]
    rw [div_le_div_iff₀ hw_pos (by positivity)]
    nlinarith [hden1_le]
  have hcore_head : δ / w ≤
      (8 * δ) / (1 + Real.sqrt (Real.log (1 + (B.Nq 0 : ℝ)))) := by
    rw [div_le_div_iff₀ hw_pos (by positivity)]
    nlinarith [hden0_le]
  let D : FullClampedPartitionData F P Φ 0 (8 * δ) n tReg :=
    { partition := B
      coverCard_original_le := hcover_original
      width_le := by
        intro q hq i x
        simpa only [B] using
          (nestedBracketPartition_of_finiteEntropy_clamped_Δ_le
            (G := F) 0 (by positivity : 0 < 8 * δ) tReg htReg_nonneg
            hcov8 hF_meas hq i x)
      truncated_nonempty := by
        obtain ⟨f, hf⟩ := hF_ne
        exact ⟨clampFn tReg f, ⟨f, hf, rfl⟩⟩
      truncated_measurable := by
        rintro g ⟨f, hf, rfl⟩
        exact clampFn_measurable (hF_meas f hf)
      truncated_L2 := by
        rintro g ⟨f, hf, rfl⟩
        refine lt_of_le_of_lt
          (eLpNorm_mono_ae (Filter.Eventually.of_forall (fun x => ?_)))
          (lt_trans (hF_L2 f hf)
            ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)))
        simpa only [Real.norm_eq_abs] using! abs_clampReal_le tReg htReg_nonneg (f x)
      original_envelope := by
        rintro g ⟨f, hf, rfl⟩ x
        exact (abs_clampReal_le tReg htReg_nonneg (f x)).trans (hΦ_env f hf x)
      clamp_envelope := by
        intro g hg x
        exact truncateClass_abs_le htReg_nonneg hg x
      initial_comparison := hNq0_card
      firstCrossing_tailEmpty := by
        intro f hf x
        let small : ℕ → Prop := fun k =>
          B.Δ (0 + k) (cellChain B hf k) x ≤
            Real.sqrt n * chainThreshold B (8 * δ) (0 + k)
        by_cases hall : ∀ k, small k
        · exact Or.inl hall
        · simp only [not_forall] at hall
          let k := Nat.find hall
          have hk_fail : ¬ small k := Nat.find_spec hall
          have hk_prev : ∀ j < k, small j := by
            intro j hj
            exact not_not.mp (Nat.find_min hall hj)
          refine Or.inr ⟨k, hk_prev, hk_fail, ?_⟩
          intro l hkl hchain
          have hc := (chainB_chain_iff B hf (8 * δ) n l x).mp (by
            simpa only [Nat.zero_add] using hchain)
          exact hk_fail (hc.2.1 k hkl) }
  refine ⟨{
    base := D
    initial_small := ?_
    head_visible := ?_
  }⟩
  · intro i x
    refine (D.width_le le_rfl i x).trans ?_
    calc
      2 * tReg = Real.sqrt n * (2 * (δ / w)) := by rw [htReg_eq]; ring
      _ ≤ Real.sqrt n *
          ((8 * δ) / (1 + Real.sqrt (Real.log (1 + (B.Nq 1 : ℝ))))) :=
        mul_le_mul_of_nonneg_left hcore_initial (Real.sqrt_nonneg _)
      _ = Real.sqrt n * chainThreshold D.partition (8 * δ) 0 := by
        simp only [D, chainThreshold, Nat.zero_sub, pow_zero, one_mul, Nat.zero_add]
  · calc
      |tReg| = Real.sqrt n * (δ / w) := by
        rw [abs_of_nonneg htReg_nonneg, htReg_eq]
      _ ≤ Real.sqrt n *
          ((8 * δ) / (1 + Real.sqrt (Real.log (1 + (B.Nq 0 : ℝ))))) :=
        mul_le_mul_of_nonneg_left hcore_head (Real.sqrt_nonneg _)
      _ = Real.sqrt n * globalThreshold D.partition (8 * δ) := by
        simp only [D, globalThreshold]

set_option linter.unusedVariables false in
/-- **vdV Lemma 19.34 (general full-class bracketing maximal inequality).**

There is one universal constant, quantified before every type and datum.  For
a measurable class in the strict population-`L²(P)` ball of radius `δ`, the
outer expected empirical-process supremum is bounded by the bracketing entropy
integral plus the outer envelope tail at the exact book head threshold.

The empty class, `n = 0`, and `J_{[]} = ∞` are internal branches.  In
particular, finite entropy, measurable/`L²` envelope, pointwise density, and
class nonemptiness are deliberately absent from this public signature. -/
theorem bracketingMaximal_full :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (Ξ : Type*) [MeasurableSpace Ξ]
        (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (X : ℕ → Ξ → Ω)
        -- LEAN-ONLY: measurability of each sample coordinate.
        (hX_meas : ∀ i, Measurable (X i))
        -- USER-INPUT: iid observations with common law `P`; vdV Lemma 19.34.
        (hX_iindep : ProbabilityTheory.iIndepFun X μ)
        (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
        (hX_law : μ.map (X 0) = P)
        (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (δ : ℝ)
        -- USER-INPUT: positive radius, `L²`-localized class, and envelope;
        -- vdV Lemma 19.34.
        (hδ : 0 < δ)
        -- LEAN-ONLY: explicit measurability of the class members.
        (hF_meas : ∀ f ∈ F, Measurable f)
        (hF_L2 : ∀ f ∈ F, eLpNorm f 2 P < ENNReal.ofReal δ)
        (hΦ_env : IsEnvelope F Φ)
        (n : ℕ),
        outerExpectation μ (fun ξ => supNormOver F
            (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) ≤
          ENNReal.ofReal C *
            (bracketingEntropyIntegral δ F P +
              ENNReal.ofReal (Real.sqrt n) *
                outerExpectation P (fun x => ENNReal.ofReal
                  (Φ x * Set.indicator
                    {y | Real.sqrt n * bracketingBookCutoff δ
                        (bracketingNumber δ F 2 P) < Φ y}
                    (1 : Ω → ℝ) x))) := by
  classical
  obtain ⟨c, hc, hcore⟩ := bracketingMaximal_of_fullClampedPartition
  refine ⟨c + 2, by linarith, ?_⟩
  intro Ω _ P _ Ξ _ μ _ X hX_meas hX_iindep hX_idem hX_law
    F Φ δ hδ hF_meas hF_L2 hΦ_env n
  by_cases hF : F = ∅
  · subst F
    simp [supNormOver, outerExpectation_const]
  by_cases hn0 : n = 0
  · subst n
    simp [supNormOver, outerExpectation_const]
  by_cases hJtop : bracketingEntropyIntegral δ F P = ⊤
  · rw [hJtop]
    have hC_ne : ENNReal.ofReal (c + 2) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    simp [hC_ne]
  have hF_ne : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hF
  have hJ : bracketingEntropyIntegral δ F P < ⊤ :=
    lt_top_iff_ne_top.mpr hJtop
  let tReg := Real.sqrt n * bracketingBookCutoff δ
    (bracketingNumber δ F 2 P)
  have hN_lt : bracketingNumber δ F 2 P < ⊤ :=
    bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mpr
      (hasFiniteBracketingCover_of_entropyIntegral_lt_top_at hJ hδ le_rfl)
  have htReg : 0 ≤ tReg := by
    dsimp only [tReg]
    rw [← ENat.coe_toNat hN_lt.ne, bracketingBookCutoff_coe]
    positivity
  obtain ⟨D⟩ := exists_fullClampedNestedPartition
    hJ hF_ne hF_meas hF_L2 hΦ_env hδ n
  have hsplit := outerExpectation_supNorm_le_truncateClass_add_tail
    hF_ne hF_meas hF_L2 hΦ_env hX_meas hX_idem hX_law htReg n
  have htrunc := hcore Ω P Ξ μ F Φ δ n tReg D X hX_meas hX_iindep
    hX_idem hX_law hδ
  set J := bracketingEntropyIntegral δ F P
  set T := ENNReal.ofReal (Real.sqrt n) *
    outerExpectation P (fun x => ENNReal.ofReal
      (Φ x * Set.indicator {y | tReg < Φ y} (1 : Ω → ℝ) x))
  have hcC : ENNReal.ofReal c ≤ ENNReal.ofReal (c + 2) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have htwoC : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (c + 2) := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc
    outerExpectation μ (fun ξ => supNormOver F
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f))
        ≤ outerExpectation μ (fun ξ => supNormOver (truncateClass F tReg)
            (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) +
          2 * T := by simpa only [T, tReg, mul_assoc] using hsplit
    _ ≤ ENNReal.ofReal c * J + 2 * T := add_le_add htrunc le_rfl
    _ ≤ ENNReal.ofReal (c + 2) * J + ENNReal.ofReal (c + 2) * T :=
      add_le_add (mul_le_mul_of_nonneg_right hcC (zero_le))
        (mul_le_mul_of_nonneg_right htwoC (zero_le))
    _ = ENNReal.ofReal (c + 2) * (J + T) := by ring

private lemma setLIntegral_Ioc_comp_third {r : ℝ}
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ε in Set.Ioc (0 : ℝ) (3 * r), g (ε / 3) ∂volume =
      3 * ∫⁻ u in Set.Ioc (0 : ℝ) r, g u ∂volume := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hmap : Measurable (fun x : ℝ => 3 * x) := measurable_const_mul 3
  have hpre : (fun x : ℝ => 3 * x) ⁻¹' Set.Ioc (0 : ℝ) (3 * r) =
      Set.Ioc (0 : ℝ) r := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have key := setLIntegral_map (μ := volume) (s := Set.Ioc (0 : ℝ) (3 * r))
    (f := fun y : ℝ => g (y / 3)) (g := fun x : ℝ => (3 : ℝ) * x)
    measurableSet_Ioc (hg.comp (measurable_id.div_const 3)) hmap
  rw [Real.map_volume_mul_left h3, setLIntegral_smul_measure, hpre] at key
  have hgcollapse : (fun x : ℝ => g ((3 * x) / 3)) = g := by
    funext x
    congr 1
    ring
  rw [hgcollapse] at key
  have habs : ENNReal.ofReal |(3 : ℝ)⁻¹| = (3 : ℝ≥0∞)⁻¹ := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < (3 : ℝ)⁻¹),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3), ENNReal.ofReal_ofNat]
  rw [habs, smul_eq_mul] at key
  rw [← key, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

set_option linter.unusedVariables false in
/-- **vdV Corollary 19.35 (integrable-envelope bracketing bound).**

For a measurable class with a measurable `L²(P)` envelope, one universal
constant bounds the outer expected empirical-process supremum by the
bracketing entropy integral at the envelope's `L²` norm.  The proof will apply
Lemma 19.34 internally at the strict scale `3 * ‖Φ‖₂`; that scale introduces no
extra public hypothesis. -/
theorem bracketingMaximal_integrableEnvelope :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (Ξ : Type*) [MeasurableSpace Ξ]
        (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (X : ℕ → Ξ → Ω)
        -- LEAN-ONLY: measurability of each sample coordinate.
        (hX_meas : ∀ i, Measurable (X i))
        -- USER-INPUT: iid observations with common law `P`; vdV Corollary 19.35.
        (hX_iindep : ProbabilityTheory.iIndepFun X μ)
        (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
        (hX_law : μ.map (X 0) = P)
        (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
        -- LEAN-ONLY: explicit measurability of the class and envelope.
        (hF_meas : ∀ f ∈ F, Measurable f)
        -- USER-INPUT: a square-integrable envelope; vdV Corollary 19.35.
        (hΦ_env : IsEnvelope F Φ)
        (hΦ_meas : Measurable Φ) (hΦ_L2 : MemLp Φ 2 P) (n : ℕ),
        outerExpectation μ (fun ξ => supNormOver F
            (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) ≤
          ENNReal.ofReal C * bracketingEntropyIntegral
            (eLpNorm Φ 2 P).toReal F P := by
  classical
  obtain ⟨c, hc, hmax⟩ := bracketingMaximal_full
  refine ⟨4 * c, by positivity, ?_⟩
  intro Ω _ P _ Ξ _ μ _ X hX_meas hX_iindep hX_idem hX_law
    F Φ hF_meas hΦ_env hΦ_meas hΦ_L2 n
  let r : ℝ := (eLpNorm Φ 2 P).toReal
  by_cases hF : F = ∅
  · subst F
    simp [supNormOver, outerExpectation_const]
  have hF_ne : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hF
  have hΦ_nn : ∀ x, 0 ≤ Φ x := fun x => hΦ_env.nonneg hF_ne.choose_spec x
  by_cases hn0 : n = 0
  · subst n
    simp [supNormOver, outerExpectation_const]
  by_cases hr0 : r = 0
  · have hΦ_norm_zero : eLpNorm Φ 2 P = 0 := by
      rw [← ENNReal.ofReal_toReal hΦ_L2.eLpNorm_lt_top.ne]
      change ENNReal.ofReal r = 0
      rw [hr0]
      simp
    have hΦ_zero : Φ =ᵐ[P] 0 :=
      (eLpNorm_eq_zero_iff hΦ_L2.aestronglyMeasurable (by norm_num)).mp hΦ_norm_zero
    have hf_zero : ∀ f ∈ F, f =ᵐ[P] 0 := by
      intro f hf
      filter_upwards [hΦ_zero] with x hx
      apply abs_eq_zero.mp
      exact le_antisymm ((hΦ_env f hf x).trans_eq hx) (abs_nonneg _)
    have hF_L2_one : ∀ f ∈ F, eLpNorm f 2 P < ENNReal.ofReal 1 := by
      intro f hf
      rw [eLpNorm_eq_zero_of_ae_zero (hf_zero f hf)]
      norm_num
    have hsplit := outerExpectation_supNorm_le_truncateClass_add_tail
      hF_ne hF_meas hF_L2_one hΦ_env hX_meas hX_idem hX_law
        (t := 0) (by norm_num) n
    have htrunc_zero : outerExpectation μ (fun ξ =>
        supNormOver (truncateClass F 0)
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) = 0 := by
      have hfun : (fun ξ => supNormOver (truncateClass F 0)
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) =
          fun _ : Ξ => 0 := by
        funext ξ
        simp only [supNormOver, truncateClass, Set.mem_setOf_eq, empiricalProcess,
          empiricalAvg, abs_mul, abs_nonneg, ENNReal.ofReal_mul, iSup_exists,
          iSup_eq_zero, mul_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff,
          Nat.cast_nonneg, Real.sqrt_eq_zero, Nat.cast_eq_zero, and_imp]
        intro f g hg hfg
        subst f
        simp [clampFn, clampReal]
      rw [hfun, outerExpectation_const]
      simp
    have htail_zero : outerExpectation P (fun x => ENNReal.ofReal
        (Φ x * Set.indicator {y | (0 : ℝ) < Φ y} (1 : Ω → ℝ) x)) = 0 := by
      have htail_ae : (fun x => ENNReal.ofReal
          (Φ x * Set.indicator {y | (0 : ℝ) < Φ y} (1 : Ω → ℝ) x)) =ᵐ[P] 0 :=
        hΦ_zero.mono (fun x hx => by simp [hx])
      rw [outerExpectation_congr_ae htail_ae]
      change outerExpectation P (fun _ : Ω => 0) = 0
      rw [outerExpectation_const]
      simp
    rw [htrunc_zero, htail_zero] at hsplit
    have hlhs : outerExpectation μ (fun ξ => supNormOver F
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) = 0 := by
      simpa using hsplit
    rw [hlhs]
    exact zero_le
  have hr : 0 < r := lt_of_le_of_ne (by positivity) (Ne.symm hr0)
  by_cases hJtop : bracketingEntropyIntegral r F P = ⊤
  · rw [hJtop]
    simp [(ENNReal.ofReal_pos.mpr hc).ne']
  have hΦ_norm : eLpNorm Φ 2 P = ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_toReal hΦ_L2.eLpNorm_lt_top.ne]
  have hF_L2 : ∀ f ∈ F, eLpNorm f 2 P < ENNReal.ofReal (3 * r) := by
    intro f hf
    have hmono : eLpNorm f 2 P ≤ eLpNorm Φ 2 P :=
      eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hΦ_nn x)] using hΦ_env f hf x)
    calc
      eLpNorm f 2 P ≤ eLpNorm Φ 2 P := hmono
      _ = ENNReal.ofReal r := hΦ_norm
      _ < ENNReal.ofReal (3 * r) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  have hbr : IsEpsBracket (3 * r) (fun x => -Φ x) Φ 2 P := by
    refine ⟨fun x => by linarith [hΦ_nn x], hΦ_meas.neg, hΦ_meas,
      hΦ_L2.neg, hΦ_L2, ?_⟩
    have heq : (fun x => Φ x - -Φ x) = (2 : ℝ) • Φ := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    calc
      eLpNorm (fun x => Φ x - -Φ x) 2 P
          = ENNReal.ofReal 2 * ENNReal.ofReal r := by
            rw [heq, eLpNorm_const_smul, hΦ_norm]
            rw [Real.enorm_eq_ofReal_abs]
            norm_num
      _ = ENNReal.ofReal (2 * r) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
      _ < ENNReal.ofReal (3 * r) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  have hN_le : bracketingNumber (3 * r) F 2 P ≤ 1 := by
    unfold bracketingNumber
    exact iInf_le_of_le 1 (iInf_le_of_le
      ⟨(fun _ => fun x => -Φ x), (fun _ => Φ), (fun _ => hbr),
        fun f hf => ⟨0, fun x => by
          have hfx := hΦ_env f hf x
          exact ⟨neg_le_of_abs_le hfx, le_trans (le_abs_self _) hfx⟩⟩⟩ le_rfl)
  have hN : bracketingNumber (3 * r) F 2 P = 1 :=
    le_antisymm hN_le (one_le_bracketingNumber_of_nonempty hF_ne (3 * r))
  have hJ_scale : bracketingEntropyIntegral (3 * r) F P ≤
      3 * bracketingEntropyIntegral r F P := by
    rw [bracketingEntropyIntegral_eq_setLIntegral,
      bracketingEntropyIntegral_eq_setLIntegral]
    calc
      (∫⁻ ε in Set.Ioc (0 : ℝ) (3 * r), entropyIntegrand ε F P ∂volume)
          ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) (3 * r),
              entropyIntegrand (ε / 3) F P ∂volume :=
        setLIntegral_mono' measurableSet_Ioc (fun ε hε =>
          entropyIntegrand_antitone_eps (by linarith [hε.1]))
      _ = 3 * ∫⁻ ε in Set.Ioc (0 : ℝ) r,
              entropyIntegrand ε F P ∂volume :=
        setLIntegral_Ioc_comp_third (measurable_entropyIntegrand F P)
  have hJ_lower : ENNReal.ofReal (Real.sqrt (Real.log 2) * r) ≤
      bracketingEntropyIntegral r F P := by
    rw [bracketingEntropyIntegral_eq_setLIntegral]
    calc
      ENNReal.ofReal (Real.sqrt (Real.log 2) * r)
          = ∫⁻ _ε in Set.Ioc (0 : ℝ) r,
              ENNReal.ofReal (Real.sqrt (Real.log 2)) ∂volume := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
          ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      _ ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) r, entropyIntegrand ε F P ∂volume :=
        setLIntegral_mono' measurableSet_Ioc
          (fun ε _ => sqrt_log_two_le_entropyIntegrand hF_ne ε)
  have hδ : 0 < 3 * r := by positivity
  have hR6 := hmax Ω P Ξ μ X hX_meas hX_iindep hX_idem hX_law
    F Φ (3 * r) hδ hF_meas hF_L2 hΦ_env n
  let a : ℝ := Real.sqrt n * (3 * r)
  have ha : 0 < a := by
    dsimp only [a]
    have hn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0))
    positivity
  have hcutoff : Real.sqrt n * bracketingBookCutoff (3 * r)
      (bracketingNumber (3 * r) F 2 P) = a := by
    rw [hN, show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl,
      bracketingBookCutoff_coe]
    norm_num [a]
  rw [hcutoff] at hR6
  let tail : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal
    (Φ x * Set.indicator {y | a < Φ y} (1 : Ω → ℝ) x)
  have htail_meas : Measurable tail := by
    dsimp only [tail]
    refine Measurable.ennreal_ofReal ?_
    exact hΦ_meas.mul (Measurable.indicator measurable_const
      (measurableSet_lt measurable_const hΦ_meas))
  have htail_pt : ∀ x, tail x ≤ ENNReal.ofReal (Φ x ^ 2 / a) := by
    intro x
    dsimp only [tail]
    by_cases hx : x ∈ {y | a < Φ y}
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      apply ENNReal.ofReal_le_ofReal
      apply (le_div_iff₀ ha).2
      calc
        Φ x * a ≤ Φ x * Φ x := mul_le_mul_of_nonneg_left hx.le (hΦ_nn x)
        _ = Φ x ^ 2 := by ring
    · rw [Set.indicator_of_notMem hx, mul_zero]
      simp
  have hphi_sq : ∫ x, Φ x ^ 2 ∂P = r ^ 2 := by
    have h_int_nn : 0 ≤ ∫ x, Φ x ^ 2 ∂P := integral_nonneg (fun _ => sq_nonneg _)
    have hsqrt : Real.sqrt (∫ x, Φ x ^ 2 ∂P) = (eLpNorm Φ 2 P).toReal := by
      rw [hΦ_L2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
      have hfun : (fun x => ‖Φ x‖ ^ (2 : ℝ≥0∞).toReal) =
          fun x => Φ x ^ 2 := by
        funext x
        rw [htwo, Real.rpow_two, Real.norm_eq_abs, sq_abs]
      rw [hfun, ENNReal.toReal_ofReal (Real.rpow_nonneg h_int_nn _), htwo,
        Real.sqrt_eq_rpow]
      norm_num
    have hsqrt_eq : Real.sqrt (∫ x, Φ x ^ 2 ∂P) = r := by
      rw [hsqrt, hΦ_norm, ENNReal.toReal_ofReal hr.le]
    nlinarith [Real.sq_sqrt h_int_nn]
  have htail_outer : outerExpectation P tail ≤ ENNReal.ofReal (r ^ 2 / a) := by
    rw [outerExpectation_eq_lintegral htail_meas]
    calc
      (∫⁻ x, tail x ∂P) ≤ ∫⁻ x, ENNReal.ofReal (Φ x ^ 2 / a) ∂P :=
        lintegral_mono htail_pt
      _ = ENNReal.ofReal (∫ x, Φ x ^ 2 / a ∂P) := by
        rw [← ofReal_integral_eq_lintegral_ofReal]
        · exact (hΦ_L2.integrable_sq.div_const a)
        · exact Filter.Eventually.of_forall (fun _ => div_nonneg (sq_nonneg _) ha.le)
      _ = ENNReal.ofReal (r ^ 2 / a) := by
        congr 1
        rw [integral_div, hphi_sq]
  have htail_bound : ENNReal.ofReal (Real.sqrt n) * outerExpectation P tail ≤
      ENNReal.ofReal (r / 3) := by
    calc
      ENNReal.ofReal (Real.sqrt n) * outerExpectation P tail
          ≤ ENNReal.ofReal (Real.sqrt n) * ENNReal.ofReal (r ^ 2 / a) :=
        mul_le_mul_right htail_outer _
      _ = ENNReal.ofReal (r / 3) := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
        congr 1
        dsimp only [a]
        field_simp [Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0))]
  have htail_J : ENNReal.ofReal (Real.sqrt n) * outerExpectation P tail ≤
      bracketingEntropyIntegral r F P := by
    have hlog_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    have hsqrt_half : (1 : ℝ) / 2 ≤ Real.sqrt (Real.log 2) := by
      nlinarith [Real.sq_sqrt (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)),
        Real.sqrt_nonneg (Real.log 2)]
    have hthird : r / 3 ≤ Real.sqrt (Real.log 2) * r := by
      nlinarith
    exact htail_bound.trans ((ENNReal.ofReal_le_ofReal hthird).trans hJ_lower)
  rw [show ENNReal.ofReal (4 * c) = 4 * ENNReal.ofReal c by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]]
  calc
    outerExpectation μ (fun ξ => supNormOver F
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f))
        ≤ ENNReal.ofReal c *
            (bracketingEntropyIntegral (3 * r) F P +
              ENNReal.ofReal (Real.sqrt n) * outerExpectation P tail) := by
          simpa only [tail] using hR6
    _ ≤ ENNReal.ofReal c *
            (3 * bracketingEntropyIntegral r F P +
              bracketingEntropyIntegral r F P) := by
          exact mul_le_mul_right (add_le_add hJ_scale htail_J) _
    _ = 4 * ENNReal.ofReal c * bracketingEntropyIntegral r F P := by ring

end AsymptoticStatistics.EmpiricalProcess
