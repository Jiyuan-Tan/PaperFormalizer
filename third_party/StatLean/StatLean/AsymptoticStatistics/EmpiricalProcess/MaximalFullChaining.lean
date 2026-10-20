module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChainingAssembly
public import StatLean.AsymptoticStatistics.ForMathlib.OuterIntegration.OuterExpectation

@[expose] public section

/-!
# Tail-free chaining for a fully clamped bracketing partition

The full-class bracketing maximal inequality (vdV Lemma 19.34, pp.286--288)
uses a clamped nested partition whose head and successive links satisfy a
tail-free chaining bound.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {P : Measure Ω} {μ : Measure Ξ}
variable {F : Set (Ω → ℝ)} {Φ : Ω → ℝ} {q₀ n : ℕ} {δ t : ℝ}

/-- The structural output of the clamped full-class construction used in vdV
Lemma 19.34.  It bundles only facts constructed from finite bracket covers,
clamping, and the envelope; in particular, no field asks a caller to certify
the desired maximal inequality.

Constitutive (vdV §19.6 pp.286--287): the nested partition, its comparison
with the original class's cover counts, its clamped widths/envelopes, the
initial small-link comparison, and the first-crossing alternative are exactly
the data read by the book's head/A/B telescope. -/
structure FullClampedPartitionData
    (F : Set (Ω → ℝ)) (P : Measure Ω) (Φ : Ω → ℝ)
    (q₀ : ℕ) (δ : ℝ) (n : ℕ) (t : ℝ) where
  /-- Constitutive (vdV §19.6 p.286): nested partitions of the clamped class. -/
  partition : NestedBracketPartition (truncateClass F t) P q₀ δ
  /-- Constitutive (vdV §19.6 p.287): partition cover counts are controlled by
  the original full-class bracketing numbers at the matching dyadic scales. -/
  coverCard_original_le : ∀ {p : ℕ}, q₀ ≤ p →
    (partition.coverCard p : ℕ∞) ≤
      bracketingNumber ((1 / 2 : ℝ) ^ (p - q₀) * δ) F 2 P
  /-- Constitutive (vdV §19.6 p.286): clamping bounds every cell width by
  twice the clamp level. -/
  width_le : ∀ {q : ℕ}, q₀ ≤ q → ∀ i x, partition.Δ q i x ≤ 2 * t
  /-- Constitutive (vdV §19.6 p.286): the clamped class is nonempty in the
  nonempty branch of the general theorem. -/
  truncated_nonempty : (truncateClass F t).Nonempty
  /-- Constitutive (vdV §19.6 p.286): members used by the empirical process are
  measurable; this is inherited from the original class through clamping. -/
  truncated_measurable : ∀ f ∈ truncateClass F t, Measurable f
  /-- Constitutive (vdV §19.6 p.286): clamping preserves the strict full-class
  L² radius needed by the head estimate. -/
  truncated_L2 : ∀ f ∈ truncateClass F t,
    eLpNorm f 2 P < ENNReal.ofReal δ
  /-- Constitutive (vdV §19.6 p.286): the original envelope continues to
  dominate the clamped class. -/
  original_envelope : IsEnvelope (truncateClass F t) Φ
  /-- Constitutive (vdV §19.6 p.286): the clamp level is a constant envelope
  for the clamped class. -/
  clamp_envelope : IsEnvelope (truncateClass F t) (fun _ => t)
  /-- Constitutive (vdV §19.6 p.287): the initial partition has no more cells
  than its head cover.  Together with `coverCard_original_le`, this is the
  initial cardinality comparison used by the head estimate. -/
  initial_comparison : partition.Nq q₀ ≤ partition.coverCard q₀
  /-- Constitutive (vdV §19.6 p.287): along every member's cell chain, either
  all links remain small, or there is a first crossing and all later B-gates
  are empty.  This condition is supplied by the construction and does not
  appear among the assumptions of the public Lemma 19.34 statement. -/
  firstCrossing_tailEmpty : ∀ f (hf : f ∈ truncateClass F t) x,
    (∀ k, partition.Δ (q₀ + k) (cellChain partition hf k) x ≤
        Real.sqrt n * chainThreshold partition δ (q₀ + k)) ∨
      ∃ k,
        (∀ j < k, partition.Δ (q₀ + j) (cellChain partition hf j) x ≤
          Real.sqrt n * chainThreshold partition δ (q₀ + j)) ∧
        ¬ partition.Δ (q₀ + k) (cellChain partition hf k) x ≤
          Real.sqrt n * chainThreshold partition δ (q₀ + k) ∧
        ∀ l, k < l →
          ¬ chainB partition δ n (q₀ + l) (cellChain partition hf l) x

/-- The regularized factor-eight data for the full-class chain.

Constitutive (vdV §19.6 p.287): `base` is the
full clamped partition at scale `8 * δ` and initial index `0`;
`initial_small` and `head_visible` encode the two comparisons corresponding to
the book's `4δ ≤ 2⁻ᵠ₀ ≤ 8δ` and `2a(δ) ≤ a_q₀`. -/
structure RegularizedFullClampedPartitionData
    (F : Set (Ω → ℝ)) (P : Measure Ω) (Φ : Ω → ℝ)
    (δ : ℝ) (n : ℕ) (t : ℝ) where
  /-- Constitutive (vdV §19.6 p.287): the clamped nested
  partition is built at scale `8 * δ` with initial index `0`. -/
  base : FullClampedPartitionData F P Φ 0 (8 * δ) n t
  /-- Constitutive (vdV §19.6 p.287): every head-cell oscillation lies below
  the first regularized chaining threshold. -/
  initial_small : ∀ i x,
    base.partition.Δ 0 i x ≤
      Real.sqrt n * chainThreshold base.partition (8 * δ) 0
  /-- Constitutive (vdV §19.6 p.287): the fixed clamp level is visible to the
  head truncation at the scale-`8δ` global threshold. -/
  head_visible : |t| ≤
    Real.sqrt n * globalThreshold base.partition (8 * δ)

/-- Literal-constant form of the finite chain-level maximal inequality.  The
constant `288 = 3 * 96` is obtained directly from `finite_sup_bound_96`; in
particular, it is fixed before every probability space, class, and scale. -/
private lemma tight_chain_level_bound_288
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : ι → Ω → ℝ) (hg_meas : ∀ i, Measurable (g i))
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (hg_bdd : ∀ i ω, |g i ω| ≤
      Real.sqrt n * ε / (1 + Real.sqrt (Real.log (1 + Fintype.card ι))))
    (hg_var : ∀ i, ∫ ω, (g i ω) ^ 2 ∂P ≤ (2 * ε) ^ 2) :
    ∫⁻ ω, ENNReal.ofReal
        (⨆ i : ι, |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) ∂μ
      ≤ ENNReal.ofReal
          (288 * ε * Real.sqrt (Real.log (1 + Fintype.card ι))) := by
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hsn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hL_nn : 0 ≤ Real.log (1 + Fintype.card ι) :=
    Real.log_nonneg (by
      have hcard : (0 : ℝ) ≤ Fintype.card ι := by positivity
      linarith)
  have hsL_nn : 0 ≤ Real.sqrt (Real.log (1 + Fintype.card ι)) :=
    Real.sqrt_nonneg _
  have h1psL_pos : (0 : ℝ) < 1 + Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    linarith
  have hM_nn : 0 ≤ Real.sqrt n * ε
      / (1 + Real.sqrt (Real.log (1 + Fintype.card ι))) := by positivity
  have hσ_nn : (0 : ℝ) ≤ 2 * ε := by positivity
  have h_bnd := finite_sup_bound_96 P hX_meas hX_iindep hX_idem hX_law
    g hg_meas hM_nn hσ_nn hg_bdd hg_var n hn
  refine h_bnd.trans (ENNReal.ofReal_le_ofReal ?_)
  have hM_div_sqrt :
      Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
          * Real.log (1 + Fintype.card ι) / Real.sqrt n
        = ε * Real.log (1 + Fintype.card ι)
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι))) := by
    field_simp
  have hLog_div_le :
      Real.log (1 + Fintype.card ι)
          / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
        ≤ Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    rw [div_le_iff₀ h1psL_pos]
    have hsq : Real.sqrt (Real.log (1 + Fintype.card ι))
            * Real.sqrt (Real.log (1 + Fintype.card ι))
          = Real.log (1 + Fintype.card ι) := Real.mul_self_sqrt hL_nn
    nlinarith
  have hM_term_le :
      Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
          * Real.log (1 + Fintype.card ι) / Real.sqrt n
        ≤ ε * Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    rw [hM_div_sqrt, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hLog_div_le hε.le
  have hsum :
      Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
          * Real.log (1 + Fintype.card ι) / Real.sqrt n
        + 2 * ε * Real.sqrt (Real.log (1 + Fintype.card ι))
        ≤ 3 * ε * Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    linarith
  calc
    96 * (Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
              * Real.log (1 + Fintype.card ι) / Real.sqrt n
          + 2 * ε * Real.sqrt (Real.log (1 + Fintype.card ι)))
        ≤ 96 * (3 * ε * Real.sqrt (Real.log (1 + Fintype.card ι))) := by
          gcongr
    _ = 288 * ε * Real.sqrt (Real.log (1 + Fintype.card ι)) := by ring

set_option linter.unusedVariables false in
/-- Head representatives of a full clamped chain satisfy the coarsest dyadic
bound.  This is the head term in vdV Lemma 19.34, p.288. -/
theorem fullClamped_chain_head_dyadic_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (Ξ : Type*) [MeasurableSpace Ξ]
        (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (q₀ n : ℕ) (δ t : ℝ)
        (D : FullClampedPartitionData F P Φ q₀ δ n t)
        (X : ℕ → Ξ → Ω)
        (hX_meas : ∀ i, Measurable (X i))
        (hX_iindep : ProbabilityTheory.iIndepFun X μ)
        (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
        (hX_law : μ.map (X 0) = P) (hδ : 0 < δ),
      levelRepSup D.partition μ X (fun _ => t) δ n q₀ ≤
        ENNReal.ofReal c * (ENNReal.ofReal δ * entropyIntegrand δ F P) := by
  classical
  refine ⟨576, by norm_num, ?_⟩
  intro Ω _ P _ Ξ _ μ _ F Φ q₀ n δ t D X hX_meas hX_iindep hX_idem hX_law hδ
  cases n with
  | zero => simp [levelRepSup, empiricalProcess, empiricalAvg]
  | succ n =>
    have hn : 1 ≤ n + 1 := by omega
    let B := D.partition
    have hNq_ne : Nonempty (Fin (B.Nq q₀)) := by
      obtain ⟨f, hf⟩ := D.truncated_nonempty
      obtain ⟨i, _⟩ := B.cover (le_refl q₀) f hf
      exact ⟨i⟩
    set g : Fin (B.Nq q₀) → Ω → ℝ :=
      fun i => truncRep B (fun _ => t) δ (n + 1) q₀ i with hg_def
    have hg_meas : ∀ i, Measurable (g i) := by
      intro i
      refine (B.π_meas (le_refl q₀) i).mul ?_
      exact measurable_one.indicator (MeasurableSet.const _)
    have hcard : Fintype.card (Fin (B.Nq q₀)) = B.Nq q₀ := Fintype.card_fin _
    have hbnd := tight_chain_level_bound_288 P hX_meas hX_iindep hX_idem hX_law
      g hg_meas hδ (n + 1) hn ?_ ?_
    · have hLHS : levelRepSup B μ X (fun _ => t) δ (n + 1) q₀
          ≤ ∫⁻ ω : Ξ, ENNReal.ofReal
              (⨆ i, |empiricalProcess P (n + 1)
                (fun j : Fin (n + 1) => X j.val ω) (g i)|) ∂μ := by
        refine lintegral_mono (fun ξ => ?_)
        refine iSup_le (fun i => ?_)
        refine ENNReal.ofReal_le_ofReal ?_
        exact le_ciSup (Finite.bddAbove_range
          (fun i : Fin (B.Nq q₀) =>
            |empiricalProcess P (n + 1) (fun j : Fin (n + 1) => X j.val ξ) (g i)|)) i
      refine hLHS.trans (hbnd.trans ?_)
      have hweight_le :
          ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.Nq q₀ : ℝ))))
            ≤ entropyIntegrand δ F P := by
        have hcard_le : (B.Nq q₀ : ℕ∞) ≤ (B.coverCard q₀ : ℕ∞) := by
          exact_mod_cast D.initial_comparison
        have hcover_le : (B.coverCard q₀ : ℕ∞) ≤ bracketingNumber δ F 2 P := by
          simpa [Nat.sub_self, pow_zero, one_mul] using
            (D.coverCard_original_le (le_refl q₀))
        calc
          ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.Nq q₀ : ℝ))))
              = entropyWeight (B.Nq q₀ : ℕ∞) := (entropyWeight_coe _).symm
          _ ≤ entropyWeight (bracketingNumber δ F 2 P) :=
            entropyWeight_mono (hcard_le.trans hcover_le)
          _ = entropyIntegrand δ F P := rfl
      rw [hcard]
      rw [show 288 * δ * Real.sqrt (Real.log (1 + (B.Nq q₀ : ℝ))) =
          (288 * δ) * Real.sqrt (Real.log (1 + (B.Nq q₀ : ℝ))) by ring,
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) hδ.le),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 288)]
      calc
        ENNReal.ofReal 288 * ENNReal.ofReal δ
              * ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.Nq q₀ : ℝ))))
            ≤ ENNReal.ofReal 576 * ENNReal.ofReal δ * entropyIntegrand δ F P :=
              mul_le_mul'
                (mul_le_mul'
                  (ENNReal.ofReal_le_ofReal (by norm_num : (288 : ℝ) ≤ 576)) le_rfl)
                hweight_le
        _ = ENNReal.ofReal 576 *
              (ENNReal.ofReal δ * entropyIntegrand δ F P) := by ring
    · intro i ω
      have hπ_F : B.π q₀ i ∈ truncateClass F t :=
        B.cell_subset (le_refl q₀) i (B.π_mem (le_refl q₀) i)
      have hRHS_eq : Real.sqrt (n + 1 : ℕ) * δ
            / (1 + Real.sqrt (Real.log (1 +
                (Fintype.card (Fin (B.Nq q₀)) : ℝ))))
          = Real.sqrt (n + 1 : ℕ) * globalThreshold B δ := by
        rw [globalThreshold, hcard]
        ring
      rw [hg_def]
      simp only [truncRep]
      calc
        |B.π q₀ i ω * {y | |t| ≤ Real.sqrt (n + 1 : ℕ) * globalThreshold B δ}.indicator
            (1 : Ω → ℝ) ω|
            ≤ Real.sqrt (n + 1 : ℕ) * globalThreshold B δ := by
              by_cases hω : ω ∈ {y : Ω |
                  |t| ≤ Real.sqrt (n + 1 : ℕ) * globalThreshold B δ}
              · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
                exact (D.clamp_envelope _ hπ_F ω).trans ((le_abs_self t).trans hω)
              · rw [Set.indicator_of_notMem hω, mul_zero, abs_zero]
                rw [globalThreshold]
                positivity
        _ = Real.sqrt (n + 1 : ℕ) * δ
              / (1 + Real.sqrt (Real.log (1 +
                  (Fintype.card (Fin (B.Nq q₀)) : ℝ)))) := hRHS_eq.symm
    · intro i
      have hπ_F : B.π q₀ i ∈ truncateClass F t :=
        B.cell_subset (le_refl q₀) i (B.π_mem (le_refl q₀) i)
      have hπ_memLp : MemLp (B.π q₀ i) 2 P := by
        refine ⟨(B.π_meas (le_refl q₀) i).aestronglyMeasurable, ?_⟩
        exact lt_trans (D.truncated_L2 _ hπ_F) ENNReal.ofReal_lt_top
      have hπ_sq_le : ∫ ω, (B.π q₀ i ω) ^ 2 ∂P ≤ δ ^ 2 := by
        have hnn : 0 ≤ ∫ ω, (B.π q₀ i ω) ^ 2 ∂P :=
          integral_nonneg (fun _ => sq_nonneg _)
        have hsqrt_eq : Real.sqrt (∫ ω, (B.π q₀ i ω) ^ 2 ∂P)
            = (eLpNorm (B.π q₀ i) 2 P).toReal := by
          rw [hπ_memLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
          have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
          have h_int_eq :
              (fun ω => ‖B.π q₀ i ω‖ ^ (2 : ℝ≥0∞).toReal)
                = (fun ω => B.π q₀ i ω ^ 2) := by
            funext ω
            rw [h2, Real.rpow_two, Real.norm_eq_abs, sq_abs]
          rw [h_int_eq, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), h2,
            Real.sqrt_eq_rpow]
          norm_num
        have hsqrt_lt : Real.sqrt (∫ ω, (B.π q₀ i ω) ^ 2 ∂P) < δ := by
          rw [hsqrt_eq]
          calc
            (eLpNorm (B.π q₀ i) 2 P).toReal
                < (ENNReal.ofReal δ).toReal :=
                  ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top
                    (D.truncated_L2 _ hπ_F)
            _ = δ := ENNReal.toReal_ofReal hδ.le
        nlinarith [Real.sq_sqrt hnn,
          Real.sqrt_nonneg (∫ ω, (B.π q₀ i ω) ^ 2 ∂P)]
      have hgsq_le : ∫ ω, (g i ω) ^ 2 ∂P
          ≤ ∫ ω, (B.π q₀ i ω) ^ 2 ∂P := by
        refine integral_mono_of_nonneg
          (Eventually.of_forall (fun ω => sq_nonneg _)) hπ_memLp.integrable_sq ?_
        refine Eventually.of_forall (fun ω => ?_)
        rw [hg_def]
        simp only [truncRep]
        by_cases hω : ω ∈ {y : Ω | |t| ≤ Real.sqrt (n + 1 : ℕ) * globalThreshold B δ}
        · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
        · rw [Set.indicator_of_notMem hω, mul_zero]
          simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
            (sq_nonneg (B.π q₀ i ω))
      refine hgsq_le.trans (hπ_sq_le.trans ?_)
      nlinarith [hδ.le]

/-- Dyadic rearrangement with a one-step look-ahead, used by the A-series. -/
private lemma fullClamped_tsum_pow_half_sum_Icc_succ_le (a : ℕ → ℝ≥0∞) :
    (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 (q + 1), a p))
      ≤ 4 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p := by
  have hsplit : ∀ q : ℕ,
      (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 (q + 1), a p)
        = (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 q, a p)
          + (2⁻¹ : ℝ≥0∞) ^ q * a (q + 1) := by
    intro q
    rw [Finset.sum_Icc_succ_top (Nat.zero_le _), mul_add]
  calc
    (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 (q + 1), a p))
        = ∑' q : ℕ, ((2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 q, a p)
            + (2⁻¹ : ℝ≥0∞) ^ q * a (q + 1)) := tsum_congr hsplit
    _ = (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 q, a p))
          + (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * a (q + 1)) := by
            rw [ENNReal.tsum_add]
    _ ≤ 2 * (∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p)
          + 2 * (∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p) := by
      refine add_le_add
        (AsymptoticStatistics.ForMathlib.ENNReal.tsum_pow_half_sum_Icc_le 0 a) ?_
      have hreidx :
          (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ (q + 1) * a (q + 1))
            ≤ ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p :=
        ENNReal.tsum_comp_le_tsum_of_injective
          (fun _ _ h => by simpa using h)
          (fun p => (2⁻¹ : ℝ≥0∞) ^ p * a p)
      have hhalf : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      calc
        (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * a (q + 1))
            = ∑' q : ℕ, 2 * ((2⁻¹ : ℝ≥0∞) ^ (q + 1) * a (q + 1)) := by
              refine tsum_congr fun q => ?_
              have hpow : (2⁻¹ : ℝ≥0∞) ^ q = 2 * (2⁻¹ : ℝ≥0∞) ^ (q + 1) := by
                rw [pow_succ, ← mul_assoc, mul_comm (2 : ℝ≥0∞) _, mul_assoc,
                  hhalf, mul_one]
              rw [hpow, mul_assoc]
        _ = 2 * (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ (q + 1) * a (q + 1)) := by
              rw [ENNReal.tsum_mul_left]
        _ ≤ 2 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p := by gcongr
    _ = 4 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p := by ring

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
/-- The A-link series of the full clamped chain is bounded by the dyadic
bracketing-entropy series (vdV Lemma 19.34, p.288). -/
theorem fullClamped_chain_A_dyadic_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (Ξ : Type*) [MeasurableSpace Ξ]
        (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (q₀ n : ℕ) (δ t : ℝ)
        (D : FullClampedPartitionData F P Φ q₀ δ n t)
        (X : ℕ → Ξ → Ω)
        (hX_meas : ∀ i, Measurable (X i))
        (hX_iindep : ProbabilityTheory.iIndepFun X μ)
        (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
        (hX_law : μ.map (X 0) = P) (hδ : 0 < δ),
      (∑' k : ℕ, levelJumpSup D.partition μ X δ n (Nat.le_add_right q₀ k)) ≤
        ENNReal.ofReal c *
          (∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ) *
            entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P) := by
  classical
  refine ⟨4 * 288, by norm_num, ?_⟩
  intro Ω _ P _ Ξ _ μ _ F Φ q₀ n δ t D X hX_meas hX_iindep hX_idem hX_law hδ
  cases n with
  | zero => simp [levelJumpSup, empiricalProcess, empiricalAvg]
  | succ n =>
    let B := D.partition
    set K : ℝ := 288 with hK_def
    have hK_pos : 0 < K := by rw [hK_def]; norm_num
    have hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i) := B.π_meas
    have hF_ne := D.truncated_nonempty
    have hn : 1 ≤ n + 1 := by omega
    -- Abbreviation: the (offset-coordinate) per-level entropy weight feeding the series.
    set a : ℕ → ℝ≥0∞ := fun k => entropyIntegrand ((1/2 : ℝ)^k * δ) F P with ha_def
    -- ===== Per-level bound =====
    -- For each level index `q` (book level `m = q₀ + q`), the jump-sup contribution
    -- is dominated by the leaf bound, whose entropy weight `√log(1 + N_{m+1})` collapses
    -- (via `jump_card_le` + `Real.sqrt_log_prod_le_sum_one_add` + `coverCard_le`) to the
    -- offset-range sum `∑_{k ∈ Icc 0 (q+1)} a k`.
    have hlevel : ∀ q : ℕ,
        levelJumpSup B μ X δ (n + 1) (Nat.le_add_right q₀ q)
          ≤ ENNReal.ofReal K
              * (ENNReal.ofReal ((1/2 : ℝ)^q * δ) * (∑ k ∈ Finset.Icc 0 (q + 1), a k)) := by
      intro q
      set m : ℕ := q₀ + q with hm_def
      have hm : q₀ ≤ m := Nat.le_add_right q₀ q
      have hmq : m - q₀ = q := by omega
      -- A nonempty level-`(m+1)` cell index.
      have hNq_ne : Nonempty (Fin (B.Nq (m + 1))) := by
        obtain ⟨f, hf⟩ := hF_ne
        obtain ⟨i, _⟩ := B.cover (le_trans hm (Nat.le_succ m)) f hf
        exact ⟨i⟩
      -- The A-gated jump family.
      set g : Fin (B.Nq (m + 1)) → Ω → ℝ := fun i => truncJump B δ (n + 1) hm i with hg_def
      -- The A-set `{x | chainA B δ (n + 1) m (parent i) x}` is, for
      -- each cell index, a countable intersection (over levels `p ≤ m`) of the
      -- single-cell sublevel sets `{x | Δ_p (ancestor) x ≤ √(n + 1)·a_p}` (the `∀ j` layer is
      -- gone; each `p` contributes ONE cell, the parent's level-`p` ancestor).
      have hA_meas : ∀ i : Fin (B.Nq (m + 1)),
          MeasurableSet {x | chainA B δ (n + 1) m (B.parent hm i) x} := by
        intro i
        have hset : {x | chainA B δ (n + 1) m (B.parent hm i) x}
            = ⋂ (p : ℕ) (hp₀ : q₀ ≤ p) (hpq : p ≤ m),
                {x | B.Δ p (B.ancestor (le_trans hp₀ hpq) (B.parent hm i) p hp₀ hpq) x
                    ≤ Real.sqrt (n + 1 : ℕ) * chainThreshold B δ p} := by
          ext x; simp only [chainA, Set.mem_setOf_eq, Set.mem_iInter]
        rw [hset]
        refine MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hp₀ =>
          MeasurableSet.iInter (fun hpq => ?_)))
        exact measurableSet_le (B.Δ_meas hp₀ _) measurable_const
      have hg_meas : ∀ i, Measurable (g i) := by
        intro i
        refine (B.jump_measurable hπ_meas hm i).mul ?_
        exact measurable_one.indicator (hA_meas i)
      have hcard : Fintype.card (Fin (B.Nq (m + 1))) = B.Nq (m + 1) := Fintype.card_fin _
      -- The leaf threshold matches `chainThreshold B δ m` exactly (card `N_{m+1}`).
      have hthr_eq :
          Real.sqrt (n + 1 : ℕ) * ((1/2 : ℝ)^q * δ)
              / (1 + Real.sqrt (Real.log (1 + (Fintype.card (Fin (B.Nq (m + 1))) : ℝ))))
            = Real.sqrt (n + 1 : ℕ) * chainThreshold B δ m := by
        rw [chainThreshold, hcard, hmq]
        ring
      -- Apply the uniform leaf with scale `ε = (1/2)^q·δ`.
      have hbnd := tight_chain_level_bound_288 P hX_meas hX_iindep hX_idem hX_law
        g hg_meas (ε := (1/2 : ℝ)^q * δ) (by positivity) (n + 1) hn ?_ ?_
      · -- Bridge `levelJumpSup` to the leaf LHS, then collapse the leaf RHS.
        have hLHS : levelJumpSup B μ X δ (n + 1) (Nat.le_add_right q₀ q)
            ≤ ∫⁻ ω : Ξ,
                ENNReal.ofReal
                  (⨆ i, |empiricalProcess P (n + 1) (fun j : Fin (n + 1) => X j.val ω) (g i)|) ∂μ := by
          refine lintegral_mono (fun ξ => ?_)
          refine iSup_le (fun i => ?_)
          refine ENNReal.ofReal_le_ofReal ?_
          exact le_ciSup (Finite.bddAbove_range
            (fun i : Fin (B.Nq (m + 1)) =>
              |empiricalProcess P (n + 1) (fun j : Fin (n + 1) => X j.val ξ) (g i)|)) i
        refine hLHS.trans (hbnd.trans ?_)
        -- Collapse `√(log(1 + N_{m+1}))` to `∑_{k ∈ Icc 0 (q+1)} a k`.
        have hweight_le :
            ENNReal.ofReal (Real.sqrt (Real.log (1 + (Fintype.card (Fin (B.Nq (m + 1))) : ℝ))))
              ≤ ∑ k ∈ Finset.Icc 0 (q + 1), a k := by
          rw [hcard]
          -- `N_{m+1} ≤ ∏_{p ∈ Icc q₀ (m+1)} coverCard p` (`jump_card_le`).
          have hcard_prod :
              (B.Nq (m + 1) : ℝ) ≤ ∏ p ∈ Finset.Icc q₀ (m + 1), (B.coverCard p : ℝ) := by
            have h := B.jump_card_le (q := m) (le_trans hm (Nat.le_succ m))
            calc (B.Nq (m + 1) : ℝ)
                ≤ ((∏ p ∈ Finset.Icc q₀ (m + 1), B.coverCard p : ℕ) : ℝ) := by exact_mod_cast h
              _ = ∏ p ∈ Finset.Icc q₀ (m + 1), (B.coverCard p : ℝ) := by push_cast; rfl
          have hIcc_ne : (Finset.Icc q₀ (m + 1)).Nonempty :=
            ⟨q₀, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
          -- `√(log(1+N)) ≤ √(log(1+∏)) ≤ ∑_p √(log(1+coverCard p))`.
          have hsalvage :
              Real.sqrt (Real.log (1 + (B.Nq (m + 1) : ℝ)))
                ≤ ∑ p ∈ Finset.Icc q₀ (m + 1), Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))) := by
            refine le_trans (Real.sqrt_le_sqrt (Real.log_le_log (by positivity) ?_))
              (AsymptoticStatistics.ForMathlib.Real.sqrt_log_prod_le_sum_one_add hIcc_ne
                (fun p => B.coverCard p))
            have : (0 : ℝ) ≤ ∏ p ∈ Finset.Icc q₀ (m + 1), (B.coverCard p : ℝ) :=
              Finset.prod_nonneg (fun p _ => Nat.cast_nonneg _)
            linarith [hcard_prod]
          -- Lift to `ℝ≥0∞`, distribute the sum, and dominate each term by `a (p - q₀)`.
          calc ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.Nq (m + 1) : ℝ))))
              ≤ ENNReal.ofReal
                  (∑ p ∈ Finset.Icc q₀ (m + 1), Real.sqrt (Real.log (1 + (B.coverCard p : ℝ)))) :=
                ENNReal.ofReal_le_ofReal hsalvage
            _ = ∑ p ∈ Finset.Icc q₀ (m + 1),
                  ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ)))) := by
                rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => Real.sqrt_nonneg _)]
            _ ≤ ∑ p ∈ Finset.Icc q₀ (m + 1), a (p - q₀) := by
                -- Term-wise: `entropyWeight (coverCard p) ≤ entropyIntegrand ((1/2)^{p-q₀}·δ)`.
                refine Finset.sum_le_sum (fun p hp => ?_)
                have hqp : q₀ ≤ p := (Finset.mem_Icc.mp hp).1
                have hcc_le :
                    (B.coverCard p : ℕ∞)
                      ≤ bracketingNumber ((1/2 : ℝ)^(p - q₀) * δ) F 2 P := by
                  exact D.coverCard_original_le hqp
                calc ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))))
                    = entropyWeight (B.coverCard p : ℕ∞) := (entropyWeight_coe _).symm
                  _ ≤ entropyWeight (bracketingNumber ((1/2 : ℝ)^(p - q₀) * δ) F 2 P) :=
                      entropyWeight_mono hcc_le
                  _ = a (p - q₀) := rfl
            _ = ∑ k ∈ Finset.Icc 0 (q + 1), a k := by
                -- Reindex `Icc q₀ (m+1)` to `Icc 0 (q+1)` by `p ↦ p - q₀` (`k ↦ k + q₀`).
                refine Finset.sum_nbij' (fun p => p - q₀) (fun k => k + q₀) ?_ ?_ ?_ ?_ ?_
                · intro p hp
                  simp only [hm_def, Finset.mem_Icc] at hp ⊢; omega
                · intro k hk
                  simp only [hm_def, Finset.mem_Icc] at hk ⊢; omega
                · intro p hp
                  simp only [hm_def, Finset.mem_Icc] at hp ⊢; omega
                · intro k hk
                  simp only [Finset.mem_Icc] at hk ⊢; omega
                · intro p _; rfl
        -- Assemble: `ofReal(K·ε·w) ≤ ofReal K · (ofReal ε · ∑ a)`.
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]
        gcongr
      · -- hg_bdd : `|truncJump i ω| ≤ √(n + 1)·chainThreshold B δ m`.
        intro i ω
        rw [hthr_eq, hg_def]
        simp only [truncJump]
        by_cases hω : ω ∈ {y | chainA B δ (n + 1) m (B.parent hm i) y}
        · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
          -- Per-ancestor gate: `hω` at `p = m` pins the parent's level-`m` ancestor,
          -- which is the parent itself (`ancestor_self`).
          have hanc := hω m hm le_rfl
          rw [B.ancestor_self hm (B.parent hm i)] at hanc
          calc |B.jump hm i ω| ≤ B.Δ m (B.parent hm i) ω := B.jump_abs_le hm i ω
            _ ≤ Real.sqrt (n + 1 : ℕ) * chainThreshold B δ m := hanc
        · rw [Set.indicator_of_notMem hω, mul_zero, abs_zero]
          have : 0 ≤ Real.sqrt (n + 1 : ℕ) * chainThreshold B δ m := by
            refine mul_nonneg (Real.sqrt_nonneg _) ?_
            rw [chainThreshold]; positivity
          linarith
      · -- hg_var : `∫ (g i)² ≤ (2·ε)²`.
        intro i
        have hjump_memLp : MemLp (B.jump hm i) 2 P := by
          refine ⟨(B.jump_measurable hπ_meas hm i).aestronglyMeasurable, ?_⟩
          exact lt_of_le_of_lt (B.jump_L2_le hm i) ENNReal.ofReal_lt_top
        -- `∫ (jump)² ≤ (δ·(1/2)^{m-q₀})²` from `‖jump‖_{P,2} ≤ δ·(1/2)^{m-q₀}`.
        have hjump_sq_le :
            ∫ ω, (B.jump hm i ω) ^ 2 ∂P ≤ (δ * (1/2 : ℝ)^(m - q₀)) ^ 2 := by
          have hnn : 0 ≤ ∫ ω, (B.jump hm i ω) ^ 2 ∂P :=
            MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
          have hC_nn : 0 ≤ δ * (1/2 : ℝ)^(m - q₀) := by positivity
          have hsqrt_eq : Real.sqrt (∫ ω, (B.jump hm i ω) ^ 2 ∂P)
              = (eLpNorm (B.jump hm i) 2 P).toReal := by
            rw [hjump_memLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
            have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
            have h_int_eq :
                (fun ω => ‖B.jump hm i ω‖ ^ (2 : ℝ≥0∞).toReal)
                  = (fun ω => B.jump hm i ω ^ 2) := by
              funext ω; rw [h2, Real.rpow_two, Real.norm_eq_abs, sq_abs]
            rw [h_int_eq, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), h2,
              Real.sqrt_eq_rpow]
            norm_num
          have hsqrt_le : Real.sqrt (∫ ω, (B.jump hm i ω) ^ 2 ∂P) ≤ δ * (1/2 : ℝ)^(m - q₀) := by
            rw [hsqrt_eq]
            calc (eLpNorm (B.jump hm i) 2 P).toReal
                ≤ (ENNReal.ofReal (δ * (1/2 : ℝ)^(m - q₀))).toReal :=
                  ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne (B.jump_L2_le hm i)
              _ = δ * (1/2 : ℝ)^(m - q₀) := ENNReal.toReal_ofReal hC_nn
          nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ ω, (B.jump hm i ω) ^ 2 ∂P)]
        -- `∫ (g i)² ≤ ∫ (jump)²` (indicator ≤ 1), chain through `(δ·(1/2)^{m-q₀})² ≤ (2ε)²`.
        have hgsq_le : ∫ ω, (g i ω) ^ 2 ∂P ≤ ∫ ω, (B.jump hm i ω) ^ 2 ∂P := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Eventually.of_forall (fun ω => sq_nonneg _)) (hjump_memLp.integrable_sq) ?_
          refine Eventually.of_forall (fun ω => ?_)
          rw [hg_def]
          simp only [truncJump]
          rcases Set.indicator_eq_zero_or_self {y | chainA B δ (n + 1) m (B.parent hm i) y}
              (1 : Ω → ℝ) ω with h0 | h1
          · rw [h0, mul_zero]; simpa using sq_nonneg (B.jump hm i ω)
          · rw [h1, Pi.one_apply, mul_one]
        refine hgsq_le.trans (hjump_sq_le.trans ?_)
        -- `(δ·(1/2)^{m-q₀})² ≤ (2·((1/2)^q·δ))²`: `m - q₀ = q`.
        rw [hmq]
        nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) q, hδ.le,
          sq_nonneg ((1/2 : ℝ)^q * δ)]
    -- ===== Sum the per-level bounds and apply the dyadic rearrangement =====
    -- The recurring conversion `ofReal((1/2)^q·δ) = (2⁻¹)^q · ofReal δ`.
    have hofReal_half : ENNReal.ofReal (1/2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
      rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
        ENNReal.ofReal_ofNat]
    have hpow_eq : ∀ q : ℕ,
        ENNReal.ofReal ((1/2 : ℝ)^q * δ) = (2⁻¹ : ℝ≥0∞)^q * ENNReal.ofReal δ := by
      intro q
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), hofReal_half]
    -- Abbreviation `w k = ofReal δ · a k` matching the dyadic-rearrangement input.
    set w : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal δ * a k with hw_def
    calc (∑' q : ℕ, levelJumpSup B μ X δ (n + 1) (Nat.le_add_right q₀ q))
        ≤ ∑' q : ℕ, ENNReal.ofReal K
            * (ENNReal.ofReal ((1/2 : ℝ)^q * δ) * (∑ k ∈ Finset.Icc 0 (q + 1), a k)) :=
          ENNReal.tsum_le_tsum hlevel
      _ = ENNReal.ofReal K
            * ∑' q : ℕ, (2⁻¹ : ℝ≥0∞)^q * (∑ k ∈ Finset.Icc 0 (q + 1), w k) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun q => ?_
          rw [hpow_eq q, hw_def, ← Finset.mul_sum]
          ring
      _ ≤ ENNReal.ofReal K * (4 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞)^p * w p) := by
          gcongr
          exact fullClamped_tsum_pow_half_sum_Icc_succ_le w
      _ = ENNReal.ofReal (4 * K)
            * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                * entropyIntegrand ((1/2 : ℝ)^q * δ) F P) := by
          have hw_series :
              (∑' p : ℕ, (2⁻¹ : ℝ≥0∞)^p * w p)
                = ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                    * entropyIntegrand ((1/2 : ℝ)^q * δ) F P := by
            refine tsum_congr fun q => ?_
            rw [hpow_eq q, hw_def, ha_def]
            ring
          rw [hw_series, hK_def]
          norm_num
          ring

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
/-- The summed B-link oscillations of the full clamped chain satisfy the
dyadic entropy-series bound.  Summation is essential: a single level carries
the cumulative prefix entropy from the nested partition (vdV Lemma 19.34,
p.287). -/
theorem fullClamped_chain_Bseries_dyadic_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (Ξ : Type*) [MeasurableSpace Ξ]
        (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (q₀ n : ℕ) (δ t : ℝ)
        (D : FullClampedPartitionData F P Φ q₀ δ n t)
        (X : ℕ → Ξ → Ω)
        (hX_meas : ∀ i, Measurable (X i))
        (hX_iindep : ProbabilityTheory.iIndepFun X μ)
        (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
        (hX_law : μ.map (X 0) = P) (hδ : 0 < δ),
      (∑' k : ℕ, levelOscSup D.partition μ X δ n (q₀ + k)) ≤
        ENNReal.ofReal c *
          (∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ) *
            entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P) := by
  classical
  refine ⟨4 * 288, by norm_num, ?_⟩
  intro Ω _ P _ Ξ _ μ _ F Φ q₀ n δ t D X hX_meas hX_iindep hX_idem hX_law hδ
  cases n with
  | zero => simp [levelOscSup, empiricalProcess, empiricalAvg]
  | succ n =>
    let B := D.partition
    set K : ℝ := 288 with hK_def
    have hK_pos : 0 < K := by rw [hK_def]; norm_num
    have hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i) := B.π_meas
    have hF_ne := D.truncated_nonempty
    have hn : 1 ≤ n + 1 := by omega
    refine (ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective q₀)
      (levelOscSup B μ X δ (n + 1))).trans ?_
    -- Series-coefficient family `b p = ofReal δ · entropyIntegrand((1/2)^{p−q₀}δ)`
    -- for `p ≥ q₀`, else `0`.  After the dyadic reindex `p = q₀ + j` it becomes the
    -- series term exactly (no antitonicity slack needed).
    set b : ℕ → ℝ≥0∞ := fun p =>
      if q₀ ≤ p then
        ENNReal.ofReal δ * entropyIntegrand ((1/2 : ℝ) ^ (p - q₀) * δ) F P
      else 0 with hb_def
    -- A nonempty cell index at any level `q ≥ q₀` (the finite-class supremum needs it).
    have hNq_ne : ∀ {q : ℕ}, q₀ ≤ q → Nonempty (Fin (B.Nq q)) := by
      intro q hq
      obtain ⟨f, hf⟩ := hF_ne
      obtain ⟨i, _⟩ := B.cover hq f hf
      exact ⟨i⟩
    -- Numerical preliminaries.
    have hn_pos_nat : 0 < (n + 1) := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hn_pos : (0 : ℝ) < ((n + 1) : ℝ) := by exact_mod_cast hn_pos_nat
    have hsn_nn : (0 : ℝ) ≤ Real.sqrt (n + 1 : ℕ) := Real.sqrt_nonneg _
    -- `(2⁻¹ : ℝ≥0∞)^k = ofReal((1/2)^k)` (reused throughout the dyadic algebra).
    have hofpow : ∀ k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k = ENNReal.ofReal ((1/2 : ℝ) ^ k) := by
      intro k
      rw [ENNReal.ofReal_pow (by norm_num), show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    -- =====================================================================
    -- STEP 1 — Per-level bound.
    -- For `q ≤ q₀` the summand vanishes (`chainB` has the false `q₀ < q` conjunct);
    -- for `q > q₀` the uniform leaf at scale `ε_q = (1/2)^{q−q₀−1}·δ` discharges it,
    -- and the cardinality `√log(1+N_q)` collapses to `∑_{p∈Icc q₀ q} b p` (salvage).
    -- =====================================================================
    have hlevel : ∀ q : ℕ,
        levelOscSup B μ X δ (n + 1) q
          ≤ ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1))
              * ((2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc q₀ q, b p)) := by
      intro q
      by_cases hq0q : q₀ < q
      · -- `q > q₀`: the genuine per-level maximal inequality.  Write `q = m + 1` with
        -- `q₀ ≤ m` to make the parent level `m = q − 1` a syntactic predecessor (no casts).
        obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos
          (lt_of_le_of_lt q₀.zero_le hq0q)).symm⟩
        have hq0_le : q₀ ≤ m + 1 := le_of_lt hq0q
        have hq1_le : q₀ ≤ m := Nat.lt_succ_iff.mp hq0q
        have hNq_ne_q : Nonempty (Fin (B.Nq (m + 1))) := hNq_ne hq0_le
        -- The level-`(m+1)` B-gated oscillation family.
        set g : Fin (B.Nq (m + 1)) → Ω → ℝ := fun i => truncOsc B δ (n + 1) (m + 1) i with hg_def
        -- Measurability of `{x | chainB …}` (inlined; under the per-ancestor gate each
        -- level `p < m+1` contributes ONE cell, `f`'s level-`p` ancestor, not all `∀ j`).
        have hchainB_meas : ∀ i : Fin (B.Nq (m + 1)),
            MeasurableSet {x | chainB B δ (n + 1) (m + 1) i x} := by
          intro i
          have hset : {x | chainB B δ (n + 1) (m + 1) i x}
              = {_x : Ω | q₀ < m + 1}
                ∩ ((⋂ (p : ℕ) (hp₀ : q₀ ≤ p) (hpq : p < m + 1),
                      {x | B.Δ p (B.ancestor (le_of_lt (lt_of_le_of_lt hp₀ hpq)) i p hp₀
                              (le_of_lt hpq)) x
                          ≤ Real.sqrt (n + 1 : ℕ) * chainThreshold B δ p})
                  ∩ {x | Real.sqrt (n + 1 : ℕ) * chainThreshold B δ (m + 1) < B.Δ (m + 1) i x}) := by
            ext x
            simp only [chainB, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
          rw [hset]
          refine MeasurableSet.inter (MeasurableSet.const _) ?_
          refine MeasurableSet.inter ?_ (measurableSet_lt measurable_const (B.Δ_meas hq0_le i))
          refine MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hp₀ =>
            MeasurableSet.iInter (fun hpq => ?_)))
          exact measurableSet_le (B.Δ_meas hp₀ _) measurable_const
        -- Measurability of each `g i`.
        have hg_meas : ∀ i, Measurable (g i) := by
          intro i
          rw [hg_def]
          refine (B.Δ_meas hq0_le i).mul ?_
          exact measurable_one.indicator (hchainB_meas i)
        -- Scale `ε = (1/2)^{(m+1)−q₀−1}·δ = (1/2)^{m−q₀}·δ`.
        set ε : ℝ := (1/2 : ℝ) ^ (m - q₀) * δ with hε_def
        have hε_pos : 0 < ε := by rw [hε_def]; positivity
        -- card = `N_{m+1}`.
        have hcard : Fintype.card (Fin (B.Nq (m + 1))) = B.Nq (m + 1) := Fintype.card_fin _
        -- Apply the uniform leaf.
        have hbnd := tight_chain_level_bound_288 P hX_meas hX_iindep hX_idem hX_law
          g hg_meas (ε := ε) hε_pos (n + 1) hn ?_ ?_
        · -- Bridge `levelOscSup` to the leaf LHS, then collapse the RHS.
          have hLHS : levelOscSup B μ X δ (n + 1) (m + 1)
              ≤ ∫⁻ ω : Ξ, ENNReal.ofReal
                  (⨆ i, |empiricalProcess P (n + 1) (fun j : Fin (n + 1) => X j.val ω) (g i)|) ∂μ := by
            refine lintegral_mono (fun ξ => ?_)
            refine iSup_le (fun i => ?_)
            refine ENNReal.ofReal_le_ofReal ?_
            exact le_ciSup (Finite.bddAbove_range
              (fun i : Fin (B.Nq (m + 1)) =>
                |empiricalProcess P (n + 1) (fun j : Fin (n + 1) => X j.val ξ) (g i)|)) i
          refine hLHS.trans (hbnd.trans ?_)
          -- Leaf RHS = `ofReal(K·ε·√log(1+N_{m+1}))`.
          rw [hcard]
          -- `√log(1+N_{m+1}) ≤ ∑_{p∈Icc q₀ (m+1)} √log(1+coverCard p)` (salvage).
          have hsalvage :
              Real.sqrt (Real.log (1 + (B.Nq (m + 1) : ℝ)))
                ≤ ∑ p ∈ Finset.Icc q₀ (m + 1), Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))) := by
            have hcardle : (B.Nq (m + 1) : ℝ) ≤ ∏ p ∈ Finset.Icc q₀ (m + 1), (B.coverCard p : ℝ) := by
              have h := B.card_le hq0_le
              calc (B.Nq (m + 1) : ℝ) ≤ ((∏ p ∈ Finset.Icc q₀ (m + 1), B.coverCard p : ℕ) : ℝ) := by
                    exact_mod_cast h
                _ = ∏ p ∈ Finset.Icc q₀ (m + 1), (B.coverCard p : ℝ) := by push_cast; rfl
            have hle1 : 1 + (B.Nq (m + 1) : ℝ)
                ≤ 1 + ∏ p ∈ Finset.Icc q₀ (m + 1), (B.coverCard p : ℝ) := by linarith
            have hpos1 : (0 : ℝ) < 1 + (B.Nq (m + 1) : ℝ) := by positivity
            refine le_trans (Real.sqrt_le_sqrt (Real.log_le_log hpos1 hle1)) ?_
            exact AsymptoticStatistics.ForMathlib.Real.sqrt_log_prod_le_sum_one_add
              ⟨m + 1, Finset.mem_Icc.mpr ⟨hq0_le, le_rfl⟩⟩ _
          -- `ofReal(K·ε·√log) ≤ ofReal(K·ε)·∑ ofReal(√log(coverCard p))`.
          have hstep1 :
              ENNReal.ofReal (K * ε * Real.sqrt (Real.log (1 + (B.Nq (m + 1) : ℝ))))
                ≤ ENNReal.ofReal (K * ε)
                    * ∑ p ∈ Finset.Icc q₀ (m + 1),
                        ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ)))) := by
            rw [ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.sqrt_nonneg _)]
            gcongr
          refine hstep1.trans ?_
          -- `ofReal(√log(1+coverCard p)) = entropyWeight(coverCard p) ≤ entropyIntegrand`.
          have hcover_term : ∀ p ∈ Finset.Icc q₀ (m + 1),
              ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))))
                ≤ entropyIntegrand ((1/2 : ℝ) ^ (p - q₀) * δ) F P := by
            intro p hp
            obtain ⟨hpq0, _⟩ := Finset.mem_Icc.mp hp
            have hco := D.coverCard_original_le hpq0
            calc ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))))
                = entropyWeight (B.coverCard p : ℕ∞) := (entropyWeight_coe _).symm
              _ ≤ entropyWeight (bracketingNumber ((1/2 : ℝ) ^ (p - q₀) * δ) F 2 P) :=
                  entropyWeight_mono hco
              _ = entropyIntegrand ((1/2 : ℝ) ^ (p - q₀) * δ) F P := rfl
          -- The dyadic identity `ofReal(K·ε) = ofReal(K·2^{q₀+1}) · (2⁻¹)^{m+1} · ofReal δ`.
          have hKε_eq :
              ENNReal.ofReal (K * ε)
                = ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1)) * (2⁻¹ : ℝ≥0∞) ^ (m + 1)
                    * ENNReal.ofReal δ := by
            have hpoweq : (1/2 : ℝ) ^ (m - q₀) = (2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (m + 1) := by
              have hsum : (q₀ + 1) + (m - q₀) = m + 1 := by omega
              have hsplit : (1/2 : ℝ) ^ (m + 1)
                  = (1/2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (m - q₀) := by
                rw [← pow_add, hsum]
              have hprod : (2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (q₀ + 1) = 1 := by
                rw [← mul_pow]; norm_num
              calc (1/2 : ℝ) ^ (m - q₀)
                  = 1 * (1/2 : ℝ) ^ (m - q₀) := (one_mul _).symm
                _ = ((2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (q₀ + 1)) * (1/2 : ℝ) ^ (m - q₀) := by
                    rw [hprod]
                _ = (2 : ℝ) ^ (q₀ + 1) * ((1/2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (m - q₀)) := by ring
                _ = (2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (m + 1) := by rw [← hsplit]
            have hexp : K * ε = K * (2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (m + 1) * δ := by
              rw [hε_def, hpoweq]; ring
            rw [hexp, hofpow (m + 1),
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          -- Combine the estimates at this level.
          rw [hKε_eq]
          -- `∑ b p = ofReal δ · ∑ entropyIntegrand` (each `p ∈ Icc` has `q₀ ≤ p`).
          have hb_sum :
              (∑ p ∈ Finset.Icc q₀ (m + 1), b p)
                = ENNReal.ofReal δ
                    * ∑ p ∈ Finset.Icc q₀ (m + 1),
                        entropyIntegrand ((1/2 : ℝ) ^ (p - q₀) * δ) F P := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun p hp => ?_)
            obtain ⟨hpq0, _⟩ := Finset.mem_Icc.mp hp
            rw [hb_def]
            simp only [if_pos hpq0]
          calc ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1)) * (2⁻¹ : ℝ≥0∞) ^ (m + 1)
                  * ENNReal.ofReal δ
                  * ∑ p ∈ Finset.Icc q₀ (m + 1),
                      ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))))
              ≤ ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1)) * (2⁻¹ : ℝ≥0∞) ^ (m + 1)
                  * ENNReal.ofReal δ
                  * ∑ p ∈ Finset.Icc q₀ (m + 1),
                      entropyIntegrand ((1/2 : ℝ) ^ (p - q₀) * δ) F P := by
                  gcongr with p hp
                  exact hcover_term p hp
            _ = ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1)) * ((2⁻¹ : ℝ≥0∞) ^ (m + 1)
                  * (∑ p ∈ Finset.Icc q₀ (m + 1), b p)) := by
                  rw [hb_sum]; ring
        · -- hg_bdd : `|g i ω| ≤ √(n + 1)·ε / (1 + √log(1+N_{m+1}))`.
          -- On `{chainB …}`, `Δ_{m+1} i ≤ Δ_m(parent) ≤ √(n + 1)·chainThreshold m`, and
          -- `chainThreshold m = (1/2)^{m−q₀}·δ / (1+√log(1+N_{m+1}))` = `ε / (…)`.
          intro i ω
          rw [hg_def]
          simp only [truncOsc]
          -- the RHS the leaf wants, in `chainThreshold m` form.
          have hthr_eq : Real.sqrt (n + 1 : ℕ) * ε
                / (1 + Real.sqrt (Real.log (1 + (Fintype.card (Fin (B.Nq (m + 1))) : ℝ))))
              = Real.sqrt (n + 1 : ℕ) * chainThreshold B δ m := by
            rw [hcard, chainThreshold, hε_def]; ring
          rw [hthr_eq]
          by_cases hω : ω ∈ {y | chainB B δ (n + 1) (m + 1) i y}
          · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
            -- The middle clause pins `f`'s own level-`m`
            -- cell-ancestor envelope directly, `Δ_m (ancestor) ω ≤ √(n + 1)·chainThreshold m`;
            -- nesting `Δ_{m+1} i ≤ Δ_m (ancestor)` is `Δ_le_ancestor`.
            have hΔ_nn : 0 ≤ B.Δ (m + 1) i ω :=
              le_trans (abs_nonneg (B.π (m + 1) i ω - B.π (m + 1) i ω)) (by
                simpa using B.diam hq0_le i (B.π (m + 1) i) (B.π_mem hq0_le i) (B.π (m + 1) i)
                  (B.π_mem hq0_le i) ω)
            obtain ⟨_, hsmall, _⟩ := hω
            -- The gate at level `p = m` (the immediate predecessor of `m+1`).
            have hanc_small :
                B.Δ m (B.ancestor hq0_le i m hq1_le (Nat.le_succ m)) ω
                  ≤ Real.sqrt (n + 1 : ℕ) * chainThreshold B δ m :=
              hsmall m hq1_le (Nat.lt_succ_self m)
            have hΔ_le_anc :
                B.Δ (m + 1) i ω ≤ B.Δ m (B.ancestor hq0_le i m hq1_le (Nat.le_succ m)) ω :=
              B.Δ_le_ancestor hq0_le i m hq1_le (Nat.le_succ m) ω
            calc |B.Δ (m + 1) i ω| = B.Δ (m + 1) i ω := abs_of_nonneg hΔ_nn
              _ ≤ B.Δ m (B.ancestor hq0_le i m hq1_le (Nat.le_succ m)) ω := hΔ_le_anc
              _ ≤ Real.sqrt (n + 1 : ℕ) * chainThreshold B δ m := hanc_small
          · rw [Set.indicator_of_notMem hω, mul_zero, abs_zero]
            have : 0 ≤ chainThreshold B δ m := by rw [chainThreshold]; positivity
            positivity
        · -- hg_var : `∫ (g i)² ≤ (2ε)²`.
          -- `‖g i‖₂ ≤ ‖Δ_{m+1} i‖₂ ≤ δ·(1/2)^{(m+1)−q₀} = δ·(1/2)^{m+1−q₀} ≤ 2ε`.
          intro i
          have hΔ_memLp : MemLp (B.Δ (m + 1) i) 2 P := B.Δ_memLp hq0_le i
          -- `∫ (Δ_{m+1} i)² ≤ (δ·(1/2)^{m+1−q₀})²`.
          have hΔ_sq_le : ∫ ω, (B.Δ (m + 1) i ω) ^ 2 ∂P
              ≤ (δ * (1/2 : ℝ) ^ (m + 1 - q₀)) ^ 2 := by
            have hnn : 0 ≤ ∫ ω, (B.Δ (m + 1) i ω) ^ 2 ∂P :=
              MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
            have hCpow_nn : 0 ≤ δ * (1/2 : ℝ) ^ (m + 1 - q₀) := by positivity
            have hsqrt_eq : Real.sqrt (∫ ω, (B.Δ (m + 1) i ω) ^ 2 ∂P)
                = (eLpNorm (B.Δ (m + 1) i) 2 P).toReal := by
              rw [hΔ_memLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
              have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
              have h_int_eq :
                  (fun ω => ‖B.Δ (m + 1) i ω‖ ^ (2 : ℝ≥0∞).toReal)
                    = (fun ω => B.Δ (m + 1) i ω ^ 2) := by
                funext ω; rw [h2, Real.rpow_two, Real.norm_eq_abs, sq_abs]
              rw [h_int_eq, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), h2,
                Real.sqrt_eq_rpow]
              norm_num
            have hsqrt_le : Real.sqrt (∫ ω, (B.Δ (m + 1) i ω) ^ 2 ∂P)
                ≤ δ * (1/2 : ℝ) ^ (m + 1 - q₀) := by
              rw [hsqrt_eq]
              calc (eLpNorm (B.Δ (m + 1) i) 2 P).toReal
                  ≤ (ENNReal.ofReal (δ * (1/2 : ℝ) ^ (m + 1 - q₀))).toReal :=
                    ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne (B.Δ_L2_le hq0_le i)
                _ = δ * (1/2 : ℝ) ^ (m + 1 - q₀) := ENNReal.toReal_ofReal hCpow_nn
            nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ ω, (B.Δ (m + 1) i ω) ^ 2 ∂P), hsqrt_le,
              hCpow_nn]
          -- `∫ (g i)² ≤ ∫ (Δ_{m+1} i)²` (indicator ≤ 1).
          have hgsq_le : ∫ ω, (g i ω) ^ 2 ∂P ≤ ∫ ω, (B.Δ (m + 1) i ω) ^ 2 ∂P := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Eventually.of_forall (fun ω => sq_nonneg _)) (hΔ_memLp.integrable_sq) ?_
            refine Eventually.of_forall (fun ω => ?_)
            rw [hg_def]
            simp only [truncOsc]
            rcases Set.indicator_eq_zero_or_self {y | chainB B δ (n + 1) (m + 1) i y} (1 : Ω → ℝ) ω with
              h0 | h1
            · rw [h0, mul_zero]; simpa using sq_nonneg (B.Δ (m + 1) i ω)
            · rw [h1, Pi.one_apply, mul_one]
          refine hgsq_le.trans (hΔ_sq_le.trans ?_)
          -- `(δ·(1/2)^{m+1−q₀})² ≤ (2ε)²`: `δ = δ`, `(1/2)^{m+1−q₀} = (1/2)·(1/2)^{m−q₀}`.
          have hCeq : δ * (1/2 : ℝ) ^ (m + 1 - q₀) ≤ 2 * ε := by
            rw [hε_def]
            have hpow : (1/2 : ℝ) ^ (m + 1 - q₀) = (1/2 : ℝ) * (1/2 : ℝ) ^ (m - q₀) := by
              rw [← pow_succ']
              congr 1; omega
            rw [hpow]; ring_nf
            nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) (m - q₀), hδ.le]
          have hCnn : 0 ≤ δ * (1/2 : ℝ) ^ (m + 1 - q₀) := by positivity
          nlinarith [hCeq, hCnn, hε_pos.le]
      · -- `q ≤ q₀`: `chainB` false (`q₀ < q` fails) ⇒ `truncOsc = 0` ⇒ `levelOscSup = 0`.
        have hzero : levelOscSup B μ X δ (n + 1) q = 0 := by
          rw [levelOscSup]
          have hpt : ∀ ξ : Ξ, (⨆ i : Fin (B.Nq q),
              ENNReal.ofReal
                |empiricalProcess P (n + 1) (fun k : Fin (n + 1) => X k.val ξ) (truncOsc B δ (n + 1) q i)|) = 0 := by
            intro ξ
            refine iSup_eq_zero.mpr (fun i => ?_)
            have hfun : truncOsc B δ (n + 1) q i = (fun _ => (0 : ℝ)) := by
              funext x
              simp only [truncOsc]
              rw [Set.indicator_of_notMem, mul_zero]
              simp only [Set.mem_setOf_eq, chainB]
              exact fun h => hq0q h.1
            rw [hfun]
            have : empiricalProcess P (n + 1) (fun k : Fin (n + 1) => X k.val ξ) (fun _ => (0 : ℝ)) = 0 := by
              simp [empiricalProcess, empiricalAvg]
            rw [this, abs_zero, ENNReal.ofReal_zero]
          simp_rw [hpt]
          rw [lintegral_zero]
        rw [hzero]
        exact zero_le
    -- =====================================================================
    -- STEP 2 — Sum the per-level bounds and reindex.
    -- =====================================================================
    calc (∑' q : ℕ, levelOscSup B μ X δ (n + 1) q)
        ≤ ∑' q : ℕ, ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1))
            * ((2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc q₀ q, b p)) :=
          ENNReal.tsum_le_tsum hlevel
      _ = ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1))
            * ∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc q₀ q, b p) := by
          rw [ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1))
            * (2 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * b p) := by
          gcongr
          exact AsymptoticStatistics.ForMathlib.ENNReal.tsum_pow_half_sum_Icc_le q₀ b
      _ = ENNReal.ofReal (4 * K)
            * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                * entropyIntegrand ((1/2 : ℝ)^q * δ) F P) := by
          -- `∑'_p (2⁻¹)^p b p = (2⁻¹)^{q₀} · series` (reindex `p = q₀ + j`).
          have hreindex :
              (∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * b p)
                = (2⁻¹ : ℝ≥0∞) ^ q₀
                    * ∑' j : ℕ, ENNReal.ofReal ((1/2 : ℝ)^j * δ)
                        * entropyIntegrand ((1/2 : ℝ)^j * δ) F P := by
            -- support of `p ↦ (2⁻¹)^p b p` ⊆ range of `j ↦ q₀ + j`.
            have hinj : Function.Injective (fun j : ℕ => q₀ + j) :=
              fun a c h => by simpa using Nat.add_left_cancel h
            have hsupp : (Function.support fun p => (2⁻¹ : ℝ≥0∞) ^ p * b p)
                ⊆ Set.range (fun j : ℕ => q₀ + j) := by
              intro p hp
              simp only [Function.mem_support, ne_eq] at hp
              by_cases hpq0 : q₀ ≤ p
              · exact ⟨p - q₀, Nat.add_sub_cancel' hpq0⟩
              · exfalso; apply hp
                rw [hb_def]; simp only [if_neg hpq0, mul_zero]
            rw [← hinj.tsum_eq hsupp, ← ENNReal.tsum_mul_left]
            refine tsum_congr fun j => ?_
            -- term `j`: `(2⁻¹)^{q₀+j} · b(q₀+j) = (2⁻¹)^{q₀}·(2⁻¹)^j·ofReal δ·integrand`.
            have hbj : b (q₀ + j)
                = ENNReal.ofReal δ * entropyIntegrand ((1/2 : ℝ) ^ j * δ) F P := by
              rw [hb_def]; simp only [if_pos (Nat.le_add_right q₀ j), Nat.add_sub_cancel_left]
            rw [hbj, pow_add, hofpow j]
            rw [show ((1/2 : ℝ) ^ j * δ) = (1/2 : ℝ) ^ j * δ from rfl,
              ENNReal.ofReal_mul (by positivity)]
            ring
          rw [hreindex]
          -- scalar `ofReal(K·2^{q₀+1}) · 2 · (2⁻¹)^{q₀} = ofReal(4K)`.
          have hofq0 : (2⁻¹ : ℝ≥0∞) ^ q₀ = ENNReal.ofReal ((1/2 : ℝ) ^ q₀) := hofpow q₀
          have hscalar :
              ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1)) * (2 * (2⁻¹ : ℝ≥0∞) ^ q₀)
                = ENNReal.ofReal (4 * K) := by
            rw [hofq0, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            have : (2 : ℝ) ^ (q₀ + 1) * (2 * (1/2 : ℝ) ^ q₀) = 4 := by
              rw [pow_succ]
              have h2 : (2 : ℝ) ^ q₀ * (1/2 : ℝ) ^ q₀ = 1 := by
                rw [← mul_pow]; norm_num
              nlinarith [h2]
            nlinarith [this]
          calc ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1))
                  * (2 * ((2⁻¹ : ℝ≥0∞) ^ q₀
                      * ∑' j : ℕ, ENNReal.ofReal ((1/2 : ℝ)^j * δ)
                          * entropyIntegrand ((1/2 : ℝ)^j * δ) F P))
              = (ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1)) * (2 * (2⁻¹ : ℝ≥0∞) ^ q₀))
                  * ∑' j : ℕ, ENNReal.ofReal ((1/2 : ℝ)^j * δ)
                      * entropyIntegrand ((1/2 : ℝ)^j * δ) F P := by ring
            _ = ENNReal.ofReal (4 * K)
                  * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                      * entropyIntegrand ((1/2 : ℝ)^q * δ) F P := by rw [hscalar]

/-- The maximal B-link mean correction is absorbed by the same dyadic entropy
series (vdV Lemma 19.34, pp.287--288). -/
theorem fullClamped_chain_Bmean_dyadic_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (q₀ n : ℕ) (δ t : ℝ)
        (D : FullClampedPartitionData F P Φ q₀ δ n t),
      0 < δ →
        Bmean D.partition δ n ≤ ENNReal.ofReal c *
          (∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ) *
            entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P) := by
  classical
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrtlog2_pos : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr hlog2_pos
  set K₀ : ℝ := 4 * (1 + 1 / Real.sqrt (Real.log 2)) with hK₀_def
  have hK₀_pos : 0 < K₀ := by rw [hK₀_def]; positivity
  clear_value K₀
  refine ⟨4 * K₀, by positivity, ?_⟩
  intro Ω _ P _ F Φ q₀ n δ t D hδ
  cases n with
  | zero => simp [Bmean]
  | succ n =>
    let B := D.partition
    have hn : 1 ≤ n + 1 := by omega
    have hF_ne : F.Nonempty := by
      obtain ⟨f, hf⟩ := D.truncated_nonempty
      obtain ⟨g, hg, _⟩ := hf
      exact ⟨g, hg⟩
    have hsn_pos : 0 < Real.sqrt (n + 1 : ℕ) := by positivity
    have hsn_nn : (0 : ℝ) ≤ Real.sqrt (n + 1 : ℕ) := hsn_pos.le
    set a : ℕ → ℝ≥0∞ :=
      fun k => entropyIntegrand ((1/2 : ℝ)^k * δ) F P with ha_def
    have hofReal_half : ENNReal.ofReal (1/2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
      rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    have hpow_eq : ∀ q : ℕ,
        ENNReal.ofReal ((1/2 : ℝ)^q * δ) =
          (2⁻¹ : ℝ≥0∞)^q * ENNReal.ofReal δ := by
      intro q
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        hofReal_half]
    have hlevel : ∀ q : ℕ,
        4 * ENNReal.ofReal (Real.sqrt (n + 1 : ℕ))
            * ⨆ i : Fin (B.Nq (q₀ + q)), ∫⁻ x, ENNReal.ofReal
                (B.Δ (q₀ + q) i x
                  * Set.indicator {y | chainB B δ (n + 1) (q₀ + q) i y}
                    (1 : Ω → ℝ) x) ∂P
          ≤ ENNReal.ofReal K₀
              * (ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                * (∑ k ∈ Finset.Icc 0 (q + 1), a k)) := by
      intro q
      set Q : ℕ := q₀ + q with hQ_def
      have hQ : q₀ ≤ Q := Nat.le_add_right q₀ q
      have hQq : Q - q₀ = q := by omega
      have hΔsq_le : ∀ i : Fin (B.Nq Q),
          ∫ x, (B.Δ Q i x) ^ 2 ∂P ≤ (δ * (1/2 : ℝ)^q) ^ 2 := by
        intro i
        have hΔ_memLp : MemLp (B.Δ Q i) 2 P := B.Δ_memLp hQ i
        have hnn : 0 ≤ ∫ x, (B.Δ Q i x) ^ 2 ∂P :=
          MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
        have hCpow_nn : 0 ≤ δ * (1/2 : ℝ) ^ (Q - q₀) := by positivity
        have hsqrt_eq : Real.sqrt (∫ x, (B.Δ Q i x) ^ 2 ∂P)
            = (eLpNorm (B.Δ Q i) 2 P).toReal := by
          rw [hΔ_memLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
          have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
          have h_int_eq :
              (fun x => ‖B.Δ Q i x‖ ^ (2 : ℝ≥0∞).toReal)
                = (fun x => B.Δ Q i x ^ 2) := by
            funext x
            rw [h2, Real.rpow_two, Real.norm_eq_abs, sq_abs]
          rw [h_int_eq, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), h2,
            Real.sqrt_eq_rpow]
          norm_num
        have hsqrt_le : Real.sqrt (∫ x, (B.Δ Q i x) ^ 2 ∂P)
            ≤ δ * (1/2 : ℝ)^q := by
          rw [hsqrt_eq]
          calc
            (eLpNorm (B.Δ Q i) 2 P).toReal
                ≤ (ENNReal.ofReal (δ * (1/2 : ℝ) ^ (Q - q₀))).toReal :=
                  ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne (B.Δ_L2_le hQ i)
            _ = δ * (1/2 : ℝ) ^ (Q - q₀) := ENNReal.toReal_ofReal hCpow_nn
            _ = δ * (1/2 : ℝ)^q := by rw [hQq]
        nlinarith [Real.sq_sqrt hnn,
          Real.sqrt_nonneg (∫ x, (B.Δ Q i x) ^ 2 ∂P), hsqrt_le,
          mul_nonneg hδ.le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) q)]
      set E : ℝ := 1 + Real.sqrt (Real.log (1 + (B.Nq (Q + 1) : ℝ))) with hE_def
      have hE_pos : 0 < E := by rw [hE_def]; positivity
      have haQ_eq : chainThreshold B δ Q = (1/2 : ℝ)^q * δ / E := by
        rw [chainThreshold, hQq, hE_def]
      have haQ_pos : 0 < chainThreshold B δ Q := by
        rw [haQ_eq]
        positivity
      have hcell : ∀ i : Fin (B.Nq Q),
          4 * ENNReal.ofReal (Real.sqrt (n + 1 : ℕ))
              * ∫⁻ x, ENNReal.ofReal
                  (B.Δ Q i x
                    * Set.indicator {y | chainB B δ (n + 1) Q i y}
                      (1 : Ω → ℝ) x) ∂P
            ≤ ENNReal.ofReal (4 * (δ * (1/2 : ℝ)^q) * E) := by
        intro i
        have hpt : ∀ x : Ω,
            ENNReal.ofReal
                (B.Δ Q i x
                  * Set.indicator {y | chainB B δ (n + 1) Q i y}
                    (1 : Ω → ℝ) x)
              ≤ ENNReal.ofReal
                  (1 / (Real.sqrt (n + 1 : ℕ) * chainThreshold B δ Q))
                    * ENNReal.ofReal ((B.Δ Q i x) ^ 2) := by
          intro x
          by_cases hx : x ∈ {y | chainB B δ (n + 1) Q i y}
          · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
            obtain ⟨_, _, hcross⟩ := hx
            have hΔnn : 0 ≤ B.Δ Q i x := by
              have hdiam := B.diam hQ i (B.π Q i) (B.π_mem hQ i)
                (B.π Q i) (B.π_mem hQ i) x
              simpa using hdiam
            have hthr_pos : 0 <
                Real.sqrt (n + 1 : ℕ) * chainThreshold B δ Q := by positivity
            have hΔ_le : B.Δ Q i x
                ≤ 1 / (Real.sqrt (n + 1 : ℕ) * chainThreshold B δ Q)
                    * (B.Δ Q i x) ^ 2 := by
              rw [div_mul_eq_mul_div, le_div_iff₀ hthr_pos]
              nlinarith [hcross.le, hΔnn, sq_nonneg (B.Δ Q i x)]
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal hΔ_le
          · rw [Set.indicator_of_notMem hx, mul_zero, ENNReal.ofReal_zero]
            exact zero_le
        have hΔ_memLp : MemLp (B.Δ Q i) 2 P := B.Δ_memLp hQ i
        have hΔsq_int : Integrable (fun x => (B.Δ Q i x) ^ 2) P :=
          hΔ_memLp.integrable_sq
        have hlint_sq : ∫⁻ x, ENNReal.ofReal ((B.Δ Q i x) ^ 2) ∂P
            = ENNReal.ofReal (∫ x, (B.Δ Q i x) ^ 2 ∂P) := by
          rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hΔsq_int
            (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
        calc
          4 * ENNReal.ofReal (Real.sqrt (n + 1 : ℕ))
                * ∫⁻ x, ENNReal.ofReal
                    (B.Δ Q i x
                      * Set.indicator {y | chainB B δ (n + 1) Q i y}
                        (1 : Ω → ℝ) x) ∂P
              ≤ 4 * ENNReal.ofReal (Real.sqrt (n + 1 : ℕ))
                  * ∫⁻ x, ENNReal.ofReal
                      (1 / (Real.sqrt (n + 1 : ℕ) * chainThreshold B δ Q))
                        * ENNReal.ofReal ((B.Δ Q i x) ^ 2) ∂P :=
                mul_le_mul_of_nonneg_left (lintegral_mono hpt) (zero_le)
          _ = 4 * ENNReal.ofReal (Real.sqrt (n + 1 : ℕ))
                * (ENNReal.ofReal
                    (1 / (Real.sqrt (n + 1 : ℕ) * chainThreshold B δ Q))
                      * ENNReal.ofReal (∫ x, (B.Δ Q i x) ^ 2 ∂P)) := by
              rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
                hlint_sq]
          _ ≤ ENNReal.ofReal (4 * (δ * (1/2 : ℝ)^q) * E) := by
              rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
                ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
                ← ENNReal.ofReal_mul (by positivity),
                ← ENNReal.ofReal_mul (by positivity)]
              apply ENNReal.ofReal_le_ofReal
              have hint_nn : 0 ≤ ∫ x, (B.Δ Q i x) ^ 2 ∂P :=
                MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
              have hcancel : 4 * Real.sqrt (n + 1 : ℕ)
                  * (1 / (Real.sqrt (n + 1 : ℕ) * chainThreshold B δ Q)
                    * (∫ x, (B.Δ Q i x) ^ 2 ∂P))
                    = 4 * (∫ x, (B.Δ Q i x) ^ 2 ∂P) / chainThreshold B δ Q := by
                field_simp
              rw [hcancel, div_le_iff₀ haQ_pos]
              calc
                4 * (∫ x, (B.Δ Q i x) ^ 2 ∂P)
                    ≤ 4 * (δ * (1/2 : ℝ)^q) ^ 2 :=
                      mul_le_mul_of_nonneg_left (hΔsq_le i) (by norm_num)
                _ = 4 * (δ * (1/2 : ℝ)^q) * E * chainThreshold B δ Q := by
                    rw [haQ_eq]
                    field_simp
      have hsup_le :
          4 * ENNReal.ofReal (Real.sqrt (n + 1 : ℕ))
              * ⨆ i : Fin (B.Nq Q), ∫⁻ x, ENNReal.ofReal
                  (B.Δ Q i x
                    * Set.indicator {y | chainB B δ (n + 1) Q i y}
                      (1 : Ω → ℝ) x) ∂P
            ≤ ENNReal.ofReal (4 * (δ * (1/2 : ℝ)^q) * E) := by
        rw [ENNReal.mul_iSup]
        exact iSup_le (fun i => hcell i)
      refine hsup_le.trans ?_
      have hIcc_ne : (Finset.Icc q₀ (Q + 1)).Nonempty :=
        ⟨q₀, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
      have hcard_prod :
          (B.Nq (Q + 1) : ℝ)
            ≤ ∏ p ∈ Finset.Icc q₀ (Q + 1), (B.coverCard p : ℝ) := by
        have hcard := B.jump_card_le (q := Q) (le_trans hQ (Nat.le_succ Q))
        calc
          (B.Nq (Q + 1) : ℝ)
              ≤ ((∏ p ∈ Finset.Icc q₀ (Q + 1), B.coverCard p : ℕ) : ℝ) := by
                exact_mod_cast hcard
          _ = ∏ p ∈ Finset.Icc q₀ (Q + 1), (B.coverCard p : ℝ) := by
                push_cast
                rfl
      have hsalvage :
          Real.sqrt (Real.log (1 + (B.Nq (Q + 1) : ℝ)))
            ≤ ∑ p ∈ Finset.Icc q₀ (Q + 1),
                Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))) := by
        refine le_trans (Real.sqrt_le_sqrt (Real.log_le_log (by positivity) ?_))
          (AsymptoticStatistics.ForMathlib.Real.sqrt_log_prod_le_sum_one_add
            hIcc_ne (fun p => B.coverCard p))
        have hprod_nonneg :
            (0 : ℝ) ≤ ∏ p ∈ Finset.Icc q₀ (Q + 1), (B.coverCard p : ℝ) :=
          Finset.prod_nonneg (fun p _ => Nat.cast_nonneg _)
        linarith [hcard_prod]
      have hcover_sum :
          (∑ p ∈ Finset.Icc q₀ (Q + 1),
              ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ)))))
            ≤ ∑ k ∈ Finset.Icc 0 (q + 1), a k := by
        have hterm : ∀ p ∈ Finset.Icc q₀ (Q + 1),
            ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))))
              ≤ entropyIntegrand ((1/2 : ℝ)^(p - q₀) * δ) F P := by
          intro p hp
          obtain ⟨hpq0, _⟩ := Finset.mem_Icc.mp hp
          have hco := D.coverCard_original_le hpq0
          calc
            ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))))
                = entropyWeight (B.coverCard p : ℕ∞) := (entropyWeight_coe _).symm
            _ ≤ entropyWeight
                (bracketingNumber ((1/2 : ℝ)^(p - q₀) * δ) F 2 P) :=
                  entropyWeight_mono hco
            _ = entropyIntegrand ((1/2 : ℝ)^(p - q₀) * δ) F P := rfl
        calc
          (∑ p ∈ Finset.Icc q₀ (Q + 1),
              ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ)))))
              ≤ ∑ p ∈ Finset.Icc q₀ (Q + 1),
                  entropyIntegrand ((1/2 : ℝ)^(p - q₀) * δ) F P :=
                    Finset.sum_le_sum hterm
          _ = ∑ k ∈ Finset.Icc 0 (q + 1), a k := by
              refine Finset.sum_nbij' (fun p => p - q₀) (fun k => k + q₀)
                ?_ ?_ ?_ ?_ ?_
              · intro p hp
                simp only [hQ_def, Finset.mem_Icc] at hp ⊢
                omega
              · intro k hk
                simp only [hQ_def, Finset.mem_Icc] at hk ⊢
                omega
              · intro p hp
                simp only [hQ_def, Finset.mem_Icc] at hp ⊢
                omega
              · intro k hk
                simp only [Finset.mem_Icc] at hk ⊢
                omega
              · intro p _
                rw [ha_def]
      have hone_le_sum :
          ENNReal.ofReal (Real.sqrt (Real.log 2))
            ≤ ∑ k ∈ Finset.Icc 0 (q + 1), a k := by
        have h0mem : (0 : ℕ) ∈ Finset.Icc 0 (q + 1) :=
          Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
        refine le_trans ?_
          (Finset.single_le_sum (f := a) (fun k _ => zero_le) h0mem)
        rw [ha_def]
        simp only [pow_zero, one_mul]
        exact sqrt_log_two_le_entropyIntegrand hF_ne δ
      have hsqrtlog2_ne : ENNReal.ofReal (Real.sqrt (Real.log 2)) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact hsqrtlog2_pos
      set Sum : ℝ≥0∞ := ∑ k ∈ Finset.Icc 0 (q + 1), a k with hSum_def
      have hE_le : ENNReal.ofReal E
          ≤ ENNReal.ofReal (1 + 1 / Real.sqrt (Real.log 2)) * Sum := by
        have hRHS : ENNReal.ofReal (1 + 1 / Real.sqrt (Real.log 2)) * Sum
            = (ENNReal.ofReal (Real.sqrt (Real.log 2)))⁻¹ * Sum + Sum := by
          rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
            ENNReal.ofReal_div_of_pos hsqrtlog2_pos, ENNReal.ofReal_one,
            one_div, add_mul, one_mul, add_comm]
        rw [hRHS, hE_def,
          ENNReal.ofReal_add (by norm_num) (Real.sqrt_nonneg _),
          ENNReal.ofReal_one]
        refine add_le_add ?_ ?_
        · calc
            (1 : ℝ≥0∞)
                = (ENNReal.ofReal (Real.sqrt (Real.log 2)))⁻¹
                    * ENNReal.ofReal (Real.sqrt (Real.log 2)) :=
                      (ENNReal.inv_mul_cancel hsqrtlog2_ne ENNReal.ofReal_ne_top).symm
            _ ≤ (ENNReal.ofReal (Real.sqrt (Real.log 2)))⁻¹ * Sum :=
                  mul_le_mul_of_nonneg_left hone_le_sum (zero_le)
        · refine le_trans ?_ hcover_sum
          rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.sqrt_nonneg _)]
          exact ENNReal.ofReal_le_ofReal hsalvage
      calc
        ENNReal.ofReal (4 * (δ * (1/2 : ℝ)^q) * E)
            = ENNReal.ofReal (4 * ((1/2 : ℝ)^q * δ)) * ENNReal.ofReal E := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                congr 1
                ring
        _ ≤ ENNReal.ofReal (4 * ((1/2 : ℝ)^q * δ))
              * (ENNReal.ofReal (1 + 1 / Real.sqrt (Real.log 2)) * Sum) :=
                mul_le_mul_of_nonneg_left hE_le (zero_le)
        _ = ENNReal.ofReal K₀
              * (ENNReal.ofReal ((1/2 : ℝ)^q * δ) * Sum) := by
                rw [hK₀_def,
                  ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
                  ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
                ring
    rw [Bmean]
    calc
      (∑' q : ℕ, 4 * ENNReal.ofReal (Real.sqrt (n + 1 : ℕ))
            * ⨆ i : Fin (B.Nq (q₀ + q)), ∫⁻ x, ENNReal.ofReal
                (B.Δ (q₀ + q) i x
                  * Set.indicator {y | chainB B δ (n + 1) (q₀ + q) i y}
                    (1 : Ω → ℝ) x) ∂P)
          ≤ ∑' q : ℕ, ENNReal.ofReal K₀
              * (ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                * (∑ k ∈ Finset.Icc 0 (q + 1), a k)) :=
            ENNReal.tsum_le_tsum hlevel
      _ = ENNReal.ofReal K₀
            * ∑' q : ℕ, (2⁻¹ : ℝ≥0∞)^q
                * (∑ k ∈ Finset.Icc 0 (q + 1), ENNReal.ofReal δ * a k) := by
              rw [← ENNReal.tsum_mul_left]
              refine tsum_congr fun q => ?_
              rw [hpow_eq q, ← Finset.mul_sum]
              ring
      _ ≤ ENNReal.ofReal K₀
            * (4 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞)^p * (ENNReal.ofReal δ * a p)) := by
              gcongr
              exact fullClamped_tsum_pow_half_sum_Icc_succ_le
                (fun k => ENNReal.ofReal δ * a k)
      _ = ENNReal.ofReal K₀
            * (4 * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
              * entropyIntegrand ((1/2 : ℝ)^q * δ) F P)) := by
              congr 1
              congr 1
              refine tsum_congr fun p => ?_
              rw [hpow_eq p, ha_def]
              ring
      _ = ENNReal.ofReal (4 * K₀)
            * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
              * entropyIntegrand ((1/2 : ℝ)^q * δ) F P) := by
              rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
                show (ENNReal.ofReal 4 : ℝ≥0∞) = 4 by simp]
              ring

/-- The scale-`8δ` dyadic entropy series is controlled by fifteen times the
target-`δ` series. The constants `8` and `15` encode the
normalization of the book's initial-scale window (vdV §19.6 p.287). -/
theorem fullClamped_factorEight_dyadic_le_target (hδ : 0 < δ) :
    (∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * (8 * δ)) *
      entropyIntegrand ((1 / 2 : ℝ) ^ k * (8 * δ)) F P) ≤
    15 * ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ) *
      entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P := by
  have hterm : ∀ k : ℕ,
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k * (8 * δ))
          * entropyIntegrand ((1 / 2 : ℝ) ^ k * (8 * δ)) F P
        ≤ 8 * (ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ)
          * entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P) := by
    intro k
    have hscale_nonneg : 0 ≤ (1 / 2 : ℝ) ^ k * δ := by positivity
    have hscale_eq : (1 / 2 : ℝ) ^ k * (8 * δ)
        = 8 * ((1 / 2 : ℝ) ^ k * δ) := by ring
    have hentropy : entropyIntegrand ((1 / 2 : ℝ) ^ k * (8 * δ)) F P
        ≤ entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P := by
      apply entropyIntegrand_antitone_eps
      rw [hscale_eq]
      nlinarith
    have hentropy' : entropyIntegrand (8 * ((1 / 2 : ℝ) ^ k * δ)) F P
        ≤ entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P := by
      simpa only [hscale_eq] using hentropy
    rw [hscale_eq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num only [ENNReal.ofReal_ofNat]
    calc
      8 * ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ)
            * entropyIntegrand (8 * ((1 / 2 : ℝ) ^ k * δ)) F P
          ≤ 8 * ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ)
            * entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P := by
              exact mul_le_mul_of_nonneg_left hentropy' (zero_le)
      _ = 8 * (ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ)
            * entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P) := by ring
  calc
    (∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * (8 * δ))
        * entropyIntegrand ((1 / 2 : ℝ) ^ k * (8 * δ)) F P)
        ≤ ∑' k : ℕ, 8 * (ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ)
          * entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P) :=
            ENNReal.tsum_le_tsum hterm
    _ = 8 * ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ)
          * entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P := by
            rw [ENNReal.tsum_mul_left]
    _ ≤ 15 * ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ)
          * entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P := by
            gcongr
            norm_num

omit [MeasurableSpace Ξ] in
/-- The gated-telescope interchange for a tail-free full-clamped chain. -/
private theorem fullClamped_Gn_telescope_link_bound
    [IsProbabilityMeasure P]
    (B : NestedBracketPartition F P q₀ C)
    (hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
    (hF_meas : ∀ f ∈ F, Measurable f)
    {X : ℕ → Ξ → Ω}
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (hn : 1 ≤ n) (ξ : Ξ)
    {f : Ω → ℝ} (hf : f ∈ F) (i₀ : Fin (B.Nq q₀)) (hi₀ : f ∈ B.cell q₀ i₀)
    (hA_q0 : ∀ x, B.Δ q₀ i₀ x ≤ Real.sqrt n * chainThreshold B δ q₀) :
    ENNReal.ofReal
        |empiricalProcess P n (fun k : Fin n => X k.val ξ)
          (fun x => f x - B.π q₀ i₀ x)|
      ≤ (∑' q : ℕ, ⨆ i : Fin (B.Nq (q₀ + q)),
            ⨆ (g : Ω → ℝ) (_ : g ∈ B.cell (q₀ + q) i), ENNReal.ofReal
              |empiricalProcess P n (fun j : Fin n => X j.val ξ)
                (fun x => (g x - B.π (q₀ + q) i x)
                  * Set.indicator {y | chainB B δ n (q₀ + q) i y} (1 : Ω → ℝ) x)|)
        + (∑' q : ℕ, ⨆ i : Fin (B.Nq (q₀ + q + 1)), ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ)
              (truncJump B δ n (Nat.le_add_right q₀ q) i)|) := by
  classical
  set Y : Fin n → Ω := fun k : Fin n => X k.val ξ with hY_def
  have hsn_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  -- The chain representatives and the per-level smallness predicate.
  set c : (k : ℕ) → Fin (B.Nq (q₀ + k)) := fun k => cellChain B hf k with hc_def
  set r : ℕ → Ω → ℝ := fun k => B.π (q₀ + k) (c k) with hr_def
  -- `r 0 = π q₀ i₀`.
  have hr0 : r 0 = B.π q₀ i₀ := by
    simp only [hr_def, hc_def]
    rw [cellChain_zero B hf i₀ hi₀]
    congr 1
  -- The level-`(q₀+k)` cell oscillation envelope of the chain cell.
  set D : ℕ → Ω → ℝ := fun k => B.Δ (q₀ + k) (c k) with hD_def
  have hf_meas' : Measurable f := hF_meas f hf
  have hr_meas : ∀ k, Measurable (r k) := fun k => hπ_meas (Nat.le_add_right q₀ k) (c k)
  have hD_meas : ∀ k, Measurable (D k) := fun k => B.Δ_meas (Nat.le_add_right q₀ k) (c k)
  have hD_nn : ∀ k x, 0 ≤ D k x := by
    intro k x
    have := B.diam (Nat.le_add_right q₀ k) (c k) (B.π (q₀+k) (c k))
      (B.π_mem (Nat.le_add_right q₀ k) (c k)) (B.π (q₀+k) (c k))
      (B.π_mem (Nat.le_add_right q₀ k) (c k)) x
    simpa [hD_def] using this
  have hD_int : ∀ k, Integrable (D k) P :=
    fun k => (B.Δ_memLp (Nat.le_add_right q₀ k) (c k)).integrable (by norm_num)
  -- `f` lies in its chain cell, so `|f − r k| ≤ D k` pointwise (cell diam).
  have hf_mem : ∀ k, f ∈ B.cell (q₀ + k) (c k) := fun k => cellChain_mem B hf k
  have hfr_le : ∀ k x, |f x - r k x| ≤ D k x := by
    intro k x
    exact B.diam (Nat.le_add_right q₀ k) (c k) f (hf_mem k) (B.π (q₀+k) (c k))
      (B.π_mem (Nat.le_add_right q₀ k) (c k)) x
  -- `f · 1{measurable set}` shifted by `r k` is integrable: `|(f − r k)·1| ≤ D k ∈ L¹`.
  have hgated_int : ∀ (k : ℕ) (s : Set Ω), MeasurableSet s →
      Integrable (fun x => (f x - r k x) * Set.indicator s (1 : Ω → ℝ) x) P := by
    intro k s hs
    refine Integrable.mono' (hD_int k)
      ((hf_meas'.sub (hr_meas k)).mul (measurable_const.indicator hs)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    calc |f x - r k x| * |Set.indicator s (1 : Ω → ℝ) x|
        ≤ D k x * 1 := by
          refine mul_le_mul (hfr_le k x) ?_ (abs_nonneg _) (hD_nn k x)
          by_cases hx : x ∈ s
          · simp [Set.indicator_of_mem hx]
          · simp [Set.indicator_of_notMem hx]
      _ = D k x := mul_one _
  -- The jump equals the representative difference, and is bounded by `D k`.
  have hjump_eq : ∀ k, B.jump (Nat.le_add_right q₀ k) (c (k+1))
      = (fun x => r (k+1) x - r k x) := by
    intro k; funext x
    simp only [NestedBracketPartition.jump, hr_def, hc_def]
    rw [cellChain_parent B hf k]
    rfl
  have hjump_le : ∀ k x, |B.jump (Nat.le_add_right q₀ k) (c (k+1)) x| ≤ D k x := by
    intro k x
    have := B.jump_abs_le (Nat.le_add_right q₀ k) (c (k+1)) x
    rwa [cellChain_parent B hf k] at this
  -- The A-gate / B-gate measurable sets and their indicators.
  set As : ℕ → Set Ω := fun k => {y | chainA B δ n (q₀ + k) (c k) y} with hAs_def
  set Bs : ℕ → Set Ω := fun k => {y | chainB B δ n (q₀ + k) (c k) y} with hBs_def
  have hAs_meas : ∀ k, MeasurableSet (As k) := by
    intro k
    have hset : As k = ⋂ (p : ℕ) (hp₀ : q₀ ≤ p) (hpq : p ≤ q₀ + k),
        {x | B.Δ p (B.ancestor (le_trans hp₀ hpq) (c k) p hp₀ hpq) x
            ≤ Real.sqrt n * chainThreshold B δ p} := by
      ext x
      simp only [hAs_def, chainA, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hset]
    refine MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hp₀ =>
      MeasurableSet.iInter (fun hpq => ?_)))
    exact measurableSet_le (B.Δ_meas hp₀ _) measurable_const
  have hBs_meas : ∀ k, MeasurableSet (Bs k) := by
    intro k
    have hset : Bs k = {_x : Ω | q₀ < q₀ + k}
        ∩ ((⋂ (p : ℕ) (hp₀ : q₀ ≤ p) (hpq : p < q₀ + k),
              {x | B.Δ p
                    (B.ancestor (le_of_lt (lt_of_le_of_lt hp₀ hpq)) (c k) p hp₀
                      (le_of_lt hpq)) x
                  ≤ Real.sqrt n * chainThreshold B δ p})
          ∩ {x | Real.sqrt n * chainThreshold B δ (q₀ + k)
              < B.Δ (q₀ + k) (c k) x}) := by
      ext x
      simp only [hBs_def, chainB, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [hset]
    refine MeasurableSet.inter (MeasurableSet.const _) ?_
    refine MeasurableSet.inter ?_
      (measurableSet_lt measurable_const (B.Δ_meas (Nat.le_add_right q₀ k) (c k)))
    refine MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hp₀ =>
      MeasurableSet.iInter (fun hpq => ?_)))
    exact measurableSet_le (B.Δ_meas hp₀ _) measurable_const
  -- The chain links: B-link at level `q₀+k`, A-jump from level `q₀+k` to `q₀+(k+1)`,
  -- and the remainder `R K` at level `q₀+K`.
  set linkB : ℕ → Ω → ℝ := fun k x =>
    (f x - r k x) * Set.indicator (Bs k) (1 : Ω → ℝ) x with hlinkB_def
  set linkJ : ℕ → Ω → ℝ := fun k x =>
    (r (k+1) x - r k x) * Set.indicator (As k) (1 : Ω → ℝ) x with hlinkJ_def
  set Rrem : ℕ → Ω → ℝ := fun K x =>
    (f x - r K x) * Set.indicator (As K) (1 : Ω → ℝ) x with hRrem_def
  -- Integrability of the three link families.
  have hlinkB_int : ∀ k, Integrable (linkB k) P :=
    fun k => hgated_int k (Bs k) (hBs_meas k)
  have hRrem_int : ∀ K, Integrable (Rrem K) P :=
    fun K => hgated_int K (As K) (hAs_meas K)
  have hlinkJ_int : ∀ k, Integrable (linkJ k) P := by
    intro k
    have hjeq : linkJ k = fun x => B.jump (Nat.le_add_right q₀ k) (c (k+1)) x
        * Set.indicator (As k) (1 : Ω → ℝ) x := by
      funext x; simp only [hlinkJ_def]; rw [hjump_eq k]
    rw [hjeq]
    refine Integrable.mono' (hD_int k)
      (((B.jump_measurable hπ_meas (Nat.le_add_right q₀ k) (c (k+1))).mul
        (measurable_const.indicator (hAs_meas k))).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    calc |B.jump (Nat.le_add_right q₀ k) (c (k+1)) x| * |Set.indicator (As k) (1 : Ω → ℝ) x|
        ≤ D k x * 1 := by
          refine mul_le_mul (hjump_le k x) ?_ (abs_nonneg _) (hD_nn k x)
          by_cases hx : x ∈ As k
          · simp [Set.indicator_of_mem hx]
          · simp [Set.indicator_of_notMem hx]
      _ = D k x := mul_one _
  -- Per-level smallness predicate `small k x := D k x ≤ √n·a_{q₀+k}`.
  set small : ℕ → Ω → Prop := fun k x =>
    D k x ≤ Real.sqrt n * chainThreshold B δ (q₀ + k) with hsmall_def
  -- `small 0` always holds (this is exactly `hA_q0`, since `c 0 = i₀` and `D 0 = Δ_{q₀} i₀`).
  have hsmall0 : ∀ x, small 0 x := by
    intro x
    simp only [hsmall_def, hD_def, hc_def]
    rw [cellChain_zero B hf i₀ hi₀]
    have hcast : B.Δ (q₀ + 0) (Fin.cast (by rw [Nat.add_zero]) i₀) x = B.Δ q₀ i₀ x := by
      congr 1
    rw [hcast]
    have : Real.sqrt n * chainThreshold B δ (q₀ + 0) = Real.sqrt n * chainThreshold B δ q₀ := by
      norm_num
    rw [this]; exact hA_q0 x
  -- `x ∈ As k ↔ ∀ j ≤ k, small j x`.
  have hAs_iff : ∀ k x, x ∈ As k ↔ ∀ j ≤ k, small j x := by
    intro k x
    simp only [hAs_def, hc_def, Set.mem_setOf_eq]
    rw [chainA_chain_iff B hf δ n k x]
  -- `x ∈ Bs (k+1) ↔ (∀ j ≤ k, small j x) ∧ ¬ small (k+1) x`.
  have hBs_iff : ∀ k x, x ∈ Bs (k+1) ↔ (∀ j ≤ k, small j x) ∧ ¬ small (k+1) x := by
    intro k x
    simp only [hBs_def, hc_def, Set.mem_setOf_eq]
    rw [chainB_chain_iff B hf δ n (k+1) x]
    constructor
    · rintro ⟨_, hsm, hcr⟩
      exact ⟨fun j hj => hsm j (by omega), hcr⟩
    · rintro ⟨hsm, hcr⟩
      exact ⟨by omega, fun j hj => hsm j (by omega), hcr⟩
  -- The indicator value of `As k` at `x` (0/1, real).
  have hindA : ∀ k x, Set.indicator (As k) (1 : Ω → ℝ) x
      = if x ∈ As k then (1 : ℝ) else 0 := by
    intro k x; by_cases hx : x ∈ As k <;> simp [Set.indicator, hx]
  have hindB : ∀ k x, Set.indicator (Bs k) (1 : Ω → ℝ) x
      = if x ∈ Bs k then (1 : ℝ) else 0 := by
    intro k x; by_cases hx : x ∈ Bs k <;> simp [Set.indicator, hx]
  -- ===== THE FINITE TELESCOPE IDENTITY (pointwise in `x`, for each step count `K`). =====
  -- `f − r 0 = Rrem K + Σ_{k<K} linkJ k + Σ_{k<K} linkB (k+1)`.
  have htel : ∀ K x,
      f x - r 0 x
        = Rrem K x + (∑ k ∈ Finset.range K, linkJ k x)
            + (∑ k ∈ Finset.range K, linkB (k+1) x) := by
    intro K x
    induction K with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, add_zero]
        -- `Rrem 0 x = (f − r 0)·[As 0] = f − r 0` since `As 0` holds.
        have hA0 : x ∈ As 0 := (hAs_iff 0 x).mpr (fun j hj => by
          have : j = 0 := Nat.le_zero.mp hj
          subst this; exact hsmall0 x)
        simp only [hRrem_def, hindA, if_pos hA0, mul_one]
    | succ K ih =>
        -- Reduce to `Rrem (K+1) + linkJ K + linkB (K+1) = Rrem K`, then use `ih`.
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hstep : Rrem (K+1) x + linkJ K x + linkB (K+1) x = Rrem K x := by
          -- Indicator values via the smallness reductions.
          have hAK : x ∈ As K ↔ ∀ j ≤ K, small j x := hAs_iff K x
          have hAK1 : x ∈ As (K+1) ↔ ∀ j ≤ K+1, small j x := hAs_iff (K+1) x
          have hBK1 : x ∈ Bs (K+1) ↔ (∀ j ≤ K, small j x) ∧ ¬ small (K+1) x := hBs_iff K x
          simp only [hRrem_def, hlinkJ_def, hlinkB_def, hindA, hindB]
          by_cases hAk : x ∈ As K
          · -- chain still small through K
            have hsmK : ∀ j ≤ K, small j x := hAK.mp hAk
            by_cases hsk1 : small (K+1) x
            · -- still small at K+1: As(K+1) holds, Bs(K+1) fails
              have hAk1 : x ∈ As (K+1) := hAK1.mpr (fun j hj => by
                rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with h | h
                · exact hsmK j (by omega)
                · subst h; exact hsk1)
              have hBk1 : x ∉ Bs (K+1) := by
                rw [hBK1]; rintro ⟨_, hcr⟩; exact hcr hsk1
              simp only [if_pos hAk, if_pos hAk1, if_neg hBk1, mul_one, mul_zero, add_zero]
              ring
            · -- crosses at K+1: As(K+1) fails, Bs(K+1) holds
              have hAk1 : x ∉ As (K+1) := by
                rw [hAK1]; intro h; exact hsk1 (h (K+1) le_rfl)
              have hBk1 : x ∈ Bs (K+1) := hBK1.mpr ⟨hsmK, hsk1⟩
              simp only [if_pos hAk, if_neg hAk1, if_pos hBk1, mul_one, mul_zero, zero_add]
              ring
          · -- chain already crossed before K: all three indicators are 0
            have hAk1 : x ∉ As (K+1) := by
              rw [hAK1]; intro h; exact hAk (hAK.mpr (fun j hj => h j (by omega)))
            have hBk1 : x ∉ Bs (K+1) := by
              rw [hBK1]; rintro ⟨hsm, _⟩; exact hAk (hAK.mpr hsm)
            simp only [if_neg hAk, if_neg hAk1, if_neg hBk1, mul_zero, add_zero]
        -- Combine the split sums via `hstep` and the inductive hypothesis.
        rw [ih]
        -- rearrange so `hstep` applies
        have : Rrem (K+1) x + (∑ k ∈ Finset.range K, linkJ k x + linkJ K x)
              + (∑ k ∈ Finset.range K, linkB (k+1) x + linkB (K+1) x)
            = (Rrem (K+1) x + linkJ K x + linkB (K+1) x)
              + ((∑ k ∈ Finset.range K, linkJ k x) + (∑ k ∈ Finset.range K, linkB (k+1) x)) := by
          ring
        rw [this, hstep]
        ring
  -- ===== Apply `𝔾ₙ` to the telescope (linearity over the finite sum). =====
  -- `gn h := 𝔾ₙ h (ξ)`.
  set gn : (Ω → ℝ) → ℝ := fun h => empiricalProcess P n Y h with hgn_def
  have hgn_tel : ∀ K,
      gn (fun x => f x - r 0 x)
        = gn (Rrem K) + (∑ k ∈ Finset.range K, gn (linkJ k))
            + (∑ k ∈ Finset.range K, gn (linkB (k+1))) := by
    intro K
    -- Rewrite the integrand via the pointwise telescope identity.
    have hfun : (fun x => f x - r 0 x)
        = (fun x => Rrem K x
            + ((∑ k ∈ Finset.range K, linkJ k x) + (∑ k ∈ Finset.range K, linkB (k+1) x))) := by
      funext x; rw [htel K x]; ring
    rw [hfun]
    -- integrability of the two finite sums
    have hJsum_int : Integrable (fun x => ∑ k ∈ Finset.range K, linkJ k x) P :=
      integrable_finset_sum _ (fun k _ => hlinkJ_int k)
    have hBsum_int : Integrable (fun x => ∑ k ∈ Finset.range K, linkB (k+1) x) P :=
      integrable_finset_sum _ (fun k _ => hlinkB_int (k+1))
    simp only [hgn_def]
    rw [empiricalProcess_add P n Y (Rrem K)
        (fun x => (∑ k ∈ Finset.range K, linkJ k x) + (∑ k ∈ Finset.range K, linkB (k+1) x))
        (hRrem_int K) (hJsum_int.add hBsum_int)]
    rw [empiricalProcess_add P n Y (fun x => ∑ k ∈ Finset.range K, linkJ k x)
        (fun x => ∑ k ∈ Finset.range K, linkB (k+1) x) hJsum_int hBsum_int]
    rw [empiricalProcess_finset_sum P n Y (Finset.range K) linkJ (fun k _ => hlinkJ_int k)]
    rw [empiricalProcess_finset_sum P n Y (Finset.range K) (fun k => linkB (k+1))
        (fun k _ => hlinkB_int (k+1))]
    ring
  -- ===== Remainder bound: `|gn (Rrem K)| ≤ 2·n·(1/2)^K·δ → 0`. =====
  have hct_le : ∀ K, chainThreshold B δ (q₀ + K) ≤ (1/2 : ℝ)^K * δ := by
    intro K
    simp only [chainThreshold]
    rw [Nat.add_sub_cancel_left, div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ 1 + Real.sqrt (Real.log (1 + ↑(B.Nq (q₀ + K + 1)))) := by
      have := Real.sqrt_nonneg (Real.log (1 + ↑(B.Nq (q₀ + K + 1)))); linarith
    have hnum_nn : (0 : ℝ) ≤ (1/2 : ℝ)^K * δ :=
      mul_nonneg (pow_nonneg (by norm_num) K) hδ.le
    nlinarith [hnum_nn, h1]
  -- Pointwise uniform bound on `Rrem K`.
  set M : ℕ → ℝ := fun K => Real.sqrt n * ((1/2 : ℝ)^K * δ) with hM_def
  have hM_nn : ∀ K, 0 ≤ M K := fun K => by
    simp only [hM_def]; positivity
  have hRrem_bd : ∀ K x, |Rrem K x| ≤ M K := by
    intro K x
    simp only [hRrem_def]
    by_cases hx : x ∈ As K
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      have hsmall_K : small K x := (hAs_iff K x).mp hx K le_rfl
      calc |f x - r K x| ≤ D K x := hfr_le K x
        _ ≤ Real.sqrt n * chainThreshold B δ (q₀ + K) := hsmall_K
        _ ≤ Real.sqrt n * ((1/2 : ℝ)^K * δ) :=
            mul_le_mul_of_nonneg_left (hct_le K) hsn_nn
    · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
      exact hM_nn K
  -- `|gn (Rrem K)| ≤ 2·n·(1/2)^K·δ`.
  have hgnR_bd : ∀ K, |gn (Rrem K)| ≤ 2 * (n : ℝ) * ((1/2 : ℝ)^K * δ) := by
    intro K
    simp only [hgn_def, empiricalProcess]
    rw [abs_mul, abs_of_nonneg hsn_nn]
    -- `|empAvg − ∫| ≤ |empAvg| + |∫| ≤ M K + M K`
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
    have hempavg : |empiricalAvg (Rrem K) n Y| ≤ M K := by
      simp only [empiricalAvg]
      rw [abs_mul, abs_inv, Nat.abs_cast]
      have hsum_le : |∑ i, Rrem K (Y i)| ≤ (n : ℝ) * M K := by
        calc |∑ i, Rrem K (Y i)| ≤ ∑ i : Fin n, |Rrem K (Y i)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, M K := Finset.sum_le_sum (fun i _ => hRrem_bd K (Y i))
          _ = (n : ℝ) * M K := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc (n : ℝ)⁻¹ * |∑ i, Rrem K (Y i)|
          ≤ (n : ℝ)⁻¹ * ((n : ℝ) * M K) :=
            mul_le_mul_of_nonneg_left hsum_le (by positivity)
        _ = M K := by rw [← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
    have hintbd : |∫ x, Rrem K x ∂P| ≤ M K := by
      calc |∫ x, Rrem K x ∂P| ≤ ∫ x, |Rrem K x| ∂P := abs_integral_le_integral_abs
        _ ≤ ∫ _x, M K ∂P := by
            refine integral_mono ((hRrem_int K).abs) (integrable_const _) (fun x => hRrem_bd K x)
        _ = M K := by simp
    have hsqsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (by positivity)
    calc Real.sqrt n * |empiricalAvg (Rrem K) n Y - ∫ x, Rrem K x ∂P|
        ≤ Real.sqrt n * (M K + M K) := by
          refine mul_le_mul_of_nonneg_left ?_ hsn_nn
          calc |empiricalAvg (Rrem K) n Y - ∫ x, Rrem K x ∂P|
              ≤ |empiricalAvg (Rrem K) n Y| + |∫ x, Rrem K x ∂P| := abs_sub _ _
            _ ≤ M K + M K := add_le_add hempavg hintbd
      _ = 2 * (n : ℝ) * ((1/2 : ℝ)^K * δ) := by
          simp only [hM_def]
          linear_combination (2 * ((1/2 : ℝ)^K * δ)) * hsqsq
  -- `ofReal|gn (Rrem K)| → 0`, by squeeze under `ofReal (2 n (1/2)^K δ) → 0`.
  have hgnR_tendsto : Filter.Tendsto (fun K => ENNReal.ofReal |gn (Rrem K)|)
      Filter.atTop (𝓝 0) := by
    have hbd : Filter.Tendsto
        (fun K => ENNReal.ofReal (2 * (n : ℝ) * ((1/2 : ℝ)^K * δ))) Filter.atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
      have hgeom : Filter.Tendsto (fun K => (1/2 : ℝ)^K) Filter.atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have : Filter.Tendsto (fun K => 2 * (n : ℝ) * ((1/2 : ℝ)^K * δ)) Filter.atTop
          (𝓝 (2 * (n : ℝ) * (0 * δ))) := by
        exact (tendsto_const_nhds.mul ((hgeom.mul tendsto_const_nhds)))
      simpa using this
    -- ℝ≥0∞ squeeze: `0 ≤ ofReal|gn(Rrem K)| ≤ ofReal(2 n (1/2)^K δ) → 0`.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hbd (Filter.Eventually.of_forall (fun K => zero_le))
      (Filter.Eventually.of_forall (fun K => ?_))
    exact ENNReal.ofReal_le_ofReal (hgnR_bd K)
  -- ===== Per-`K` ENNReal triangle bound, then pass to the limit. =====
  -- The two target series (as `tsum`s of the per-level terms).
  set bTerm : ℕ → ℝ≥0∞ := fun q => ⨆ i : Fin (B.Nq (q₀ + q)),
      ⨆ (g : Ω → ℝ) (_ : g ∈ B.cell (q₀ + q) i), ENNReal.ofReal
        |empiricalProcess P n Y
          (fun x => (g x - B.π (q₀ + q) i x)
            * Set.indicator {y | chainB B δ n (q₀ + q) i y} (1 : Ω → ℝ) x)| with hbTerm_def
  set jTerm : ℕ → ℝ≥0∞ := fun q => ⨆ i : Fin (B.Nq (q₀ + q + 1)), ENNReal.ofReal
      |empiricalProcess P n Y (truncJump B δ n (Nat.le_add_right q₀ q) i)| with hjTerm_def
  set Sb : ℝ≥0∞ := ∑' q : ℕ, bTerm q with hSb_def
  set Sj : ℝ≥0∞ := ∑' q : ℕ, jTerm q with hSj_def
  -- Each B-link lands in the `(k+1)`-th B-term, each A-jump in the `k`-th jump-term.
  have hlinkB_le : ∀ k, ENNReal.ofReal |gn (linkB (k+1))| ≤ bTerm (k+1) := by
    intro k
    rw [hbTerm_def]
    -- `linkB (k+1) = (f − π_{q₀+(k+1)} (c (k+1)))·1{chainB …}`; pick `g = f`, `i = c (k+1)`.
    refine le_trans (le_of_eq ?_) (le_iSup_of_le (c (k+1)) (le_iSup₂_of_le f (hf_mem (k+1)) le_rfl))
    simp only [hgn_def, hlinkB_def, hr_def, hc_def, hBs_def]
  have hlinkJ_le : ∀ k, ENNReal.ofReal |gn (linkJ k)| ≤ jTerm k := by
    intro k
    rw [hjTerm_def]
    refine le_iSup_of_le (c (k+1)) (le_of_eq ?_)
    -- `linkJ k = truncJump B δ n (Nat.le_add_right q₀ k) (c (k+1))`.
    have heq : linkJ k = truncJump B δ n (Nat.le_add_right q₀ k) (c (k+1)) := by
      funext x
      simp only [hlinkJ_def, truncJump]
      rw [hjump_eq k]
      congr 2
      simp only [hAs_def, hc_def]
      rw [cellChain_parent B hf k]
    rw [hgn_def, heq]
  -- Finite-sum ENNReal triangle: `ofReal|Σ a_k| ≤ Σ ofReal|a_k|`.
  have htri_fin : ∀ (s : Finset ℕ) (a : ℕ → ℝ),
      ENNReal.ofReal |∑ k ∈ s, a k| ≤ ∑ k ∈ s, ENNReal.ofReal |a k| := by
    intro s a
    induction s using Finset.induction with
    | empty => simp
    | insert b s hb ih =>
        rw [Finset.sum_insert hb, Finset.sum_insert hb]
        calc ENNReal.ofReal |a b + ∑ k ∈ s, a k|
            ≤ ENNReal.ofReal (|a b| + |∑ k ∈ s, a k|) :=
              ENNReal.ofReal_le_ofReal (abs_add_le _ _)
          _ ≤ ENNReal.ofReal |a b| + ENNReal.ofReal |∑ k ∈ s, a k| := ENNReal.ofReal_add_le
          _ ≤ ENNReal.ofReal |a b| + ∑ k ∈ s, ENNReal.ofReal |a k| := add_le_add le_rfl ih
  -- The per-`K` bound.
  have hperK : ∀ K, ENNReal.ofReal |gn (fun x => f x - B.π q₀ i₀ x)|
      ≤ ENNReal.ofReal |gn (Rrem K)| + (Sb + Sj) := by
    intro K
    have hrw : (fun x => f x - B.π q₀ i₀ x) = (fun x => f x - r 0 x) := by rw [hr0]
    rw [hrw, hgn_tel K]
    -- triangle (left-associated), then dominate the two finite sums by their tsums
    have hAbsA : ENNReal.ofReal |gn (Rrem K) + (∑ k ∈ Finset.range K, gn (linkJ k))
            + (∑ k ∈ Finset.range K, gn (linkB (k+1)))|
        ≤ ENNReal.ofReal |gn (Rrem K)|
            + ENNReal.ofReal |∑ k ∈ Finset.range K, gn (linkJ k)|
            + ENNReal.ofReal |∑ k ∈ Finset.range K, gn (linkB (k+1))| := by
      refine le_trans (ENNReal.ofReal_le_ofReal (abs_add_le _ _)) ?_
      refine le_trans ENNReal.ofReal_add_le ?_
      refine add_le_add ?_ le_rfl
      refine le_trans (ENNReal.ofReal_le_ofReal (abs_add_le _ _)) ENNReal.ofReal_add_le
    have hJsum_le_Sj : ENNReal.ofReal |∑ k ∈ Finset.range K, gn (linkJ k)| ≤ Sj := by
      refine le_trans (htri_fin _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun k _ => hlinkJ_le k)) ?_
      rw [hSj_def]; exact ENNReal.sum_le_tsum _
    have hBsum_le_Sb : ENNReal.ofReal |∑ k ∈ Finset.range K, gn (linkB (k+1))| ≤ Sb := by
      refine le_trans (htri_fin _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun k _ => hlinkB_le k)) ?_
      rw [hSb_def]
      refine le_trans (le_of_eq ?_)
        (ENNReal.sum_le_tsum ((Finset.range K).map ⟨Nat.succ, Nat.succ_injective⟩))
      rw [Finset.sum_map]; rfl
    calc ENNReal.ofReal |gn (Rrem K) + (∑ k ∈ Finset.range K, gn (linkJ k))
            + (∑ k ∈ Finset.range K, gn (linkB (k+1)))|
        ≤ ENNReal.ofReal |gn (Rrem K)|
            + ENNReal.ofReal |∑ k ∈ Finset.range K, gn (linkJ k)|
            + ENNReal.ofReal |∑ k ∈ Finset.range K, gn (linkB (k+1))| := hAbsA
      _ ≤ ENNReal.ofReal |gn (Rrem K)| + Sj + Sb :=
          add_le_add (add_le_add le_rfl hJsum_le_Sj) hBsum_le_Sb
      _ = ENNReal.ofReal |gn (Rrem K)| + (Sb + Sj) := by
          rw [add_assoc, add_comm Sj Sb]
  -- ===== Pass to the limit `K → ∞`: `LHS ≤ 0 + (Sb + Sj)`. =====
  have hlim : Filter.Tendsto (fun K => ENNReal.ofReal |gn (Rrem K)| + (Sb + Sj))
      Filter.atTop (𝓝 (Sb + Sj)) := by
    have := hgnR_tendsto.add (tendsto_const_nhds (x := Sb + Sj))
    rwa [zero_add] at this
  simp only [hgn_def] at hperK hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards with K
  simpa using hperK K

omit [MeasurableSpace Ξ] in
/-- The first-crossing data give the pointwise tail-free head/A/B telescope
for the full clamped class (vdV Lemma 19.34, p.287). -/
theorem fullClamped_chain_supNorm_le_pointwise
    [IsProbabilityMeasure P]
    (D : RegularizedFullClampedPartitionData F P Φ δ n t)
    {X : ℕ → Ξ → Ω} (ξ : Ξ)
    (hδ : 0 < δ) (hn : 1 ≤ n) :
    supNormOver (truncateClass F t)
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ≤
      (⨆ i : Fin (D.base.partition.Nq 0), ENNReal.ofReal
        |empiricalProcess P n (fun j : Fin n => X j.val ξ) (D.base.partition.π 0 i)|) +
        (∑' k : ℕ, ⨆ i : Fin (D.base.partition.Nq (0 + k)),
          ⨆ (f : Ω → ℝ) (_ : f ∈ D.base.partition.cell (0 + k) i),
            ENNReal.ofReal |empiricalProcess P n (fun j : Fin n => X j.val ξ)
              (fun x => (f x - D.base.partition.π (0 + k) i x) *
                Set.indicator
                  {y | chainB D.base.partition (8 * δ) n (0 + k) i y}
                  (1 : Ω → ℝ) x)|) +
        (∑' k : ℕ, ⨆ i : Fin (D.base.partition.Nq (0 + k + 1)),
          ENNReal.ofReal |empiricalProcess P n (fun j : Fin n => X j.val ξ)
            (truncJump D.base.partition (8 * δ) n (Nat.le_add_right 0 k) i)|) := by
  classical
  let B := D.base.partition
  have h8δ : 0 < 8 * δ := by positivity
  refine iSup₂_le fun f hf => ?_
  obtain ⟨i₀, hi₀⟩ := B.cover (Nat.zero_le 0) f hf
  have hf_int : Integrable f P := by
    refine (MemLp.integrable one_le_two ?_)
    exact ⟨(D.base.truncated_measurable f hf).aestronglyMeasurable,
      lt_trans (D.base.truncated_L2 f hf) ENNReal.ofReal_lt_top⟩
  have hπ_mem : B.π 0 i₀ ∈ truncateClass F t :=
    B.cell_subset (Nat.zero_le 0) i₀ (B.π_mem (Nat.zero_le 0) i₀)
  have hπ_int : Integrable (B.π 0 i₀) P := by
    refine (MemLp.integrable one_le_two ?_)
    exact ⟨(B.π_meas (Nat.zero_le 0) i₀).aestronglyMeasurable,
      lt_trans (D.base.truncated_L2 _ hπ_mem) ENNReal.ofReal_lt_top⟩
  have hrep : truncRep B (fun _ => t) (8 * δ) n 0 i₀ = B.π 0 i₀ := by
    funext x
    simp only [truncRep]
    rw [Set.indicator_of_mem]
    · simp
    · exact D.head_visible
  let G : (Ω → ℝ) → ℝ := fun g =>
    empiricalProcess P n (fun i : Fin n => X i.val ξ) g
  have hsplit : G f = G (truncRep B (fun _ => t) (8 * δ) n 0 i₀)
      + G (fun x => f x - B.π 0 i₀ x) := by
    rw [hrep]
    change empiricalProcess P n (fun i : Fin n => X i.val ξ) f = _
    have hfun : f = fun x => B.π 0 i₀ x + (f x - B.π 0 i₀ x) := by
      funext x
      ring
    conv_lhs => rw [hfun]
    exact empiricalProcess_add P n _ _ _ hπ_int (hf_int.sub hπ_int)
  have hhead : ENNReal.ofReal |G (truncRep B (fun _ => t) (8 * δ) n 0 i₀)| ≤
      ⨆ i : Fin (B.Nq 0), ENNReal.ofReal
        |empiricalProcess P n (fun j : Fin n => X j.val ξ) (B.π 0 i)| := by
    rw [hrep]
    exact le_iSup (fun i : Fin (B.Nq 0) => ENNReal.ofReal
      |empiricalProcess P n (fun j : Fin n => X j.val ξ) (B.π 0 i)|) i₀
  have htail := fullClamped_Gn_telescope_link_bound (X := X) B B.π_meas
    D.base.truncated_measurable h8δ n hn ξ hf i₀ hi₀ (D.initial_small i₀)
  have htri : ENNReal.ofReal |G f| ≤
      ENNReal.ofReal |G (truncRep B (fun _ => t) (8 * δ) n 0 i₀)| +
        ENNReal.ofReal |G (fun x => f x - B.π 0 i₀ x)| := by
    rw [hsplit]
    exact le_trans (ENNReal.ofReal_le_ofReal (abs_add_le _ _)) ENNReal.ofReal_add_le
  change ENNReal.ofReal |G f| ≤ _
  rw [add_assoc]
  exact htri.trans (add_le_add hhead htail)

set_option linter.unusedVariables false in
/-- The tail-free pointwise chain has a measurable finite-head plus A/B-tsum
majorant, without assuming measurability of the external envelope `Φ`. -/
theorem fullClamped_chain_measurableMajorant_dyadic_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (Ξ : Type*) [MeasurableSpace Ξ]
        (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (δ : ℝ) (n : ℕ) (t : ℝ)
        (D : RegularizedFullClampedPartitionData F P Φ δ n t)
        (X : ℕ → Ξ → Ω)
        (hX_meas : ∀ i, Measurable (X i))
        (hX_iindep : ProbabilityTheory.iIndepFun X μ)
        (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
        (hX_law : μ.map (X 0) = P)
        (hδ : 0 < δ),
      ∃ Maj : Ξ → ℝ≥0∞, Measurable Maj ∧
      (∀ ξ, supNormOver (truncateClass F t)
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ≤ Maj ξ) ∧
      ∫⁻ ξ, Maj ξ ∂μ ≤ ENNReal.ofReal c *
        (∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ) *
          entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P) := by
  classical
  obtain ⟨cH, hcH, hH⟩ := fullClamped_chain_head_dyadic_bound
  obtain ⟨cA, hcA, hA⟩ := fullClamped_chain_A_dyadic_bound
  obtain ⟨cB, hcB, hB⟩ := fullClamped_chain_Bseries_dyadic_bound
  obtain ⟨cM, hcM, hM⟩ := fullClamped_chain_Bmean_dyadic_bound
  set c : ℝ := 15 * (cH + 3 * cB + cA + cM) with hc_def
  have hc : 0 < c := by
    rw [hc_def]
    positivity
  refine ⟨c, hc, ?_⟩
  intro Ω _ P _ Ξ _ μ _ F Φ δ n t D X hX_meas hX_iindep hX_idem hX_law hδ
  by_cases hn0 : n = 0
  · subst n
    refine ⟨fun _ => 0, measurable_const, ?_, ?_⟩
    · intro ξ
      simp [supNormOver, empiricalProcess, empiricalAvg]
    · simp
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have h8δ : 0 < 8 * δ := by positivity
    let B := D.base.partition
    -- The three measurable pieces corresponding to the pointwise chain.
    set head : Ξ → ℝ≥0∞ := fun ξ => ⨆ i : Fin (B.Nq 0), ENNReal.ofReal
        |empiricalProcess P n (fun k : Fin n => X k.val ξ)
          (truncRep B (fun _ => t) (8 * δ) n 0 i)| with hhead_def
    set jump : ℕ → Ξ → ℝ≥0∞ := fun q ξ =>
      ⨆ i : Fin (B.Nq (0 + q + 1)), ENNReal.ofReal
        |empiricalProcess P n (fun k : Fin n => X k.val ξ)
          (truncJump B (8 * δ) n (Nat.le_add_right 0 q) i)| with hjump_def
    set bmeanConst : ℕ → ℝ≥0∞ := fun q =>
      4 * ENNReal.ofReal (Real.sqrt n) *
        ⨆ i : Fin (B.Nq (0 + q)), ∫⁻ x, ENNReal.ofReal
          (B.Δ (0 + q) i x *
            Set.indicator {y | chainB B (8 * δ) n (0 + q) i y}
              (1 : Ω → ℝ) x) ∂P with hbmeanConst_def
    set oscDom : ℕ → Ξ → ℝ≥0∞ := fun q ξ =>
      3 * (⨆ i : Fin (B.Nq (0 + q)), ENNReal.ofReal
        |empiricalProcess P n (fun k : Fin n => X k.val ξ)
          (truncOsc B (8 * δ) n (0 + q) i)|) + bmeanConst q with hoscDom_def
    set Maj : Ξ → ℝ≥0∞ := fun ξ =>
      head ξ + (∑' q, oscDom q ξ) + (∑' q, jump q ξ) with hMaj_def
    -- Measurability of the A/B gates at initial index zero.
    have hchainA_meas (q : ℕ) (i : Fin (B.Nq q)) :
        MeasurableSet {x | chainA B (8 * δ) n q i x} := by
      have hset : {x | chainA B (8 * δ) n q i x} =
          ⋂ (p : ℕ) (hp₀ : 0 ≤ p) (hpq : p ≤ q),
            {x | B.Δ p (B.ancestor (le_trans hp₀ hpq) i p hp₀ hpq) x ≤
              Real.sqrt n * chainThreshold B (8 * δ) p} := by
        ext x
        simp only [chainA, Set.mem_setOf_eq, Set.mem_iInter]
      rw [hset]
      refine MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hp₀ =>
        MeasurableSet.iInter (fun hpq => ?_)))
      exact measurableSet_le (B.Δ_meas hp₀ _) measurable_const
    have hchainB_meas (q : ℕ) (i : Fin (B.Nq q)) :
        MeasurableSet {x | chainB B (8 * δ) n q i x} := by
      have hset : {x | chainB B (8 * δ) n q i x} = {_x : Ω | 0 < q} ∩
          ((⋂ (p : ℕ) (hp₀ : 0 ≤ p) (hpq : p < q),
              {x | B.Δ p
                (B.ancestor (le_of_lt (lt_of_le_of_lt hp₀ hpq)) i p hp₀
                  (le_of_lt hpq)) x ≤ Real.sqrt n * chainThreshold B (8 * δ) p}) ∩
            {x | Real.sqrt n * chainThreshold B (8 * δ) q < B.Δ q i x}) := by
        ext x
        simp only [chainB, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      rw [hset]
      refine MeasurableSet.inter (MeasurableSet.const _) ?_
      refine MeasurableSet.inter ?_
        (measurableSet_lt measurable_const (B.Δ_meas (Nat.zero_le q) i))
      refine MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hp₀ =>
        MeasurableSet.iInter (fun hpq => ?_)))
      exact measurableSet_le (B.Δ_meas hp₀ _) measurable_const
    have hemp_meas (g : Ω → ℝ) (hg : Measurable g) : Measurable (fun ξ : Ξ =>
        ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ) g|) := by
      have hE : Measurable (fun ξ : Ξ =>
          empiricalProcess P n (fun i : Fin n => X i.val ξ) g) := by
        unfold empiricalProcess empiricalAvg
        refine Measurable.const_mul (Measurable.sub ?_ measurable_const) _
        refine Measurable.const_mul ?_ _
        exact Finset.measurable_sum Finset.univ
          (fun i _ => hg.comp (hX_meas i.val))
      have habs : (fun ξ : Ξ =>
          |empiricalProcess P n (fun i : Fin n => X i.val ξ) g|) =
          (fun ξ : Ξ =>
            ‖empiricalProcess P n (fun i : Fin n => X i.val ξ) g‖) := by
        funext ξ
        exact (Real.norm_eq_abs _).symm
      exact Measurable.ennreal_ofReal (habs ▸ hE.norm)
    have hhead_meas : Measurable head := by
      rw [hhead_def]
      refine Measurable.iSup (fun i => hemp_meas _ ?_)
      refine (B.π_meas (Nat.zero_le 0) i).mul ?_
      exact measurable_one.indicator (measurableSet_le measurable_const measurable_const)
    have hjump_meas : ∀ q, Measurable (jump q) := by
      intro q
      rw [hjump_def]
      refine Measurable.iSup (fun i => hemp_meas _ ?_)
      refine (B.jump_measurable B.π_meas (Nat.le_add_right 0 q) i).mul ?_
      exact measurable_one.indicator
        (hchainA_meas (0 + q) (B.parent (Nat.le_add_right 0 q) i))
    have hoscDom_meas : ∀ q, Measurable (oscDom q) := by
      intro q
      rw [hoscDom_def]
      refine (Measurable.const_mul ?_ 3).add measurable_const
      refine Measurable.iSup (fun i => hemp_meas _ ?_)
      exact (B.Δ_meas (Nat.zero_le (0 + q)) i).mul
        (measurable_const.indicator (hchainB_meas (0 + q) i))
    have hMaj_meas : Measurable Maj := by
      rw [hMaj_def]
      exact (hhead_meas.add (Measurable.ennreal_tsum hoscDom_meas)).add
        (Measurable.ennreal_tsum hjump_meas)
    -- `head` is `levelRepSup`: head visibility makes truncation inert.
    have hrep : ∀ i : Fin (B.Nq 0),
        truncRep B (fun _ => t) (8 * δ) n 0 i = B.π 0 i := by
      intro i
      funext x
      simp only [truncRep]
      rw [Set.indicator_of_mem]
      · simp
      · simpa using D.head_visible
    have hptwise : ∀ ξ, supNormOver (truncateClass F t)
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ≤ Maj ξ := by
      intro ξ
      have hpt := fullClamped_chain_supNorm_le_pointwise (X := X) D ξ hδ hn
      have hhead_eq : (⨆ i : Fin (B.Nq 0), ENNReal.ofReal
          |empiricalProcess P n (fun j : Fin n => X j.val ξ) (B.π 0 i)|) = head ξ := by
        rw [hhead_def]
        simp_rw [hrep]
      refine hpt.trans ?_
      simp only [hMaj_def]
      rw [← hhead_eq]
      refine add_le_add (add_le_add le_rfl ?_) le_rfl
      refine ENNReal.tsum_le_tsum (fun q => ?_)
      simpa only [hoscDom_def, hbmeanConst_def] using
        supNormOver_link_meanSplit_pointwise_le B B.π_meas
          D.base.truncated_measurable (X := X) (δ := 8 * δ) n
            (Nat.zero_le (0 + q)) ξ
    refine ⟨Maj, hMaj_meas, hptwise, ?_⟩
    -- Integral identities for the three pieces.
    have hhead_int : ∫⁻ ξ, head ξ ∂μ =
        levelRepSup B μ X (fun _ => t) (8 * δ) n 0 := rfl
    have hjump_int : ∀ q, ∫⁻ ξ, jump q ξ ∂μ =
        levelJumpSup B μ X (8 * δ) n (Nat.le_add_right 0 q) := fun q => rfl
    have hoscDom_int : ∀ q, ∫⁻ ξ, oscDom q ξ ∂μ =
        3 * levelOscSup B μ X (8 * δ) n (0 + q) + bmeanConst q := by
      intro q
      rw [hoscDom_def]
      rw [lintegral_add_right' _ measurable_const.aemeasurable]
      rw [lintegral_const_mul' _ _ (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)]
      rw [lintegral_const, measure_univ, mul_one]
      rfl
    have hosc_sum_meas : Measurable (fun ξ => ∑' q, oscDom q ξ) :=
      Measurable.ennreal_tsum hoscDom_meas
    have hjump_sum_meas : Measurable (fun ξ => ∑' q, jump q ξ) :=
      Measurable.ennreal_tsum hjump_meas
    have hMaj_split : ∫⁻ ξ, Maj ξ ∂μ =
        (∫⁻ ξ, head ξ ∂μ) + (∑' q, ∫⁻ ξ, oscDom q ξ ∂μ) +
          (∑' q, ∫⁻ ξ, jump q ξ ∂μ) := by
      rw [hMaj_def]
      rw [lintegral_add_right' _ hjump_sum_meas.aemeasurable,
        lintegral_add_left' hhead_meas.aemeasurable,
        lintegral_tsum (fun q => (hoscDom_meas q).aemeasurable),
        lintegral_tsum (fun q => (hjump_meas q).aemeasurable)]
    have hosc_sum : (∑' q, ∫⁻ ξ, oscDom q ξ ∂μ) =
        3 * (∑' q : ℕ, levelOscSup B μ X (8 * δ) n (0 + q)) +
          Bmean B (8 * δ) n := by
      simp only [hoscDom_int]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hbmeanConst_def, Bmean]
    have hjump_sum : (∑' q, ∫⁻ ξ, jump q ξ ∂μ) =
        ∑' q : ℕ, levelJumpSup B μ X (8 * δ) n (Nat.le_add_right 0 q) := by
      simp only [hjump_int]
    set S8 : ℝ≥0∞ := ∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ)^q * (8 * δ)) *
      entropyIntegrand ((1 / 2 : ℝ)^q * (8 * δ)) F P with hS8_def
    set S : ℝ≥0∞ := ∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ)^q * δ) *
      entropyIntegrand ((1 / 2 : ℝ)^q * δ) F P with hS_def
    have hH8 := hH Ω P Ξ μ F Φ 0 n (8 * δ) t D.base X
      hX_meas hX_iindep hX_idem hX_law h8δ
    have hH8' : levelRepSup B μ X (fun _ => t) (8 * δ) n 0 ≤
        ENNReal.ofReal cH * S8 := by
      refine hH8.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (zero_le)
      rw [hS8_def]
      simpa only [pow_zero, one_mul] using (ENNReal.le_tsum
        (f := fun q : ℕ => ENNReal.ofReal ((1 / 2 : ℝ)^q * (8 * δ)) *
          entropyIntegrand ((1 / 2 : ℝ)^q * (8 * δ)) F P) 0)
    have hA8 := hA Ω P Ξ μ F Φ 0 n (8 * δ) t D.base X
      hX_meas hX_iindep hX_idem hX_law h8δ
    have hB8 := hB Ω P Ξ μ F Φ 0 n (8 * δ) t D.base X
      hX_meas hX_iindep hX_idem hX_law h8δ
    have hM8 := hM Ω P F Φ 0 n (8 * δ) t D.base h8δ
    rw [← hS8_def] at hA8 hB8 hM8
    have hscale : S8 ≤ 15 * S := by
      rw [hS8_def, hS_def]
      exact fullClamped_factorEight_dyadic_le_target hδ
    have hc_ofReal : ENNReal.ofReal c =
        15 * (ENNReal.ofReal cH + 3 * ENNReal.ofReal cB +
          ENNReal.ofReal cA + ENNReal.ofReal cM) := by
      rw [hc_def, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 15),
        ENNReal.ofReal_add (by positivity) hcM.le,
        ENNReal.ofReal_add (by positivity) hcA.le,
        ENNReal.ofReal_add hcH.le (by positivity),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    rw [hMaj_split, hhead_int, hosc_sum, hjump_sum]
    calc
      levelRepSup B μ X (fun _ => t) (8 * δ) n 0 +
            (3 * (∑' q : ℕ, levelOscSup B μ X (8 * δ) n (0 + q)) +
              Bmean B (8 * δ) n) +
            (∑' q : ℕ, levelJumpSup B μ X (8 * δ) n (Nat.le_add_right 0 q))
          ≤ ENNReal.ofReal cH * S8 +
              (3 * (ENNReal.ofReal cB * S8) + ENNReal.ofReal cM * S8) +
              ENNReal.ofReal cA * S8 := by
            exact add_le_add (add_le_add hH8' (add_le_add
              (mul_le_mul_of_nonneg_left hB8 (zero_le)) hM8)) hA8
      _ = (ENNReal.ofReal cH + 3 * ENNReal.ofReal cB +
            ENNReal.ofReal cA + ENNReal.ofReal cM) * S8 := by ring
      _ ≤ (ENNReal.ofReal cH + 3 * ENNReal.ofReal cB +
            ENNReal.ofReal cA + ENNReal.ofReal cM) * (15 * S) := by
          exact mul_le_mul_of_nonneg_left hscale (zero_le)
      _ = ENNReal.ofReal c * S := by rw [hc_ofReal]; ring

/-- The full-class dyadic series is bounded by the bracketing entropy integral
at `δ` (vdV Lemma 19.34, p.288). -/
theorem fullClamped_dyadic_to_J
    (hδ : 0 < δ) :
    (∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ) *
        entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P) ≤
      2 * bracketingEntropyIntegral δ F P := by
  exact dyadic_sum_le_bracketingEntropyIntegral hδ

set_option linter.unusedVariables false in
/-- Partition-level, tail-free full-clamped maximal bound. It uses the structural
object constructed by `exists_fullClampedNestedPartition`. -/
theorem bracketingMaximal_of_fullClampedPartition :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (Ξ : Type*) [MeasurableSpace Ξ]
        (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
        (δ : ℝ) (n : ℕ) (t : ℝ)
        (D : RegularizedFullClampedPartitionData F P Φ δ n t)
        (X : ℕ → Ξ → Ω)
        (hX_meas : ∀ i, Measurable (X i))
        (hX_iindep : ProbabilityTheory.iIndepFun X μ)
        (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
        (hX_law : μ.map (X 0) = P)
        (hδ : 0 < δ),
      outerExpectation μ (fun ξ => supNormOver (truncateClass F t)
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)) ≤
        ENNReal.ofReal c * bracketingEntropyIntegral δ F P := by
  obtain ⟨cM, hcM, hM⟩ := fullClamped_chain_measurableMajorant_dyadic_bound
  refine ⟨2 * cM, mul_pos (by norm_num) hcM, ?_⟩
  intro Ω _ P _ Ξ _ μ _ F Φ δ n t D X hX_meas hX_iindep hX_idem hX_law hδ
  obtain ⟨Maj, hMaj_meas, hMaj, hMaj_int⟩ :=
    hM Ω P Ξ μ F Φ δ n t D X hX_meas hX_iindep hX_idem hX_law hδ
  calc
    outerExpectation μ (fun ξ => supNormOver (truncateClass F t)
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f))
        ≤ outerExpectation μ Maj := outerExpectation_mono hMaj
    _ = ∫⁻ ξ, Maj ξ ∂μ := outerExpectation_eq_lintegral hMaj_meas
    _ ≤ ENNReal.ofReal cM *
          (∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ) *
            entropyIntegrand ((1 / 2 : ℝ) ^ k * δ) F P) := hMaj_int
    _ ≤ ENNReal.ofReal cM * (2 * bracketingEntropyIntegral δ F P) := by
      gcongr
      exact fullClamped_dyadic_to_J hδ
    _ = ENNReal.ofReal (2 * cM) * bracketingEntropyIntegral δ F P := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
      ring

end AsymptoticStatistics.EmpiricalProcess
