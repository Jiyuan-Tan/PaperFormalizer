module
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVecNative
public import StatLean.AsymptoticStatistics.Asymptotics.OneStepVec
public import StatLean.AsymptoticStatistics.OneStepEstimator.AsymptoticExpansion
public import StatLean.AsymptoticStatistics.DQM.Defs
public import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw
public import StatLean.AsymptoticStatistics.ForMathlib.SplitProductMoments
public import StatLean.AsymptoticStatistics.ForMathlib.MeasurableCountableRange
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.LocalContiguity
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.AsymptoticRepresentation
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.WeightedScoreEmpiricalLinearization
public import StatLean.AsymptoticStatistics.Core.EfficiencyOperational

@[expose] public section

/-!
# One-step estimator semiparametric efficiency (vector θ)

This file proves the vector-parameter (`θ ∈ ℝᵈ`) form of vdV Theorem 25.57 for
the one-step estimator.

## Native vector formulation

The one-step estimator solves the vector estimating equation `√n·𝕡_n ℓ̃_{θ̂_n} = o_P` up to
one Newton step, encoded by the vector/matrix assumptions
`ZEstimatorTaylorCoreNative_vec` (`hPD`, the vector estimating equation `score_eq_vec`, the
matrix Bartlett identity `matrix_bartlett`, and the matrix DQM-Taylor remainder `matrix_taylor`).
The theorem `ZEstimatorVecNative.mle_asympLinear_of_nativeTaylorCore_vec` then
gives its asymptotic linearity directly, with influence `Ĩ⁻¹ℓ̃ = candidateVecEIF` **by
construction** (arbitrary, non-diagonal `Ĩ`) and no coordinatewise identification.

Reference: vdV §25.5, thm:25.57 (vector form). Main declarations:
`oneStep_asympLinear_native_vec`, `oneStep_semiparametricallyEfficient_native_vec`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal Matrix.Norms.L2Operator

namespace AsymptoticStatistics.Asymptotics.Discharge.OneStepVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EIF
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVecNative

variable {Ω : Type} [MeasurableSpace Ω]
variable {d : ℕ}
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
variable {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
variable [proj : T_nuis.HasOrthogonalProjection] {e : Fin d → Θ}
variable {estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
variable {score_func_seq : ∀ n, (Fin n → Ω) → (Ω → EuclideanSpace ℝ (Fin d))}
variable {score_l_dot : Matrix (Fin d) (Fin d) (Lp ℝ 2 P)}
variable {θ₀ : EuclideanSpace ℝ (Fin d)}

/-- **vdV Theorem 25.57 (vector form): asymptotic linearity of the one-step
estimator.** The vector estimating equation and matrix Taylor identity imply
asymptotic linearity at `P` with influence tuple `candidateVecEIF S_θ T_nuis e`
and centering `θ₀`. No diagonal coordinatewise identification is assumed. -/
theorem oneStep_asympLinear_native_vec
    (h : @ZEstimatorTaylorCoreNative_vec Ω _ d P _ Θ _ _ _ S_θ T_nuis proj e estimator
            score_func_seq score_l_dot θ₀) :
    AsymptoticallyLinearAt_vec estimator P
      (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) θ₀ :=
  @mle_asympLinear_of_nativeTaylorCore_vec Ω _ d P _ Θ _ _ _ S_θ T_nuis
    proj e estimator score_func_seq score_l_dot θ₀ h

/-- vdV thm:25.57 (vector form) — semiparametric efficiency of the one-step
estimator. From the vector/matrix assumptions
`ZEstimatorTaylorCoreNative_vec` (solved estimating equation etc.) plus the EIF-construction
inputs (`h_mem`, `h_Dψ`) and `ψ P = θ₀`, the one-step estimator is asymptotically efficient
at `P` relative to the tangent space `T` for the vector functional `ψ`. The matrix
formulation carries no diagonal-only coordinatewise identification. -/
theorem oneStep_semiparametricallyEfficient_native_vec
    (h : @ZEstimatorTaylorCoreNative_vec Ω _ d P _ Θ _ _ _ S_θ T_nuis proj e estimator
            score_func_seq score_l_dot θ₀)
    {T : Submodule ℝ ↥(L2ZeroMean P)} {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h_mem : ∀ j, @candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e j ∈ T)
    (h_Dψ : ∀ (j : Fin d) (g : T),
      (EuclideanSpace.proj j ∘L Dψ) g
        = ⟪@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e j,
            (g : ↥(L2ZeroMean P))⟫_ℝ)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt_vec estimator ψ P T :=
  @mle_semiparametricallyEfficient_of_nativeTaylorCore_vec Ω _ d P _ Θ _ _ _
    S_θ T_nuis proj e estimator score_func_seq score_l_dot θ₀ h T Dψ h_mem h_Dψ ψ h_ψ

/-! ## Vector forms of conditions (25.55)--(25.57) -/

open AsymptoticStatistics
open AsymptoticStatistics.Asymptotics.OneStepVec
open AsymptoticStatistics.OneStepEstimator
open AsymptoticStatistics.Core.EfficiencyOperational

private theorem TendstoInProbZero.of_contiguous
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)]
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
    {P Q : ∀ n, Measure (S n)} {Z : ∀ n, S n → G}
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (hcont : Contiguity.Contiguous atTop P Q)
    (hZ : ∀ n, Measurable (Z n))
    (hP : TendstoInProbZero P Z) :
    TendstoInProbZero Q Z := by
  intro ε hε
  have hstat := (Contiguity.contiguous_iff_tendsto_zero_statistics P Q).mp hcont
    (fun n x => ‖Z n x‖) (fun n => (hZ n).norm) (by
      intro δ hδ
      rw [← ENNReal.tendsto_toReal_zero_iff]
      simpa only [Real.norm_eq_abs, abs_norm, measureReal_def] using hP δ hδ) ε hε
  rw [← ENNReal.tendsto_toReal_zero_iff] at hstat
  simpa only [Real.norm_eq_abs, abs_norm, measureReal_def] using hstat

private theorem TendstoInProbZero.add
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)]
    {G : Type*} [NormedAddCommGroup G]
    {P : ∀ n, Measure (S n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z W : ∀ n, S n → G}
    (hZ : TendstoInProbZero P Z) (hW : TendstoInProbZero P W) :
    TendstoInProbZero P (fun n x => Z n x + W n x) := by
  intro ε hε
  have hsub (n : ℕ) : {x | ε ≤ ‖Z n x + W n x‖} ⊆
      {x | ε / 2 ≤ ‖Z n x‖} ∪ {x | ε / 2 ≤ ‖W n x‖} := by
    intro x hx
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hnot
    exact (not_lt_of_ge hx) <| (norm_add_le _ _).trans_lt (by linarith [hnot.1, hnot.2])
  have hsum := (hZ (ε / 2) (half_pos hε)).add (hW (ε / 2) (half_pos hε))
  refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) (by simpa using hsum)
  exact (measureReal_mono (hsub n)).trans (measureReal_union_le _ _)

private theorem TendstoInProbZero.neg
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)]
    {G : Type*} [NormedAddCommGroup G]
    {P : ∀ n, Measure (S n)} {Z : ∀ n, S n → G}
    (hZ : TendstoInProbZero P Z) :
    TendstoInProbZero P (fun n x => -Z n x) := by
  intro ε hε
  simpa only [norm_neg] using hZ ε hε

private theorem IsRootNBoundedSeq.tendsto
    {k : ℕ} {thetaSeq : ℕ → EuclideanSpace ℝ (Fin k)}
    {theta0 : EuclideanSpace ℝ (Fin k)}
    (h : IsRootNBoundedSeq thetaSeq theta0) :
    Tendsto thetaSeq atTop (𝓝 theta0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨C, hC⟩ := h
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ * max C 0) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa only [zero_mul] using! hsqrt.inv_tendsto_atTop.mul_const (max C 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
    (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [hC, Filter.eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hbound : Real.sqrt n * ‖thetaSeq n - theta0‖ ≤ max C 0 :=
    hn.trans (le_max_left _ _)
  calc
    ‖thetaSeq n - theta0‖ = (Real.sqrt n)⁻¹ *
        (Real.sqrt n * ‖thetaSeq n - theta0‖) := by field_simp
    _ ≤ (Real.sqrt n)⁻¹ * max C 0 :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hsqrt.le)

private theorem dqm_sqrtDensity_l2_tendsto_of_tendsto
    {k : ℕ} (M : ParametricFamily Ω (EuclideanSpace ℝ (Fin k)))
    (μ : Measure Ω) (theta0 : EuclideanSpace ℝ (Fin k))
    (ℓ : Ω → EuclideanSpace ℝ (Fin k)) (hPDF : IsPDFOf M μ)
    (hDQM : DifferentiableQuadraticMean M μ theta0 ℓ)
    (thetaSeq : ℕ → EuclideanSpace ℝ (Fin k))
    (htheta : Tendsto thetaSeq atTop (𝓝 theta0)) :
    Tendsto (fun n => ∫ x,
      (M.sqrtDensity (thetaSeq n) x - M.sqrtDensity theta0 x) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  let delta : ℕ → EuclideanSpace ℝ (Fin k) := fun n => thetaSeq n - theta0
  let r : ℕ → Ω → ℝ := fun n x =>
    M.sqrtDensity (theta0 + delta n) x - M.sqrtDensity theta0 x -
      (1 / 2 : ℝ) * ⟪delta n, ℓ x⟫_ℝ * M.sqrtDensity theta0 x
  let s : ℕ → Ω → ℝ := fun n x =>
    (1 / 2 : ℝ) * ⟪delta n, ℓ x⟫_ℝ * M.sqrtDensity theta0 x
  have hdelta : Tendsto delta atTop (𝓝 0) := by
    simpa only [delta, sub_self] using htheta.sub (tendsto_const_nhds (x := theta0))
  have hdelta_sq : Tendsto (fun n => ‖delta n‖ ^ 2) atTop (𝓝 0) := by
    simpa using hdelta.norm.pow 2
  have hr : Tendsto (fun n => ∫ x, (r n x) ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa only [r] using!
      (hDQM.isLittleO.comp_tendsto hdelta).trans_tendsto hdelta_sq
  have hfisher := (dqm_fisher_cont M μ theta0 ℓ
    (hPDF.density_integrable theta0) hDQM
      (fun _ _ => hPDF.density_integrable _)).comp hdelta
  have hs : Tendsto (fun n => ∫ x, (s n x) ^ 2 ∂μ) atTop (𝓝 0) := by
    have hquarter := hfisher.const_mul (1 / 4 : ℝ)
    have heq : (fun n => ∫ x, (s n x) ^ 2 ∂μ) =
        fun n => (1 / 4 : ℝ) *
          ((fun v => ∫ x, ⟪v, ℓ x⟫_ℝ ^ 2 * M.density theta0 x ∂μ) (delta n)) := by
      funext n
      simp only [s]
      rw [show (fun x => (1 / 2 * ⟪delta n, ℓ x⟫_ℝ * M.sqrtDensity theta0 x) ^ 2) =
          fun x => (1 / 4 : ℝ) * (⟪delta n, ℓ x⟫_ℝ ^ 2 * M.density theta0 x) by
        funext x
        rw [← M.sqrtDensity_sq theta0 x]
        ring,
        integral_const_mul]
    rw [heq]
    simpa only [Function.comp_apply, mul_zero] using hquarter
  have hupper : Tendsto (fun n =>
      2 * (∫ x, (r n x) ^ 2 ∂μ) + 2 * ∫ x, (s n x) ^ 2 ∂μ)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (hr.const_mul 2).add (hs.const_mul 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) ?_
  have hr_mem : ∀ᶠ n in atTop, MemLp (r n) 2 μ := by
    simpa only [r] using hdelta.eventually hDQM.mem
  filter_upwards [hr_mem] with n hrn
  have hsn : MemLp (s n) 2 μ := by
    have hscore := dqm_score_memLp_two M μ theta0 ℓ
      (hPDF.density_integrable theta0) hDQM (delta n)
        (fun _ => hPDF.density_integrable _)
    convert hscore.const_mul (1 / 2 : ℝ) using 1
    funext x
    simp only [s]
    ring
  have hdiff : (fun x => M.sqrtDensity (thetaSeq n) x - M.sqrtDensity theta0 x) =
      fun x => r n x + s n x := by
    funext x
    simp only [r, s, delta]
    rw [show theta0 + (thetaSeq n - theta0) = thetaSeq n by abel]
    ring
  simp_rw [congrFun hdiff]
  have hleft : Integrable (fun x => (r n x + s n x) ^ 2) μ := (hrn.add hsn).integrable_sq
  have hright : Integrable (fun x => 2 * (r n x) ^ 2 + 2 * (s n x) ^ 2) μ :=
    (hrn.integrable_sq.const_mul 2).add (hsn.integrable_sq.const_mul 2)
  rw [show 2 * (∫ x, (r n x) ^ 2 ∂μ) + 2 * ∫ x, (s n x) ^ 2 ∂μ =
      ∫ x, 2 * (r n x) ^ 2 + 2 * (s n x) ^ 2 ∂μ by
    rw [integral_add, integral_const_mul, integral_const_mul]
    exacts [hrn.integrable_sq.const_mul 2, hsn.integrable_sq.const_mul 2]]
  exact integral_mono hleft hright fun x => L2Utils.sq_add_le_two_mul_sq (r n x) (s n x)

private theorem populationGram_tupleEfficientScore_eq_information
    {k : ℕ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : OrdinaryScore Q H) (T : NuisanceTangentSpace Q)
    [p : T.HasOrthogonalProjection] (v : Fin k → H) :
    populationGram Q (fun x => tupleEval Q (fun j =>
      @efficientScore Ω _ Q _ H _ _ _ S T p (v j)) x) =
      @efficientInformationMatrix Ω _ Q _ H _ _ _ k S T p v := by
  ext j l
  rw [populationGram, efficientInformationMatrix_apply]
  change (∫ x,
      (((@efficientScore Ω _ Q _ H _ _ _ S T p (v j) : ↥(L2ZeroMean Q)) :
        Lp ℝ 2 Q) x) *
      (((@efficientScore Ω _ Q _ H _ _ _ S T p (v l) : ↥(L2ZeroMean Q)) :
        Lp ℝ 2 Q) x) ∂Q) = _
  change _ = ⟪
    ((@efficientScore Ω _ Q _ H _ _ _ S T p (v j) : ↥(L2ZeroMean Q)) :
      Lp ℝ 2 Q),
    ((@efficientScore Ω _ Q _ H _ _ _ S T p (v l) : ↥(L2ZeroMean Q)) :
      Lp ℝ 2 Q)⟫_ℝ
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => mul_comm _ _

private theorem Vhat_coordinate_measurable
    {k : ℕ}
    (splitSide : ∀ n, Fin n → Bool)
    (scoreHalf : ∀ n, (Fin n → Ω) → Bool → EuclideanSpace ℝ (Fin k) →
      Ω → EuclideanSpace ℝ (Fin k))
    (preliminary : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (hhalf : ∀ n b t,
      Measurable (fun p : (Fin n → Ω) × Ω => scoreHalf n p.1 b t p.2))
    (hpre : ∀ n, Measurable (preliminary n))
    (hgrid : ∀ n, 0 < n → ∀ X, ∃ z : Fin k → ℤ, ∀ j,
      preliminary n X j = (z j : ℝ) / Real.sqrt n) :
    ∀ n j l, Measurable (fun omega : ℕ → Ω =>
      (-empInfo (indexedSplitScore splitSide scoreHalf) n
        (fun i : Fin n => omega i.val)
        (preliminary n (fun i : Fin n => omega i.val))) j l) := by
  intro n j l
  let trunc : (ℕ → Ω) → (Fin n → Ω) := fun omega i => omega i.val
  have htrunc : Measurable trunc :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have hrange : (Set.range (preliminary n)).Countable := by
    by_cases hn : n = 0
    · subst n
      exact (Set.finite_range (preliminary 0)).countable
    · let point : (Fin k → ℤ) → EuclideanSpace ℝ (Fin k) := fun z =>
        (WithLp.equiv 2 (Fin k → ℝ)).symm (fun q => (z q : ℝ) / Real.sqrt n)
      refine (Set.countable_range point).mono ?_
      rintro t ⟨X, rfl⟩
      obtain ⟨z, hz⟩ := hgrid n (Nat.pos_of_ne_zero hn) X
      refine ⟨z, ?_⟩
      ext q
      exact (hz q).symm
  have hfin : Measurable (fun X : Fin n → Ω =>
      empInfo (indexedSplitScore splitSide scoreHalf) n X (preliminary n X) j l) := by
    apply measurable_diag_of_countable_range (preliminary n)
      (fun X t => empInfo (indexedSplitScore splitSide scoreHalf) n X t j l)
      (hpre n) hrange
    intro t
    unfold empInfo indexedSplitScore
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    have hi : Measurable (fun X : Fin n → Ω =>
        scoreHalf n X (splitSide n i) t (X i)) :=
      (hhalf n (splitSide n i) t).comp
        (measurable_id.prodMk (measurable_pi_apply i))
    exact ((PiLp.proj (p := 2) (β := fun _ : Fin k => ℝ) j :
        EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).measurable.comp hi).mul
      ((PiLp.proj (p := 2) (β := fun _ : Fin k => ℝ) l :
        EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).measurable.comp hi)
  simpa only [trunc, Matrix.neg_apply] using! (hfin.comp htrunc).neg

private theorem matrix_nonsing_inv_neg {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) :
    (-A)⁻¹ = -A⁻¹ := by
  classical
  by_cases hA : IsUnit A.det
  · have hneg : IsUnit (-A).det := by
      rw [isUnit_iff_ne_zero, Matrix.det_neg]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (isUnit_iff_ne_zero.mp hA)
    calc
      (-A)⁻¹ = (-A)⁻¹ * 1 := by rw [Matrix.mul_one]
      _ = (-A)⁻¹ * ((-A) * (-A⁻¹)) := by
        congr 1
        rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_nonsing_inv A hA]
        module
      _ = ((-A)⁻¹ * (-A)) * (-A⁻¹) := by rw [Matrix.mul_assoc]
      _ = 1 * (-A⁻¹) := by rw [Matrix.nonsing_inv_mul (-A) hneg]
      _ = -A⁻¹ := by rw [Matrix.one_mul]
  · have hneg : ¬IsUnit (-A).det := by
      intro hn
      apply hA
      rw [isUnit_iff_ne_zero]
      intro hzero
      rw [Matrix.det_neg, hzero, mul_zero] at hn
      exact (isUnit_iff_ne_zero.mp hn) rfl
    rw [Matrix.nonsing_inv_apply_not_isUnit (-A) hneg,
      Matrix.nonsing_inv_apply_not_isUnit A hA, neg_zero]

/-- **25.55 empirical replacement.**  The two literal mean/`L²` clauses of
(25.55), together with opposite-half locality, product-law block independence,
and the root-`n` grid,
replace the indexed estimated-score mean at the random preliminary estimator
by the corresponding fixed-nuisance score mean in `P^n`-probability.  Local
DQM supplies bounded-local contiguity, which transports the moving-law
conditions (25.55) to the true product laws `P^n`.

The proof uses joint score measurability, score centering, `L²` integrability,
and condition (25.55) → conditional first/second moments on each half-sample →
DQM contiguity transport → grid evaluation. -/
theorem oneStep2555_empiricalReplacement_vec
    {M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))} {μ : Measure Ω}
    {scoreLocal : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)}
    {splitSide : ∀ n, Fin n → Bool}
    {scoreHalf : ∀ n, (Fin n → Ω) → Bool → EuclideanSpace ℝ (Fin d) →
      Ω → EuclideanSpace ℝ (Fin d)}
    {preliminary estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    (h : @OneStep2557NativeHyp_vec Ω _ d P _ Θ _ _ _ S_θ T_nuis proj e
      M μ θ₀ scoreLocal splitSide scoreHalf preliminary estimator)
    (hDQM : DifferentiableQuadraticMean M μ θ₀
      (fun x => tupleEval P (fun j =>
        @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j)) x)) :
    TendstoInProbZero (fun n : ℕ => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n •
        (scoreMean (indexedSplitScore splitSide scoreHalf) n X (preliminary n X) -
          (n : ℝ)⁻¹ • ∑ i, scoreLocal (preliminary n X) (X i))) := by
  classical
  let hPDF := OneStep2557NativeHyp_vec.hPDF (proj := proj) h
  let hP := OneStep2557NativeHyp_vec.hP (proj := proj) h
  let hsplit_half_locality :=
    OneStep2557NativeHyp_vec.split_half_locality (proj := proj) h
  let hscoreHalf_joint_meas :=
    OneStep2557NativeHyp_vec.scoreHalf_joint_meas (proj := proj) h
  let hscoreLocal_meas := OneStep2557NativeHyp_vec.scoreLocal_meas (proj := proj) h
  let hscoreLocal_memLp := OneStep2557NativeHyp_vec.scoreLocal_memLp (proj := proj) h
  let hscoreHalf_memLp := OneStep2557NativeHyp_vec.scoreHalf_memLp (proj := proj) h
  let hscoreLocal_centered :=
    OneStep2557NativeHyp_vec.scoreLocal_centered (proj := proj) h
  let hcondition2555_mean :=
    OneStep2557NativeHyp_vec.condition2555_mean (proj := proj) h
  let hcondition2555_l2 :=
    OneStep2557NativeHyp_vec.condition2555_l2 (proj := proj) h
  let hpreliminary_rootN :=
    OneStep2557NativeHyp_vec.preliminary_rootN (proj := proj) h
  let hpreliminary_grid :=
    OneStep2557NativeHyp_vec.preliminary_grid (proj := proj) h
  let ℓ : Ω → EuclideanSpace ℝ (Fin d) := fun x => tupleEval P (fun j =>
    @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j)) x
  have hℓ_meas : Measurable ℓ := by
    apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
    rw [measurable_pi_iff]
    intro j
    exact (Lp.stronglyMeasurable
      ((@efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j) :
        ↥(L2ZeroMean P)) : Lp ℝ 2 P)).measurable
  have hℓ_memLp : MemLp ℓ 2 P := by
    apply MemLp.of_eval_piLp
    intro j
    change MemLp (fun x =>
      (((@efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j) :
        ↥(L2ZeroMean P)) : Lp ℝ 2 P) x)) 2 P
    exact Lp.memLp _
  let R : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) := fun n X t => Real.sqrt n •
    (scoreMean (indexedSplitScore splitSide scoreHalf) n X t -
      (n : ℝ)⁻¹ • ∑ i, scoreLocal t (X i))
  apply rootNGrid_tendstoInProbZero_at_random
    (fun n : ℕ => Measure.pi (fun _ : Fin n => P)) R preliminary θ₀
  · intro thetaSeq htheta
    let Pθ : ℕ → Measure Ω := fun n => modelMeasure M μ (thetaSeq n)
    haveI : ∀ n, IsProbabilityMeasure (Pθ n) := fun n => by
      refine ⟨?_⟩
      dsimp only [Pθ, modelMeasure]
      rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (hPDF.density_integrable (thetaSeq n))
          (Filter.Eventually.of_forall (M.density_nonneg (thetaSeq n))),
        hPDF.density_integral_eq_one (thetaSeq n), ENNReal.ofReal_one]
    let half : ∀ n, (Fin n → Ω) → Bool → Ω → EuclideanSpace ℝ (Fin d) :=
      fun n X b x => scoreHalf n X b (thetaSeq n) x
    let base : ℕ → Ω → EuclideanSpace ℝ (Fin d) :=
      fun n x => scoreLocal (thetaSeq n) x
    have hcont0 := mutuallyContiguous_products_of_dqm_of_rootNBounded
      M μ θ₀ ℓ hPDF hℓ_meas (by simpa only [ℓ] using hDQM) thetaSeq htheta
    have hcont : Contiguity.MutuallyContiguous atTop
        (fun n : ℕ => Measure.pi (fun _ : Fin n => P))
        (fun n : ℕ => Measure.pi (fun _ : Fin n => Pθ n)) := by
      have hP' : (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) = P := by
        simpa only [modelMeasure] using hP.symm
      simpa only [AsymptoticRepresentation.productMeasure, Pθ, modelMeasure, hP'] using hcont0
    have hlocal : ∀ n (X Y : Fin n → Ω) b,
        (∀ i, splitSide n i ≠ b → X i = Y i) → half n X b = half n Y b := by
      intro n X Y b hXY
      simpa only [half] using hsplit_half_locality n X Y b (thetaSeq n) hXY
    have hjoint : ∀ n b,
        Measurable (fun p : (Fin n → Ω) × Ω => half n p.1 b p.2) := by
      intro n b
      simpa only [half] using hscoreHalf_joint_meas n b (thetaSeq n)
    have hbase_meas (n : ℕ) : Measurable (base n) := by
      simpa only [base] using hscoreLocal_meas (thetaSeq n)
    have hbase_memLp : ∀ n, MemLp (base n) 2 (Pθ n) := by
      intro n
      simpa only [base, Pθ] using hscoreLocal_memLp (thetaSeq n)
    have hhalf_memLp : ∀ n X b, MemLp (half n X b) 2 (Pθ n) := by
      intro n X b
      simpa only [half, Pθ] using hscoreHalf_memLp n X b (thetaSeq n)
    have hbase_centered : ∀ n, (∫ x, base n x ∂(Pθ n)) = 0 := by
      intro n
      simpa only [base, Pθ] using hscoreLocal_centered (thetaSeq n)
    have hmean_meas (b : Bool) (n : ℕ) : Measurable (fun X : Fin n → Ω =>
        Real.sqrt n • ∫ x, half n X b x ∂(Pθ n)) := by
      exact (hjoint n b).stronglyMeasurable.integral_prod_right'.measurable.const_smul
        (Real.sqrt n : ℝ)
    have hl2_meas (b : Bool) (n : ℕ) : Measurable (fun X : Fin n → Ω =>
        ∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(Pθ n)) := by
      exact (((hjoint n b).sub ((hbase_meas n).comp measurable_snd)).norm.pow_const 2)
        |>.stronglyMeasurable.integral_prod_right' |>.measurable
    have hmeanQ (b : Bool) :
        TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => Pθ n))
          (fun n X => Real.sqrt n • ∫ x, half n X b x ∂(Pθ n)) := by
      apply TendstoInProbZero.of_contiguous hcont.1 (hmean_meas b)
      simpa only [half, Pθ] using hcondition2555_mean thetaSeq htheta b
    have hl2Q (b : Bool) :
        TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => Pθ n))
          (fun n X => ∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(Pθ n)) := by
      apply TendstoInProbZero.of_contiguous hcont.1 (hl2_meas b)
      simpa only [half, base, Pθ] using hcondition2555_l2 thetaSeq htheta b
    have hsplitQ := splitMean_sub_empMean_tendstoInProbZero Pθ splitSide half base
      hlocal hjoint hbase_memLp hhalf_memLp hbase_centered hmeanQ hl2Q
    have hsplit_meas (n : ℕ) : Measurable (fun X : Fin n → Ω =>
        splitMean splitSide half n X) := by
      unfold splitMean
      exact (Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
        (hjoint n (splitSide n i)).comp
          (measurable_id.prodMk (measurable_pi_apply i))).const_smul ((n : ℝ)⁻¹)
    have hemp_meas (n : ℕ) : Measurable (fun X : Fin n → Ω => empMean base n X) := by
      unfold empMean
      exact (Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
        (hbase_meas n).comp (measurable_pi_apply i)).const_smul ((n : ℝ)⁻¹)
    have hres_meas (n : ℕ) : Measurable (fun X : Fin n → Ω =>
        Real.sqrt n • (splitMean splitSide half n X - empMean base n X)) :=
      ((hsplit_meas n).sub (hemp_meas n)).const_smul (Real.sqrt n : ℝ)
    have hsplitP := TendstoInProbZero.of_contiguous hcont.2 hres_meas hsplitQ
    simpa only [R, half, base, splitMean, empMean, scoreMean, indexedSplitScore]
      using hsplitP
  · exact hpreliminary_rootN
  · exact hpreliminary_grid

/-- **25.55 information consistency.**  The `L²` replacement clause, weighted
score continuity, and the iid law of large numbers identify the empirical Gram
matrix at the preliminary estimator with the efficient information matrix.
Local DQM supplies bounded-local contiguity, which transports the moving-law
conditions (25.55) to the true product laws `P^n`.

The proof uses joint score measurability, moving-score/estimated-score `L²`
integrability, DQM contiguity transport, the second clause of (25.55), (25.56),
and the Gram-matrix LLN. -/
theorem oneStep2555_empInfoConsistency_vec
    {M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))} {μ : Measure Ω}
    {scoreLocal : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)}
    {splitSide : ∀ n, Fin n → Bool}
    {scoreHalf : ∀ n, (Fin n → Ω) → Bool → EuclideanSpace ℝ (Fin d) →
      Ω → EuclideanSpace ℝ (Fin d)}
    {preliminary estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    (h : @OneStep2557NativeHyp_vec Ω _ d P _ Θ _ _ _ S_θ T_nuis proj e
      M μ θ₀ scoreLocal splitSide scoreHalf preliminary estimator)
    (hDQM : DifferentiableQuadraticMean M μ θ₀
      (fun x => tupleEval P (fun j =>
        @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j)) x)) :
    TendstoInProbZero (fun n : ℕ => Measure.pi (fun _ : Fin n => P))
      (fun n X => empInfo (indexedSplitScore splitSide scoreHalf) n X (preliminary n X) -
        @efficientInformationMatrix Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) := by
  classical
  let hPDF := OneStep2557NativeHyp_vec.hPDF (proj := proj) h
  let hP := OneStep2557NativeHyp_vec.hP (proj := proj) h
  let hsplit_half_locality :=
    OneStep2557NativeHyp_vec.split_half_locality (proj := proj) h
  let hscoreHalf_joint_meas :=
    OneStep2557NativeHyp_vec.scoreHalf_joint_meas (proj := proj) h
  let hscoreLocal_meas := OneStep2557NativeHyp_vec.scoreLocal_meas (proj := proj) h
  let hscoreLocal_memLp := OneStep2557NativeHyp_vec.scoreLocal_memLp (proj := proj) h
  let hscoreHalf_memLp := OneStep2557NativeHyp_vec.scoreHalf_memLp (proj := proj) h
  let hcondition2555_l2 :=
    OneStep2557NativeHyp_vec.condition2555_l2 (proj := proj) h
  let hcondition2556 := OneStep2557NativeHyp_vec.condition2556 (proj := proj) h
  let hpreliminary_rootN :=
    OneStep2557NativeHyp_vec.preliminary_rootN (proj := proj) h
  let hpreliminary_grid :=
    OneStep2557NativeHyp_vec.preliminary_grid (proj := proj) h
  let ℓ : Ω → EuclideanSpace ℝ (Fin d) := fun x => tupleEval P (fun j =>
    @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j)) x
  have hℓ_meas : Measurable ℓ := by
    apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
    rw [measurable_pi_iff]
    intro j
    exact (Lp.stronglyMeasurable
      ((@efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j) :
        ↥(L2ZeroMean P)) : Lp ℝ 2 P)).measurable
  have hℓ_memLp : MemLp ℓ 2 P := by
    apply MemLp.of_eval_piLp
    intro j
    change MemLp (fun x =>
      (((@efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j) :
        ↥(L2ZeroMean P)) : Lp ℝ 2 P) x)) 2 P
    exact Lp.memLp _
  have hgram : populationGram P ℓ =
      @efficientInformationMatrix Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e := by
    simpa only [ℓ] using
      (populationGram_tupleEfficientScore_eq_information S_θ T_nuis e)
  let R : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d) →
      Matrix (Fin d) (Fin d) ℝ := fun n X t =>
    empInfo (indexedSplitScore splitSide scoreHalf) n X t -
      @efficientInformationMatrix Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e
  apply rootNGrid_tendstoInProbZero_at_random
    (fun n : ℕ => Measure.pi (fun _ : Fin n => P)) R preliminary θ₀
  · intro thetaSeq htheta
    let Pθ : ℕ → Measure Ω := fun n => modelMeasure M μ (thetaSeq n)
    haveI : ∀ n, IsProbabilityMeasure (Pθ n) := fun n => by
      refine ⟨?_⟩
      dsimp only [Pθ, modelMeasure]
      rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (hPDF.density_integrable (thetaSeq n))
          (Filter.Eventually.of_forall (M.density_nonneg (thetaSeq n))),
        hPDF.density_integral_eq_one (thetaSeq n), ENNReal.ofReal_one]
    let half : ∀ n, (Fin n → Ω) → Bool → Ω → EuclideanSpace ℝ (Fin d) :=
      fun n X b x => scoreHalf n X b (thetaSeq n) x
    let base : ℕ → Ω → EuclideanSpace ℝ (Fin d) :=
      fun n x => scoreLocal (thetaSeq n) x
    let g0 : Ω → EuclideanSpace ℝ (Fin d) := fun x =>
      M.sqrtDensity θ₀ x • ℓ x
    let g : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun n x =>
      M.sqrtDensity (thetaSeq n) x • base n x
    let D : ℕ → ℝ := fun n => ∫ x, ‖g n x - g0 x‖ ^ 2 ∂μ
    have hcont0 := mutuallyContiguous_products_of_dqm_of_rootNBounded
      M μ θ₀ ℓ hPDF hℓ_meas (by simpa only [ℓ] using hDQM) thetaSeq htheta
    have hcont : Contiguity.MutuallyContiguous atTop
        (fun n : ℕ => Measure.pi (fun _ : Fin n => P))
        (fun n : ℕ => Measure.pi (fun _ : Fin n => Pθ n)) := by
      have hP' : (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) = P := by
        simpa only [modelMeasure] using hP.symm
      simpa only [AsymptoticRepresentation.productMeasure, Pθ, modelMeasure, hP'] using hcont0
    have hlocal : ∀ n (X Y : Fin n → Ω) b,
        (∀ i, splitSide n i ≠ b → X i = Y i) → half n X b = half n Y b := by
      intro n X Y b hXY
      simpa only [half] using hsplit_half_locality n X Y b (thetaSeq n) hXY
    have hjoint : ∀ n b,
        Measurable (fun p : (Fin n → Ω) × Ω => half n p.1 b p.2) := by
      intro n b
      simpa only [half] using hscoreHalf_joint_meas n b (thetaSeq n)
    have hbase_meas (n : ℕ) : Measurable (base n) := by
      simpa only [base] using hscoreLocal_meas (thetaSeq n)
    have hbase_memLp : ∀ n, MemLp (base n) 2 (Pθ n) := by
      intro n
      simpa only [base, Pθ] using hscoreLocal_memLp (thetaSeq n)
    have hhalf_memLp : ∀ n X b, MemLp (half n X b) 2 (Pθ n) := by
      intro n X b
      simpa only [half, Pθ] using hscoreHalf_memLp n X b (thetaSeq n)
    have hl2Q (b : Bool) :
        TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => Pθ n))
          (fun n X => ∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(Pθ n)) := by
      have hl2_meas (n : ℕ) : Measurable (fun X : Fin n → Ω =>
          ∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(Pθ n)) := by
        exact (((hjoint n b).sub ((hbase_meas n).comp measurable_snd)).norm.pow_const 2)
          |>.stronglyMeasurable.integral_prod_right' |>.measurable
      apply TendstoInProbZero.of_contiguous hcont.1 hl2_meas
      simpa only [half, base, Pθ] using hcondition2555_l2 thetaSeq htheta b
    have hweighted : Tendsto D atTop (𝓝 0) := by
      simpa only [D, g, g0, base, weightedScore] using hcondition2556 thetaSeq htheta
    have hg0_memLp : MemLp g0 2 μ := by
      have hℓ_model : MemLp ℓ 2
          (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) := by
        simpa only [modelMeasure, hP] using hℓ_memLp
      have hi : Integrable
          (fun x => ‖ℓ x‖ ^ 2 * (ENNReal.ofReal (M.density θ₀ x)).toReal) μ := by
        rw [← integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal (by simp)]
        exact (memLp_two_iff_integrable_sq_norm hℓ_model.aestronglyMeasurable).mp hℓ_model
      refine (memLp_two_iff_integrable_sq_norm
        ((M.sqrtDensity_meas θ₀).fun_smul hℓ_meas).aestronglyMeasurable).mpr ?_
      convert! hi using 1
      funext x
      rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x), ← M.sqrtDensity_sq θ₀ x]
      simp only [norm_smul, Real.norm_eq_abs, mul_pow]
      rw [sq_abs]
      ring
    have hg_memLp (n : ℕ) : MemLp (g n) 2 μ := by
      have hbase_model : MemLp (base n) 2
          (μ.withDensity fun x => ENNReal.ofReal (M.density (thetaSeq n) x)) := by
        simpa only [Pθ, modelMeasure] using hbase_memLp n
      have hi : Integrable (fun x => ‖base n x‖ ^ 2 *
          (ENNReal.ofReal (M.density (thetaSeq n) x)).toReal) μ := by
        rw [← integrable_withDensity_iff
          (M.density_meas (thetaSeq n)).ennreal_ofReal (by simp)]
        exact (memLp_two_iff_integrable_sq_norm hbase_model.aestronglyMeasurable).mp
          hbase_model
      refine (memLp_two_iff_integrable_sq_norm
        ((M.sqrtDensity_meas (thetaSeq n)).fun_smul (hbase_meas n)).aestronglyMeasurable).mpr ?_
      convert! hi using 1
      funext x
      rw [ENNReal.toReal_ofReal (M.density_nonneg (thetaSeq n) x),
        ← M.sqrtDensity_sq (thetaSeq n) x]
      simp only [norm_smul, Real.norm_eq_abs, mul_pow]
      rw [sq_abs]
      ring
    have henergy_eq (n : ℕ) :
        (∫ x, ‖base n x‖ ^ 2 ∂(Pθ n)) = ∫ x, ‖g n x‖ ^ 2 ∂μ := by
      rw [show Pθ n = μ.withDensity
          (fun x => ENNReal.ofReal (M.density (thetaSeq n) x)) by rfl,
        integral_withDensity_eq_integral_toReal_smul
          (M.density_meas (thetaSeq n)).ennreal_ofReal (by simp)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change (ENNReal.ofReal (M.density (thetaSeq n) x)).toReal * ‖base n x‖ ^ 2 = _
        rw [ENNReal.toReal_ofReal (M.density_nonneg (thetaSeq n) x),
          ← M.sqrtDensity_sq (thetaSeq n) x]
        simp only [g, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (M.sqrtDensity_nonneg _ _), mul_pow]
    have hbase_l2_bdd : ∃ C : ℝ, ∀ n, ∫ x, ‖base n x‖ ^ 2 ∂(Pθ n) ≤ C := by
      rcases hweighted.bddAbove_range with ⟨Dmax, hDmax⟩
      let B0 : ℝ := ∫ x, ‖g0 x‖ ^ 2 ∂μ
      refine ⟨2 * Dmax + 2 * B0, fun n => ?_⟩
      rw [henergy_eq]
      have hgn_sq : Integrable (fun x => ‖g n x‖ ^ 2) μ :=
        (memLp_two_iff_integrable_sq_norm (hg_memLp n).aestronglyMeasurable).mp (hg_memLp n)
      have hg0_sq : Integrable (fun x => ‖g0 x‖ ^ 2) μ :=
        (memLp_two_iff_integrable_sq_norm hg0_memLp.aestronglyMeasurable).mp hg0_memLp
      have hdiff_sq : Integrable (fun x => ‖g n x - g0 x‖ ^ 2) μ :=
        (memLp_two_iff_integrable_sq_norm
          ((hg_memLp n).sub hg0_memLp).aestronglyMeasurable).mp
            ((hg_memLp n).sub hg0_memLp)
      calc
        (∫ x, ‖g n x‖ ^ 2 ∂μ) ≤
            ∫ x, 2 * ‖g n x - g0 x‖ ^ 2 + 2 * ‖g0 x‖ ^ 2 ∂μ := by
          apply integral_mono hgn_sq ((hdiff_sq.const_mul 2).add (hg0_sq.const_mul 2))
          intro x
          have hn := norm_add_le (g n x - g0 x) (g0 x)
          rw [sub_add_cancel] at hn
          calc
            ‖g n x‖ ^ 2 ≤ (‖g n x - g0 x‖ + ‖g0 x‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hn 2
            _ ≤ 2 * ‖g n x - g0 x‖ ^ 2 + 2 * ‖g0 x‖ ^ 2 := by
              nlinarith [sq_nonneg (‖g n x - g0 x‖ - ‖g0 x‖)]
        _ = 2 * D n + 2 * B0 := by
          rw [integral_add, integral_const_mul, integral_const_mul]
          exacts [hdiff_sq.const_mul 2, hg0_sq.const_mul 2]
        _ ≤ 2 * Dmax + 2 * B0 := by
          gcongr
          exact hDmax ⟨n, rfl⟩
    have hsplitQ := splitGram_sub_empGram_tendstoInProbZero Pθ splitSide half base
      hlocal hjoint hbase_memLp hhalf_memLp hl2Q hbase_l2_bdd
    have htheta_tendsto := IsRootNBoundedSeq.tendsto htheta
    have hDensityHell := dqm_sqrtDensity_l2_tendsto_of_tendsto
      M μ θ₀ ℓ hPDF (by simpa only [ℓ] using hDQM) thetaSeq htheta_tendsto
    have hempQ := empGram_tendstoInProbZero_of_weightedAnchor μ P Pθ
      (M.density θ₀) (fun n => M.density (thetaSeq n))
      (M.density_meas θ₀) (fun n => M.density_meas (thetaSeq n))
      (M.density_nonneg θ₀) (fun n => M.density_nonneg (thetaSeq n))
      (by simpa only [modelMeasure] using hP)
      (fun n => by rfl) ℓ base hℓ_meas hbase_meas hℓ_memLp hbase_memLp
      (by simpa only [ParametricFamily.sqrtDensity] using hDensityHell)
      (by simpa only [weightedScore, base, ℓ] using! hcondition2556 thetaSeq htheta)
    have hsumQ := TendstoInProbZero.add hsplitQ hempQ
    letI : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) := MeasurableSpace.pi
    haveI : BorelSpace (Matrix (Fin d) (Fin d) ℝ) := Pi.borelSpace
    have hsplit_meas (n : ℕ) : Measurable (fun X : Fin n → Ω =>
        splitGram splitSide half n X) := by
      unfold splitGram
      fun_prop
    have hres_meas (n : ℕ) : Measurable (fun X : Fin n → Ω =>
        splitGram splitSide half n X - populationGram P ℓ) :=
      (hsplit_meas n).sub measurable_const
    have hsumP : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
        (fun n X => splitGram splitSide half n X - populationGram P ℓ) := by
      apply TendstoInProbZero.of_contiguous hcont.2 hres_meas
      convert hsumQ using 1
      funext n X
      abel
    simpa only [R, half, splitGram, empInfo, indexedSplitScore, hgram] using! hsumP
  · exact hpreliminary_rootN
  · exact hpreliminary_grid

/-- **25.56 and DQM imply the deterministic-sequence Ch5 linearization.**
For every deterministic root-`n` sequence, the score map formed on the
infinite iid product satisfies condition (5.47) with derivative `-Ĩ`.
Local contiguity is derived in the proof from DQM; it is not a caller-supplied
conclusion. -/
theorem oneStep2556_deterministicLinearization_vec
    {M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))} {μ : Measure Ω}
    {scoreLocal : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)}
    {splitSide : ∀ n, Fin n → Bool}
    {scoreHalf : ∀ n, (Fin n → Ω) → Bool → EuclideanSpace ℝ (Fin d) →
      Ω → EuclideanSpace ℝ (Fin d)}
    {preliminary estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    (h : @OneStep2557NativeHyp_vec Ω _ d P _ Θ _ _ _ S_θ T_nuis proj e
      M μ θ₀ scoreLocal splitSide scoreHalf preliminary estimator)
    (hDQM : DifferentiableQuadraticMean M μ θ₀
      (fun x => tupleEval P (fun j =>
        @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j)) x)) :
    ∀ thetaSeq : ℕ → EuclideanSpace ℝ (Fin d),
      IsRootNBoundedSeq thetaSeq θ₀ →
      TendstoInProbZero
        (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => P))
        (fun n omega => oneStepResidual
          (fun m w t => scoreMean (indexedSplitScore splitSide scoreHalf)
            m (fun i : Fin m => w i.val) t)
          θ₀ (-@efficientInformationMatrix Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e)
            n omega (thetaSeq n)) := by
  classical
  let hPDF := OneStep2557NativeHyp_vec.hPDF (proj := proj) h
  let hP := OneStep2557NativeHyp_vec.hP (proj := proj) h
  let hsplit_half_locality :=
    OneStep2557NativeHyp_vec.split_half_locality (proj := proj) h
  let hscoreHalf_joint_meas :=
    OneStep2557NativeHyp_vec.scoreHalf_joint_meas (proj := proj) h
  let hscoreLocal_meas := OneStep2557NativeHyp_vec.scoreLocal_meas (proj := proj) h
  let hscoreLocal_memLp := OneStep2557NativeHyp_vec.scoreLocal_memLp (proj := proj) h
  let hscoreHalf_memLp := OneStep2557NativeHyp_vec.scoreHalf_memLp (proj := proj) h
  let hscoreLocal_centered :=
    OneStep2557NativeHyp_vec.scoreLocal_centered (proj := proj) h
  let hcondition2555_mean :=
    OneStep2557NativeHyp_vec.condition2555_mean (proj := proj) h
  let hcondition2555_l2 :=
    OneStep2557NativeHyp_vec.condition2555_l2 (proj := proj) h
  let hcondition2556 := OneStep2557NativeHyp_vec.condition2556 (proj := proj) h
  intro thetaSeq htheta
  let ℓ : Ω → EuclideanSpace ℝ (Fin d) := fun x => tupleEval P (fun j =>
    @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j)) x
  have hℓ_meas : Measurable ℓ := by
    apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
    rw [measurable_pi_iff]
    intro j
    exact (Lp.stronglyMeasurable
      ((@efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j) :
        ↥(L2ZeroMean P)) : Lp ℝ 2 P)).measurable
  let Pθ : ℕ → Measure Ω := fun n => modelMeasure M μ (thetaSeq n)
  haveI : ∀ n, IsProbabilityMeasure (Pθ n) := fun n => by
    refine ⟨?_⟩
    dsimp only [Pθ, modelMeasure]
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hPDF.density_integrable (thetaSeq n))
        (Filter.Eventually.of_forall (M.density_nonneg (thetaSeq n))),
      hPDF.density_integral_eq_one (thetaSeq n), ENNReal.ofReal_one]
  let half : ∀ n, (Fin n → Ω) → Bool → Ω → EuclideanSpace ℝ (Fin d) :=
    fun n X b x => scoreHalf n X b (thetaSeq n) x
  let base : ℕ → Ω → EuclideanSpace ℝ (Fin d) :=
    fun n x => scoreLocal (thetaSeq n) x
  have hcont0 := mutuallyContiguous_products_of_dqm_of_rootNBounded
    M μ θ₀ ℓ hPDF hℓ_meas (by simpa only [ℓ] using hDQM) thetaSeq htheta
  have hcont : Contiguity.MutuallyContiguous atTop
      (fun n : ℕ => Measure.pi (fun _ : Fin n => P))
      (fun n : ℕ => Measure.pi (fun _ : Fin n => Pθ n)) := by
    have hP' : (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) = P := by
      simpa only [modelMeasure] using hP.symm
    simpa only [AsymptoticRepresentation.productMeasure, Pθ, modelMeasure, hP'] using hcont0
  have hlocal : ∀ n (X Y : Fin n → Ω) b,
      (∀ i, splitSide n i ≠ b → X i = Y i) → half n X b = half n Y b := by
    intro n X Y b hXY
    simpa only [half] using hsplit_half_locality n X Y b (thetaSeq n) hXY
  have hjoint : ∀ n b,
      Measurable (fun p : (Fin n → Ω) × Ω => half n p.1 b p.2) := by
    intro n b
    simpa only [half] using hscoreHalf_joint_meas n b (thetaSeq n)
  have hbase_meas (n : ℕ) : Measurable (base n) := by
    simpa only [base] using hscoreLocal_meas (thetaSeq n)
  have hbase_memLp : ∀ n, MemLp (base n) 2 (Pθ n) := by
    intro n
    simpa only [base, Pθ] using hscoreLocal_memLp (thetaSeq n)
  have hhalf_memLp : ∀ n X b, MemLp (half n X b) 2 (Pθ n) := by
    intro n X b
    simpa only [half, Pθ] using hscoreHalf_memLp n X b (thetaSeq n)
  have hbase_centered : ∀ n, (∫ x, base n x ∂(Pθ n)) = 0 := by
    intro n
    simpa only [base, Pθ] using hscoreLocal_centered (thetaSeq n)
  have hmean_meas (b : Bool) (n : ℕ) : Measurable (fun X : Fin n → Ω =>
      Real.sqrt n • ∫ x, half n X b x ∂(Pθ n)) := by
    exact (hjoint n b).stronglyMeasurable.integral_prod_right'.measurable.const_smul
      (Real.sqrt n : ℝ)
  have hl2_meas (b : Bool) (n : ℕ) : Measurable (fun X : Fin n → Ω =>
      ∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(Pθ n)) := by
    exact (((hjoint n b).sub ((hbase_meas n).comp measurable_snd)).norm.pow_const 2)
      |>.stronglyMeasurable.integral_prod_right' |>.measurable
  have hmeanQ (b : Bool) :
      TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => Pθ n))
        (fun n X => Real.sqrt n • ∫ x, half n X b x ∂(Pθ n)) := by
    apply TendstoInProbZero.of_contiguous hcont.1 (hmean_meas b)
    simpa only [half, Pθ] using hcondition2555_mean thetaSeq htheta b
  have hl2Q (b : Bool) :
      TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => Pθ n))
        (fun n X => ∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(Pθ n)) := by
    apply TendstoInProbZero.of_contiguous hcont.1 (hl2_meas b)
    simpa only [half, base, Pθ] using hcondition2555_l2 thetaSeq htheta b
  have hsplitQ := splitMean_sub_empMean_tendstoInProbZero Pθ splitSide half base
    hlocal hjoint hbase_memLp hhalf_memLp hbase_centered hmeanQ hl2Q
  have hsplit_meas (n : ℕ) : Measurable (fun X : Fin n → Ω =>
      splitMean splitSide half n X) := by
    unfold splitMean
    exact (Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
      (hjoint n (splitSide n i)).comp
        (measurable_id.prodMk (measurable_pi_apply i))).const_smul ((n : ℝ)⁻¹)
  have hemp_meas (n : ℕ) : Measurable (fun X : Fin n → Ω => empMean base n X) := by
    unfold empMean
    exact (Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
      (hbase_meas n).comp (measurable_pi_apply i)).const_smul ((n : ℝ)⁻¹)
  have hsplit_res_meas (n : ℕ) : Measurable (fun X : Fin n → Ω =>
      Real.sqrt n • (splitMean splitSide half n X - empMean base n X)) :=
    ((hsplit_meas n).sub (hemp_meas n)).const_smul (Real.sqrt n : ℝ)
  have hsplitP := TendstoInProbZero.of_contiguous hcont.2 hsplit_res_meas hsplitQ
  have hweighted := hcondition2556 thetaSeq htheta
  have hWQ := weightedScore_centeredEmpMean_linearization_of_dqm_rootNBounded
    M μ θ₀ ℓ hPDF hℓ_meas (by simpa only [ℓ] using hDQM) thetaSeq htheta base
      hbase_meas hbase_memLp hbase_centered (by
        simpa only [weightedScore, base, ℓ] using hweighted)
  have hW_meas (n : ℕ) : Measurable (fun X : Fin n → Ω =>
      Real.sqrt n • (empMean base n X - empMean (fun _ => ℓ) n X) +
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (populationGram (modelMeasure M μ θ₀) ℓ)
          (Real.sqrt n • (thetaSeq n - θ₀))) := by
    have hℓ_emp : Measurable (fun X : Fin n → Ω => empMean (fun _ => ℓ) n X) := by
      unfold empMean
      exact (Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
        hℓ_meas.comp (measurable_pi_apply i)).const_smul ((n : ℝ)⁻¹)
    exact (((hemp_meas n).sub hℓ_emp).const_smul (Real.sqrt n : ℝ)).add measurable_const
  have hWP := TendstoInProbZero.of_contiguous hcont.2 hW_meas hWQ
  have hroot0 : IsRootNBoundedSeq (fun _ : ℕ => θ₀) θ₀ := by
    refine ⟨0, Filter.Eventually.of_forall fun n => ?_⟩
    simp
  let half0 : ∀ n, (Fin n → Ω) → Bool → Ω → EuclideanSpace ℝ (Fin d) :=
    fun n X b x => scoreHalf n X b θ₀ x
  let base0 : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun _ x => scoreLocal θ₀ x
  have hlocal0 : ∀ n (X Y : Fin n → Ω) b,
      (∀ i, splitSide n i ≠ b → X i = Y i) → half0 n X b = half0 n Y b := by
    intro n X Y b hXY
    simpa only [half0] using hsplit_half_locality n X Y b θ₀ hXY
  have hjoint0 : ∀ n b,
      Measurable (fun p : (Fin n → Ω) × Ω => half0 n p.1 b p.2) := by
    intro n b
    simpa only [half0] using hscoreHalf_joint_meas n b θ₀
  have hbase0_memLp : ∀ n, MemLp (base0 n) 2 P := by
    intro n
    simpa only [base0, ← hP] using hscoreLocal_memLp θ₀
  have hhalf0_memLp : ∀ n X b, MemLp (half0 n X b) 2 P := by
    intro n X b
    simpa only [half0, ← hP] using hscoreHalf_memLp n X b θ₀
  have hbase0_centered : ∀ n, (∫ x, base0 n x ∂P) = 0 := by
    intro n
    simpa only [base0, ← hP] using hscoreLocal_centered θ₀
  have hmean0 (b : Bool) : TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n • ∫ x, half0 n X b x ∂P) := by
    simpa only [half0, ← hP] using hcondition2555_mean (fun _ => θ₀) hroot0 b
  have hl20 (b : Bool) : TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => ∫ x, ‖half0 n X b x - base0 n x‖ ^ 2 ∂P) := by
    simpa only [half0, base0, ← hP] using
      hcondition2555_l2 (fun _ => θ₀) hroot0 b
  have hsplit0 := splitMean_sub_empMean_tendstoInProbZero (fun _ : ℕ => P)
    splitSide half0 base0 hlocal0 hjoint0 hbase0_memLp hhalf0_memLp
      hbase0_centered hmean0 hl20
  have hW0 := weightedScore_centeredEmpMean_linearization_of_dqm_rootNBounded
    M μ θ₀ ℓ hPDF hℓ_meas (by simpa only [ℓ] using hDQM)
      (fun _ : ℕ => θ₀) hroot0 base0
      (fun _ => by simpa only [base0] using hscoreLocal_meas θ₀)
      (fun _ => by simpa only [base0] using hscoreLocal_memLp θ₀)
      (fun _ => by simpa only [base0] using hscoreLocal_centered θ₀) (by
        simpa only [weightedScore, base0, ℓ] using
          hcondition2556 (fun _ : ℕ => θ₀) hroot0)
  have hW0P : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n •
        (empMean base0 n X - empMean (fun _ => ℓ) n X)) := by
    simpa only [← hP, sub_self, smul_zero, map_zero, add_zero] using hW0
  have hsum := TendstoInProbZero.add
    (TendstoInProbZero.add
      (TendstoInProbZero.add hsplitP hWP) (TendstoInProbZero.neg hsplit0))
    (TendstoInProbZero.neg hW0P)
  let Zfin : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d) := fun n X =>
    Real.sqrt n •
        (scoreMean (indexedSplitScore splitSide scoreHalf) n X (thetaSeq n) -
          scoreMean (indexedSplitScore splitSide scoreHalf) n X θ₀) +
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
        (@efficientInformationMatrix Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e)
        (Real.sqrt n • (thetaSeq n - θ₀))
  have hZfin : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P)) Zfin := by
    convert hsum using 1
    funext n X
    simp only [Zfin, scoreMean, indexedSplitScore, splitMean, empMean,
      half, base, half0, base0]
    rw [show populationGram (modelMeasure M μ θ₀) ℓ =
        @efficientInformationMatrix Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e by
      rw [← hP]
      simpa only [ℓ] using
        (populationGram_tupleEfficientScore_eq_information S_θ T_nuis e)]
    module
  have hZfin_meas (n : ℕ) : Measurable (Zfin n) := by
    have hmoving : Measurable (fun X : Fin n → Ω =>
        splitMean splitSide half n X) := by
      unfold splitMean
      exact (Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
        (hjoint n (splitSide n i)).comp
          (measurable_id.prodMk (measurable_pi_apply i))).const_smul ((n : ℝ)⁻¹)
    have hfixed : Measurable (fun X : Fin n → Ω =>
        splitMean splitSide half0 n X) := by
      unfold splitMean
      exact (Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
        (hjoint0 n (splitSide n i)).comp
          (measurable_id.prodMk (measurable_pi_apply i))).const_smul ((n : ℝ)⁻¹)
    simpa only [Zfin, scoreMean, indexedSplitScore, splitMean, half, half0] using!
      ((hmoving.sub hfixed).const_smul (Real.sqrt n : ℝ)).add measurable_const
  intro ε hε
  have hfin := hZfin ε hε
  apply hfin.congr'
  exact Filter.Eventually.of_forall fun n => by
    have hset : MeasurableSet {X : Fin n → Ω | ε ≤ ‖Zfin n X‖} :=
      measurableSet_le measurable_const (hZfin_meas n).norm
    have hbridge := pi_real_eq_infinitePi_real_of_truncate P n hset
    simpa only [Zfin, oneStepResidual, scoreMean, indexedSplitScore,
      map_neg, ContinuousLinearMap.neg_apply, sub_neg_eq_add] using! hbridge

/-- **Native vector vdV 25.57 asymptotic linearity.**  The Ch5 discretized
one-step expansion is first applied on `ℕ → Ω` under `infinitePi`; the
`IIdJointLaw` truncation identities then transport its residual back to the
finite product measures in `AsymptoticallyLinearAt_vec`.

This theorem consumes the literal one-step formula and the three named
25.55/25.56 consequences above.  It does not route through a generic
Z-estimator score-equation bundle. -/
theorem oneStep_asymptoticallyLinear_2557_native_vec
    {M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))} {μ : Measure Ω}
    {scoreLocal : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)}
    {splitSide : ∀ n, Fin n → Bool}
    {scoreHalf : ∀ n, (Fin n → Ω) → Bool → EuclideanSpace ℝ (Fin d) →
      Ω → EuclideanSpace ℝ (Fin d)}
    {preliminary estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    (h : @OneStep2557NativeHyp_vec Ω _ d P _ Θ _ _ _ S_θ T_nuis proj e
      M μ θ₀ scoreLocal splitSide scoreHalf preliminary estimator)
    (hDQM : DifferentiableQuadraticMean M μ θ₀
      (fun x => tupleEval P (fun j =>
        @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j)) x)) :
    AsymptoticallyLinearAt_vec estimator P
      (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) θ₀ := by
  classical
  let hPDF := OneStep2557NativeHyp_vec.hPDF (proj := proj) h
  let hP := OneStep2557NativeHyp_vec.hP (proj := proj) h
  let hPD := OneStep2557NativeHyp_vec.hPD (proj := proj) h
  let hpre_root := OneStep2557NativeHyp_vec.preliminary_rootN (proj := proj) h
  let hpre_grid := OneStep2557NativeHyp_vec.preliminary_grid (proj := proj) h
  let hpre_meas := OneStep2557NativeHyp_vec.preliminary_meas (proj := proj) h
  let hhalf_meas := OneStep2557NativeHyp_vec.scoreHalf_joint_meas (proj := proj) h
  let hest := OneStep2557NativeHyp_vec.estimator_def (proj := proj) h
  let ℓ : Ω → EuclideanSpace ℝ (Fin d) := fun x => tupleEval P (fun j =>
    @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j)) x
  let I : Matrix (Fin d) (Fin d) ℝ :=
    @efficientInformationMatrix Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e
  let μinf : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P)
  let trunc : ∀ n, (ℕ → Ω) → (Fin n → Ω) := fun n omega i => omega i.val
  let Ψ : ℕ → (ℕ → Ω) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun n omega t => scoreMean (indexedSplitScore splitSide scoreHalf) n (trunc n omega) t
  let pre : ℕ → (ℕ → Ω) → EuclideanSpace ℝ (Fin d) :=
    fun n omega => preliminary n (trunc n omega)
  let Vhat : ℕ → (ℕ → Ω) → Matrix (Fin d) (Fin d) ℝ := fun n omega =>
    -empInfo (indexedSplitScore splitSide scoreHalf) n (trunc n omega) (pre n omega)
  let V0 : Matrix (Fin d) (Fin d) ℝ := -I
  haveI : IsProbabilityMeasure μinf := by simp only [μinf]; infer_instance
  have hℓ_meas : Measurable ℓ := by
    apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
    rw [measurable_pi_iff]
    intro j
    exact (Lp.stronglyMeasurable
      ((@efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j) :
        ↥(L2ZeroMean P)) : Lp ℝ 2 P)).measurable
  have hℓ_memLp_native : MemLp ℓ 2 P := by
    apply MemLp.of_eval_piLp
    intro j
    change MemLp (fun x =>
      (((@efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j) :
        ↥(L2ZeroMean P)) : Lp ℝ 2 P) x)) 2 P
    exact Lp.memLp _
  have hJ : ∀ u v : EuclideanSpace ℝ (Fin d),
      fisherInformation M μ θ₀ ℓ u v =
        ⟪u, (WithLp.equiv 2 _).symm (I.mulVec ((WithLp.equiv 2 _) v))⟫_ℝ := by
    intro u v
    have hmeasure : modelMeasure M μ θ₀ = P := hP.symm
    have hgram := populationGram_tupleEfficientScore_eq_information S_θ T_nuis e
    have hcoord (j : Fin d) : MemLp (fun x => (ℓ x).ofLp j) 2 P := by
      change MemLp (fun x =>
        (((@efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j) :
          ↥(L2ZeroMean P)) : Lp ℝ 2 P) x)) 2 P
      exact Lp.memLp _
    rw [fisherInformation]
    have hdens : (∫ x, (⟪u, ℓ x⟫_ℝ * ⟪v, ℓ x⟫_ℝ) * M.density θ₀ x ∂μ) =
        ∫ x, ⟪u, ℓ x⟫_ℝ * ⟪v, ℓ x⟫_ℝ ∂(modelMeasure M μ θ₀) := by
      rw [modelMeasure, integral_withDensity_eq_integral_toReal_smul
        (M.density_meas θ₀).ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x), smul_eq_mul]
        ring
    rw [hdens, hmeasure]
    change ∫ x, ⟪u, ℓ x⟫_ℝ * ⟪v, ℓ x⟫_ℝ ∂P = _
    simp only [PiLp.inner_apply, WithLp.equiv_apply, WithLp.equiv_symm_apply]
    change _ = ∑ i, (I.mulVec v.ofLp) i * u.ofLp i
    rw [show (∑ i, (I.mulVec v.ofLp) i * u.ofLp i) =
        dotProduct u.ofLp (I.mulVec v.ofLp) by
      simp only [dotProduct]; apply Finset.sum_congr rfl; intro i _; ring]
    rw [← show populationGram P ℓ = I by simpa only [ℓ, I] using hgram]
    simp only [populationGram, dotProduct, Matrix.mulVec]
    calc
      (∫ x, (∑ i, ⟪u.ofLp i, (ℓ x).ofLp i⟫_ℝ) *
          ∑ j, ⟪v.ofLp j, (ℓ x).ofLp j⟫_ℝ ∂P) =
          ∫ x, ∑ i, ∑ j,
            (u.ofLp i * v.ofLp j) * ((ℓ x).ofLp i * (ℓ x).ofLp j) ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change (∑ i, ⟪u.ofLp i, (ℓ x).ofLp i⟫_ℝ) *
              ∑ j, ⟪v.ofLp j, (ℓ x).ofLp j⟫_ℝ =
            ∑ i, ∑ j, (u.ofLp i * v.ofLp j) *
              ((ℓ x).ofLp i * (ℓ x).ofLp j)
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          have hr (a b : ℝ) : ⟪a, b⟫_ℝ = b * a := by
            exact RCLike.inner_apply a b
          rw [hr, hr]
          ring
      _ = ∑ i, ∑ j, (u.ofLp i * v.ofLp j) *
          ∫ x, (ℓ x).ofLp i * (ℓ x).ofLp j ∂P := by
        rw [integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro i _
          rw [integral_finset_sum]
          · apply Finset.sum_congr rfl
            intro j _
            rw [integral_const_mul]
          · intro j _
            exact ((hcoord i).integrable_mul (hcoord j)).const_mul _
        · intro i _
          exact integrable_finset_sum _ fun j _ =>
            ((hcoord i).integrable_mul (hcoord j)).const_mul _
      _ = ∑ i, u.ofLp i * ∑ j,
          (∫ x, (ℓ x).ofLp i * (ℓ x).ofLp j ∂P) * v.ofLp j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  let ν : Measure (EuclideanSpace ℝ (Fin d)) :=
    ProbabilityTheory.multivariateGaussian 0 I
  haveI : IsProbabilityMeasure ν := by
    simp only [ν]
    infer_instance
  have hscoreWeak := AsymptoticRepresentation.scoreSum_weakly_converges
    M μ θ₀ ℓ hℓ_meas (hPDF.density_integral_eq_one θ₀)
      (hPDF.density_integrable θ₀)
      (fun t u => hPDF.density_integral_eq_one (θ₀ + t • u))
      (fun t u => hPDF.density_integrable (θ₀ + t • u))
      (by simpa only [ℓ] using hDQM) I (by simpa only [I] using hPD.posSemidef) hJ
  have hweakLeading : WeakConverges
      (fun n => μinf.map (fun omega =>
        Real.sqrt n • empMean (fun _ => ℓ) n (trunc n omega))) ν := by
    have hpush : ∀ n,
        (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (AsymptoticRepresentation.scoreSum ℓ n) =
        μinf.map (fun omega => Real.sqrt n • empMean (fun _ => ℓ) n (trunc n omega)) := by
      intro n
      rw [AsymptoticRepresentation.scoreSum_pushforward_eq M μ θ₀
        (hPDF.density_integral_eq_one θ₀) (hPDF.density_integrable θ₀) ℓ hℓ_meas n]
      change Measure.map _ (Measure.infinitePi (fun _ : ℕ => modelMeasure M μ θ₀)) = _
      rw [← hP]
      simp only [μinf]
      apply Measure.map_congr
      filter_upwards with omega
      simp only [empMean, trunc, smul_smul]
      rw [show (∑ x : Fin n, ℓ (omega x.val)) =
          ∑ i ∈ Finset.range n, ℓ (omega i) by
        exact Fin.sum_univ_eq_sum_range (fun i => ℓ (omega i)) n]
      by_cases hn : n = 0
      · subst n
        simp
      · have hs : Real.sqrt n ≠ 0 :=
          (Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).ne'
        have hnreal : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
        have hc : (Real.sqrt n)⁻¹ = Real.sqrt n * (n : ℝ)⁻¹ := by
          calc
            (Real.sqrt n)⁻¹ = Real.sqrt n / Real.sqrt n ^ 2 := by field_simp
            _ = Real.sqrt n / (n : ℝ) := by rw [← hnreal]
            _ = Real.sqrt n * (n : ℝ)⁻¹ := div_eq_mul_inv _ _
        rw [hc]
    intro f
    simpa only [ν, hpush] using hscoreWeak f
  have hreplaceFin : TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n •
        (scoreMean (indexedSplitScore splitSide scoreHalf) n X θ₀ -
          empMean (fun _ => ℓ) n X)) := by
    let half0 : ∀ n, (Fin n → Ω) → Bool → Ω → EuclideanSpace ℝ (Fin d) :=
      fun n X b x => scoreHalf n X b θ₀ x
    let base0 : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun _ x => scoreLocal θ₀ x
    have hroot0 : IsRootNBoundedSeq (fun _ : ℕ => θ₀) θ₀ := by
      refine ⟨0, Filter.Eventually.of_forall fun n => ?_⟩
      simp
    have hlocal0 : ∀ n (X Y : Fin n → Ω) b,
        (∀ i, splitSide n i ≠ b → X i = Y i) → half0 n X b = half0 n Y b := by
      intro n X Y b hXY
      simpa only [half0] using
        OneStep2557NativeHyp_vec.split_half_locality (proj := proj) h n X Y b θ₀ hXY
    have hjoint0 : ∀ n b,
        Measurable (fun p : (Fin n → Ω) × Ω => half0 n p.1 b p.2) := by
      intro n b
      simpa only [half0] using hhalf_meas n b θ₀
    have hbase0_mem : ∀ n, MemLp (base0 n) 2 P := by
      intro n
      simpa only [base0, ← hP] using
        OneStep2557NativeHyp_vec.scoreLocal_memLp (proj := proj) h θ₀
    have hhalf0_mem : ∀ n X b, MemLp (half0 n X b) 2 P := by
      intro n X b
      simpa only [half0, ← hP] using
        OneStep2557NativeHyp_vec.scoreHalf_memLp (proj := proj) h n X b θ₀
    have hbase0_ctr : ∀ n, (∫ x, base0 n x ∂P) = 0 := by
      intro n
      simpa only [base0, ← hP] using
        OneStep2557NativeHyp_vec.scoreLocal_centered (proj := proj) h θ₀
    have hmean0 (b : Bool) :=
      OneStep2557NativeHyp_vec.condition2555_mean (proj := proj) h
        (fun _ : ℕ => θ₀) hroot0 b
    have hl20 (b : Bool) :=
      OneStep2557NativeHyp_vec.condition2555_l2 (proj := proj) h
        (fun _ : ℕ => θ₀) hroot0 b
    have hs := splitMean_sub_empMean_tendstoInProbZero (fun _ : ℕ => P)
      splitSide half0 base0 hlocal0 hjoint0 hbase0_mem hhalf0_mem hbase0_ctr
      (by intro b; simpa only [half0, ← hP] using hmean0 b)
      (by intro b; simpa only [half0, base0, ← hP] using hl20 b)
    have hW := weightedScore_centeredEmpMean_linearization_of_dqm_rootNBounded
      M μ θ₀ ℓ hPDF hℓ_meas (by simpa only [ℓ] using hDQM)
        (fun _ : ℕ => θ₀) hroot0 base0
        (fun _ => by simpa only [base0] using
          OneStep2557NativeHyp_vec.scoreLocal_meas (proj := proj) h θ₀)
        (fun _ => by simpa only [base0] using
          OneStep2557NativeHyp_vec.scoreLocal_memLp (proj := proj) h θ₀)
        (fun _ => by simpa only [base0] using
          OneStep2557NativeHyp_vec.scoreLocal_centered (proj := proj) h θ₀)
        (by
          have hc := OneStep2557NativeHyp_vec.condition2556 (proj := proj) h
            (fun _ : ℕ => θ₀) hroot0
          simpa only [weightedScore, base0, ℓ] using hc)
    have hWP : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
        (fun n X => Real.sqrt n • (empMean base0 n X - empMean (fun _ => ℓ) n X)) := by
      simpa only [← hP, sub_self, smul_zero, map_zero, add_zero] using hW
    have hadd := TendstoInProbZero.add hs hWP
    convert hadd using 1
    funext n X
    simp only [scoreMean, indexedSplitScore, splitMean, empMean, half0, base0]
    module
  have hreplaceInf : TendstoInProbZero (fun _ : ℕ => μinf)
      (fun n omega => Real.sqrt n • (Ψ n omega θ₀ - empMean (fun _ => ℓ) n (trunc n omega))) := by
    intro ε hε
    have hfin := hreplaceFin ε hε
    apply hfin.congr'
    exact Filter.Eventually.of_forall fun n => by
      have hfin_meas : Measurable (fun X : Fin n → Ω => Real.sqrt n •
          (scoreMean (indexedSplitScore splitSide scoreHalf) n X θ₀ -
            empMean (fun _ => ℓ) n X)) := by
        unfold scoreMean indexedSplitScore empMean
        have hscore (i : Fin n) : Measurable (fun X : Fin n → Ω =>
            scoreHalf n X (splitSide n i) θ₀ (X i)) :=
          (hhalf_meas n (splitSide n i) θ₀).comp
            (measurable_id.prodMk (measurable_pi_apply i))
        simpa only [Function.comp_apply, smul_smul] using!
          (((Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
          hscore i).const_smul ((n : ℝ)⁻¹)).sub
          ((Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
            hℓ_meas.comp (measurable_pi_apply i)).const_smul ((n : ℝ)⁻¹))).const_smul
              (Real.sqrt n : ℝ)
      have hset : MeasurableSet {X : Fin n → Ω | ε ≤ ‖Real.sqrt n •
          (scoreMean (indexedSplitScore splitSide scoreHalf) n X θ₀ -
            empMean (fun _ => ℓ) n X)‖} :=
        measurableSet_le measurable_const hfin_meas.norm
      simpa only [Ψ, trunc, μinf] using! pi_real_eq_infinitePi_real_of_truncate P n hset
  have hΨ0_meas (n : ℕ) : Measurable (fun omega => Real.sqrt n • Ψ n omega θ₀) := by
    have htrunc : Measurable (trunc n) := by
      exact measurable_pi_lambda _ fun i => measurable_pi_apply i.val
    have hfin : Measurable (fun X : Fin n → Ω =>
        Real.sqrt n • scoreMean (indexedSplitScore splitSide scoreHalf) n X θ₀) := by
      unfold scoreMean indexedSplitScore
      fun_prop
    simpa only [Ψ] using! hfin.comp htrunc
  have hleading_meas (n : ℕ) : Measurable
      (fun omega => Real.sqrt n • empMean (fun _ => ℓ) n (trunc n omega)) := by
    have htrunc : Measurable (trunc n) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply i.val
    have hfin : Measurable (fun X : Fin n → Ω =>
        Real.sqrt n • empMean (fun _ => ℓ) n X) := by
      unfold empMean
      simpa only [Function.comp_apply, smul_smul] using!
        (Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
          hℓ_meas.comp (measurable_pi_apply i)).const_smul
            (Real.sqrt n * (n : ℝ)⁻¹)
    exact hfin.comp htrunc
  have hweak : WeakConverges
      (fun n => μinf.map (fun omega => Real.sqrt n • Ψ n omega θ₀)) ν := by
    apply WeakConverges.slutsky_of_tendstoInMeasure_dist
      (fun n => (hleading_meas n).aemeasurable)
      (fun n => (hΨ0_meas n).aemeasurable) hweakLeading
    · intro ε hε
      have hneg := TendstoInProbZero.neg hreplaceInf
      have hdiff : TendstoInProbZero (fun _ : ℕ => μinf)
          (fun n omega => Real.sqrt n • empMean (fun _ => ℓ) n (trunc n omega) -
            Real.sqrt n • Ψ n omega θ₀) := by
        convert hneg using 1
        funext n omega
        module
      simpa only [dist_eq_norm] using hdiff ε hε
  have hV0 : V0.det ≠ 0 := by
    simp only [V0, I, Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt hPD.det_pos)
  letI : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) := MeasurableSpace.pi
  haveI : BorelSpace (Matrix (Fin d) (Fin d) ℝ) := Pi.borelSpace
  have hVhat_meas : ∀ n i j, Measurable (fun omega => Vhat n omega i j) := by
    intro n i j
    simpa only [Vhat, pre, trunc] using
      Vhat_coordinate_measurable splitSide scoreHalf preliminary hhalf_meas
        hpre_meas hpre_grid n i j
  have hVhat : TendstoInProbZero (fun _ : ℕ => μinf)
      (fun n omega => Vhat n omega - V0) := by
    have hfin := oneStep2555_empInfoConsistency_vec h hDQM
    intro ε hε
    have hconv := hfin ε hε
    apply hconv.congr'
    exact Filter.Eventually.of_forall fun n => by
      have hstat_meas : Measurable (fun X : Fin n → Ω =>
          empInfo (indexedSplitScore splitSide scoreHalf) n X (preliminary n X) - I) := by
        apply measurable_pi_lambda _
        intro i
        apply measurable_pi_lambda _
        intro j
        have hrange : (Set.range (preliminary n)).Countable := by
          by_cases hn : n = 0
          · subst n
            exact (Set.finite_range (preliminary 0)).countable
          · let point : (Fin d → ℤ) → EuclideanSpace ℝ (Fin d) := fun z =>
              (WithLp.equiv 2 (Fin d → ℝ)).symm
                (fun q => (z q : ℝ) / Real.sqrt n)
            refine (Set.countable_range point).mono ?_
            rintro t ⟨X, rfl⟩
            obtain ⟨z, hz⟩ := hpre_grid n (Nat.pos_of_ne_zero hn) X
            refine ⟨z, ?_⟩
            ext q
            exact (hz q).symm
        have hcoord : Measurable (fun X : Fin n → Ω =>
            empInfo (indexedSplitScore splitSide scoreHalf) n X (preliminary n X) i j) := by
          apply measurable_diag_of_countable_range (preliminary n)
            (fun X t => empInfo (indexedSplitScore splitSide scoreHalf) n X t i j)
            (hpre_meas n) hrange
          intro t
          unfold empInfo indexedSplitScore
          apply measurable_const.mul
          apply Finset.measurable_sum
          intro q _
          have hq : Measurable (fun X : Fin n → Ω =>
              scoreHalf n X (splitSide n q) t (X q)) :=
            (hhalf_meas n (splitSide n q) t).comp
              (measurable_id.prodMk (measurable_pi_apply q))
          exact ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) i :
              EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp hq).mul
            ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
              EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp hq)
        simpa only [Matrix.sub_apply] using! hcoord.sub measurable_const
      have hset : MeasurableSet {X : Fin n → Ω | ε ≤
          ‖empInfo (indexedSplitScore splitSide scoreHalf) n X (preliminary n X) - I‖} :=
        measurableSet_le measurable_const hstat_meas.norm
      have hbridge := pi_real_eq_infinitePi_real_of_truncate P n hset
      calc
        (Measure.pi (fun _ : Fin n => P)).real
            {X | ε ≤ ‖empInfo (indexedSplitScore splitSide scoreHalf) n X
              (preliminary n X) - I‖} =
            μinf.real {omega | ε ≤ ‖empInfo (indexedSplitScore splitSide scoreHalf) n
              (trunc n omega) (pre n omega) - I‖} := by
                simpa only [trunc, pre, μinf] using! hbridge
        _ = μinf.real {omega | ε ≤ ‖Vhat n omega - V0‖} := by
          congr 1
          ext omega
          simp only [Set.mem_setOf_eq, Vhat, V0]
          rw [show -empInfo (indexedSplitScore splitSide scoreHalf) n (trunc n omega)
              (pre n omega) - -I = -(empInfo (indexedSplitScore splitSide scoreHalf) n
                (trunc n omega) (pre n omega) - I) by module, norm_neg]
  have hpre : IsBoundedInProb (fun _ : ℕ => μinf)
      (fun n omega => Real.sqrt n • (pre n omega - θ₀)) := by
    intro ε hε
    obtain ⟨M0, hM0⟩ := hpre_root ε hε
    refine ⟨M0, fun n => ?_⟩
    have hstat_meas : Measurable (fun X : Fin n → Ω =>
        Real.sqrt n • (preliminary n X - θ₀)) :=
      ((hpre_meas n).sub measurable_const).const_smul (Real.sqrt n : ℝ)
    have hset : MeasurableSet {X : Fin n → Ω |
        M0 < ‖Real.sqrt n • (preliminary n X - θ₀)‖} :=
      measurableSet_lt measurable_const hstat_meas.norm
    have hbridge := pi_real_eq_infinitePi_real_of_truncate P n hset
    rw [← show (Measure.pi (fun _ : Fin n => P)).real
        {X | M0 < ‖Real.sqrt n • (preliminary n X - θ₀)‖} =
        μinf.real {omega | M0 < ‖Real.sqrt n • (pre n omega - θ₀)‖} by
      simpa only [pre, trunc, μinf] using! hbridge]
    exact hM0 n
  have h47 : ∀ thetaSeq : ℕ → EuclideanSpace ℝ (Fin d),
      IsRootNBoundedSeq thetaSeq θ₀ → TendstoInProbZero (fun _ : ℕ => μinf)
        (fun n omega => oneStepResidual Ψ θ₀ V0 n omega (thetaSeq n)) := by
    intro thetaSeq htheta
    simpa only [Ψ, V0, trunc, I] using
      (oneStep2556_deterministicLinearization_vec h hDQM thetaSeq htheta)
  have hgrid : ∀ n, 0 < n → ∀ omega, ∃ z : Fin d → ℤ, ∀ j,
      pre n omega j = (z j : ℝ) / Real.sqrt n := by
    intro n hn omega
    simpa only [pre, trunc] using hpre_grid n hn (trunc n omega)
  have hexp := discretizedOneStepEstimator_linearExpansion μinf Ψ pre Vhat θ₀ V0 ν
    hweak hV0 hVhat hpre h47 hgrid hΨ0_meas hVhat_meas
  let Linv := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) I⁻¹
  have hupdate (n : ℕ) (omega : ℕ → Ω) :
      oneStepUpdate Ψ pre Vhat n omega = estimator n (trunc n omega) := by
    apply WithLp.ofLp_injective 2
    simp only [oneStepUpdate, Ψ, pre, Vhat, trunc]
    rw [matrix_nonsing_inv_neg]
    rw [hest]
    rw [show scoreMean (indexedSplitScore splitSide scoreHalf) n (trunc n omega)
          (preliminary n (trunc n omega)) =
        WithLp.toLp 2 (scoreMean (indexedSplitScore splitSide scoreHalf) n
          (trunc n omega) (preliminary n (trunc n omega))).ofLp by
      exact (WithLp.toLp_ofLp 2 _).symm]
    rw [Matrix.toEuclideanCLM_toLp]
    simp only [Matrix.neg_mulVec, Matrix.mulVecLin_apply]
    funext j
    simp only [PiLp.sub_apply, Pi.neg_apply, Pi.add_apply, sub_neg_eq_add]
  have hmapped := tendstoInProbZero_clm μinf Linv hreplaceInf
  have hmid : TendstoInProbZero (fun _ : ℕ => μinf)
      (fun n omega => Real.sqrt n • (estimator n (trunc n omega) - θ₀) -
        Linv (Real.sqrt n • empMean (fun _ => ℓ) n (trunc n omega))) := by
    have hadd := TendstoInProbZero.add hexp hmapped
    convert hadd using 1
    funext n omega
    rw [hupdate]
    simp only [V0, Linv, map_sub, map_smul]
    rw [matrix_nonsing_inv_neg I]
    simp only [map_neg, ContinuousLinearMap.neg_apply]
    module
  have hnativeInf : TendstoInProbZero (fun _ : ℕ => μinf)
      (fun n omega => Real.sqrt n • (estimator n (trunc n omega) - θ₀) -
        (Real.sqrt n)⁻¹ • ∑ i, tupleEval P
          (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) ((trunc n omega) i)) := by
    have h5 := @native_influence_eq_candidateVecEIF Ω _ d P _ Θ _ _ _
      S_θ T_nuis proj e
    have hinfluence (n : ℕ) :
        (fun omega => Linv (Real.sqrt n • empMean (fun _ => ℓ) n (trunc n omega))) =ᵐ[μinf]
        (fun omega => (Real.sqrt n)⁻¹ • ∑ i, tupleEval P
          (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) ((trunc n omega) i)) := by
      have hall : ∀ᵐ omega ∂μinf, ∀ i : Fin n,
          Linv (ℓ ((trunc n omega) i)) = tupleEval P
            (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e)
              ((trunc n omega) i) := by
        rw [ae_all_iff]
        intro i
        exact (measurePreserving_eval_infinitePi (μ := fun _ : ℕ => P) i.val)
          |>.quasiMeasurePreserving.ae h5
      filter_upwards [hall] with omega homega
      by_cases hn : n = 0
      · subst n
        simp
      · have hs : Real.sqrt n ≠ 0 :=
          (Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).ne'
        have hnreal : (n : ℝ) = Real.sqrt n ^ 2 :=
          (Real.sq_sqrt (Nat.cast_nonneg n)).symm
        have hc : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
          rw [show (n : ℝ)⁻¹ = (Real.sqrt n ^ 2)⁻¹ by rw [← hnreal]]
          field_simp
        simp only [empMean, map_smul, map_sum, trunc, homega, smul_smul, hc]
    intro ε hε
    have hconv := hmid ε hε
    apply hconv.congr'
    exact Filter.Eventually.of_forall fun n => by
      apply congrArg ENNReal.toReal
      apply MeasureTheory.measure_congr
      filter_upwards [hinfluence n] with omega homega
      exact congrArg
        (fun z => ε ≤ ‖Real.sqrt n • (estimator n (trunc n omega) - θ₀) - z‖) homega
  intro ε hε
  rw [← ENNReal.tendsto_toReal_zero_iff]
  have hinf := hnativeInf ε hε
  apply Tendsto.congr' ?_ hinf
  exact Filter.Eventually.of_forall fun n => by
    have hres_meas : Measurable (fun X : Fin n → Ω =>
        Real.sqrt n • (estimator n X - θ₀) - (Real.sqrt n)⁻¹ • ∑ i, tupleEval P
          (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) (X i)) := by
      have hrange : (Set.range (preliminary n)).Countable := by
        by_cases hn : n = 0
        · subst n
          exact (Set.finite_range (preliminary 0)).countable
        · let point : (Fin d → ℤ) → EuclideanSpace ℝ (Fin d) := fun z =>
            (WithLp.equiv 2 (Fin d → ℝ)).symm
              (fun q => (z q : ℝ) / Real.sqrt n)
          refine (Set.countable_range point).mono ?_
          rintro t ⟨X, rfl⟩
          obtain ⟨z, hz⟩ := hpre_grid n (Nat.pos_of_ne_zero hn) X
          refine ⟨z, ?_⟩
          ext q
          exact (hz q).symm
      have hscore_meas : Measurable (fun X : Fin n → Ω =>
          scoreMean (indexedSplitScore splitSide scoreHalf) n X (preliminary n X)) := by
        apply measurable_diag_of_countable_range (preliminary n)
          (fun X t => scoreMean (indexedSplitScore splitSide scoreHalf) n X t)
          (hpre_meas n) hrange
        intro t
        unfold scoreMean indexedSplitScore
        exact (Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
          (hhalf_meas n (splitSide n i) t).comp
            (measurable_id.prodMk (measurable_pi_apply i))).const_smul ((n : ℝ)⁻¹)
      have hinfo_coord : ∀ j k, Measurable (fun X : Fin n → Ω =>
          empInfo (indexedSplitScore splitSide scoreHalf) n X (preliminary n X) j k) := by
        intro j k
        apply measurable_diag_of_countable_range (preliminary n)
          (fun X t => empInfo (indexedSplitScore splitSide scoreHalf) n X t j k)
          (hpre_meas n) hrange
        intro t
        unfold empInfo indexedSplitScore
        apply measurable_const.mul
        apply Finset.measurable_sum
        intro i _
        have hi : Measurable (fun X : Fin n → Ω =>
            scoreHalf n X (splitSide n i) t (X i)) :=
          (hhalf_meas n (splitSide n i) t).comp
            (measurable_id.prodMk (measurable_pi_apply i))
        exact ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
            EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp hi).mul
          ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) k :
            EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp hi)
      let A : (Fin n → Ω) → Matrix (Fin d) (Fin d) ℝ := fun X =>
        empInfo (indexedSplitScore splitSide scoreHalf) n X (preliminary n X)
      have hA : Measurable A :=
        measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun k => hinfo_coord j k
      have hAinv_coord : ∀ j k, Measurable (fun X => (A X)⁻¹ j k) := by
        intro j k
        rw [show (fun X => (A X)⁻¹ j k) = fun X =>
            ((A X).det)⁻¹ * (A X).adjugate j k by
          funext X
          rw [Matrix.inv_def, Ring.inverse_eq_inv']
          rfl]
        exact (continuous_id.matrix_det.measurable.comp hA).inv.mul
          ((continuous_id.matrix_adjugate.matrix_elem j k).measurable.comp hA)
      have hest_meas : Measurable (estimator n) := by
        apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
        rw [measurable_pi_iff]
        intro j
        rw [show (fun X => estimator n X j) = fun X => preliminary n X j +
            ∑ k, (A X)⁻¹ j k *
              scoreMean (indexedSplitScore splitSide scoreHalf) n X (preliminary n X) k by
          funext X
          rw [hest]
          rfl]
        exact ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
            EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp (hpre_meas n)).add
          (Finset.measurable_sum (Finset.univ : Finset (Fin d)) fun k _ =>
            (hAinv_coord j k).mul
              ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) k :
                EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp hscore_meas))
      have hif_meas : Measurable (fun x => tupleEval P
          (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) x) := by
        apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
        rw [measurable_pi_iff]
        intro j
        exact (Lp.stronglyMeasurable
          ((@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e j :
            ↥(L2ZeroMean P)) : Lp ℝ 2 P)).measurable
      have hsum_meas : Measurable (fun X : Fin n → Ω => ∑ i, tupleEval P
          (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) (X i)) :=
        Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
          hif_meas.comp (measurable_pi_apply i)
      exact (((hest_meas.sub measurable_const).const_smul (Real.sqrt n : ℝ)).sub
        (hsum_meas.const_smul ((Real.sqrt n)⁻¹ : ℝ)))
    have hset : MeasurableSet {X : Fin n → Ω | ε ≤ ‖Real.sqrt n • (estimator n X - θ₀) -
        (Real.sqrt n)⁻¹ • ∑ i, tupleEval P
          (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) (X i)‖} :=
      measurableSet_le measurable_const hres_meas.norm
    simpa only [μinf, trunc, Set.mem_setOf_eq] using!
      (pi_real_eq_infinitePi_real_of_truncate P n hset).symm

/-- **Semiparametric efficiency in vdV Theorem 25.57 (vector form).**
The primitive 25.55/25.56 bundle and DQM produce asymptotic linearity; the
standard efficient-score representation then identifies its influence tuple
as the vector EIF. -/
theorem oneStep_semiparametricallyEfficient_2557_native_vec
    {M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))} {μ : Measure Ω}
    {scoreLocal : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)}
    {splitSide : ∀ n, Fin n → Bool}
    {scoreHalf : ∀ n, (Fin n → Ω) → Bool → EuclideanSpace ℝ (Fin d) →
      Ω → EuclideanSpace ℝ (Fin d)}
    {preliminary estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    (h : @OneStep2557NativeHyp_vec Ω _ d P _ Θ _ _ _ S_θ T_nuis proj e
      M μ θ₀ scoreLocal splitSide scoreHalf preliminary estimator)
    (hDQM : DifferentiableQuadraticMean M μ θ₀
      (fun x => tupleEval P (fun j =>
        @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j)) x))
    {T : Submodule ℝ ↥(L2ZeroMean P)} {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h_mem : ∀ j, @candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e j ∈ T)
    (h_Dψ : ∀ (j : Fin d) (g : T),
      (EuclideanSpace.proj j ∘L Dψ) g =
        ⟪@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e j,
          (g : ↥(L2ZeroMean P))⟫_ℝ)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt_vec estimator ψ P T := by
  letI : T_nuis.HasOrthogonalProjection := proj
  have hEIF : IsEfficientInfluenceFunction_vec Dψ
      (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) := by
    intro j
    refine eif_of_representation_and_membership ?_ (h_mem j)
    intro g
    exact (h_Dψ j g).symm
  have hAL : AsymptoticallyLinearAt_vec estimator P
      (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) (ψ P) := by
    rw [h_ψ]
    exact oneStep_asymptoticallyLinear_2557_native_vec h hDQM
  exact estimator_semiparametricallyEfficient_of_asympLinear_eif_vec hEIF hAL

/-- **`d = 1` scalar agreement for native vdV 25.57.**  Projecting the native
vector estimator and its candidate influence tuple to the unique coordinate
gives the scalar `AsymptoticallyLinearAt` conclusion. No coordinatewise
diagonal-information premise is introduced. -/
theorem oneStep_asymptoticallyLinear_2557_native_fin_one
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [proj1 : T_nuis.HasOrthogonalProjection] {e : Fin 1 → Θ}
    {M : ParametricFamily Ω (EuclideanSpace ℝ (Fin 1))} {μ : Measure Ω}
    {θ₀ : EuclideanSpace ℝ (Fin 1)}
    {scoreLocal : EuclideanSpace ℝ (Fin 1) → Ω → EuclideanSpace ℝ (Fin 1)}
    {splitSide : ∀ n, Fin n → Bool}
    {scoreHalf : ∀ n, (Fin n → Ω) → Bool → EuclideanSpace ℝ (Fin 1) →
      Ω → EuclideanSpace ℝ (Fin 1)}
    {preliminary estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin 1)}
    (h : @OneStep2557NativeHyp_vec Ω _ 1 P _ Θ _ _ _ S_θ T_nuis proj1 e M μ θ₀
      scoreLocal splitSide scoreHalf preliminary estimator)
    (hDQM : DifferentiableQuadraticMean M μ θ₀
      (fun x => tupleEval P (fun j =>
        @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj1 (e j)) x)) :
    AsymptoticallyLinearAt (fun n X => estimator n X 0) P
      (@candidateVecEIF Ω _ P _ Θ _ _ _ 1 S_θ T_nuis proj1 e 0) (θ₀ 0) := by
  have hAL := oneStep_asymptoticallyLinear_2557_native_vec h hDQM
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hAL ε hε)
  · exact Filter.Eventually.of_forall fun _ => zero_le
  · exact Filter.Eventually.of_forall fun n => measure_mono (fun X hX => by
    simp only [Set.mem_setOf_eq] at hX ⊢
    have hcoord :
        Real.sqrt n * (estimator n X 0 - θ₀ 0) -
            (Real.sqrt n)⁻¹ *
              (∑ i, (((@candidateVecEIF Ω _ P _ Θ _ _ _ 1 S_θ T_nuis proj1 e 0 :
                ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)))
          = (Real.sqrt n • (estimator n X - θ₀) -
              (Real.sqrt n)⁻¹ •
                (∑ i, tupleEval P
                  (@candidateVecEIF Ω _ P _ Θ _ _ _ 1 S_θ T_nuis proj1 e) (X i))) 0 := by
      simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [show (∑ i, tupleEval P
          (@candidateVecEIF Ω _ P _ Θ _ _ _ 1 S_θ T_nuis proj1 e) (X i)) 0
            = ∑ i, tupleEval P
                (@candidateVecEIF Ω _ P _ Θ _ _ _ 1 S_θ T_nuis proj1 e) (X i) 0 by
        simp only [WithLp.ofLp_sum, Finset.sum_apply]]
      congr 2
    rw [hcoord] at hX
    calc
      ε ≤ |(Real.sqrt n • (estimator n X - θ₀) -
          (Real.sqrt n)⁻¹ •
            (∑ i, tupleEval P
              (@candidateVecEIF Ω _ P _ Θ _ _ _ 1 S_θ T_nuis proj1 e) (X i))) 0| := hX
      _ = ‖Real.sqrt n • (estimator n X - θ₀) -
          (Real.sqrt n)⁻¹ •
            (∑ i, tupleEval P
              (@candidateVecEIF Ω _ P _ Θ _ _ _ 1 S_θ T_nuis proj1 e) (X i))‖ := by
        rw [EuclideanSpace.norm_eq]
        simp only [Fin.sum_univ_one, Real.norm_eq_abs]
        exact (Real.sqrt_sq (abs_nonneg _)).symm)

end AsymptoticStatistics.Asymptotics.Discharge.OneStepVec
