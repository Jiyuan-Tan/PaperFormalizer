module
public import StatLean.AsymptoticStatistics.Core.CandidateIF
public import StatLean.AsymptoticStatistics.Operators.InformationLoss
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section

/-!
# Complete-case inverse-probability weighting

The explicit complete-case formula from van der Vaart, *Asymptotic Statistics*,
Lemma 25.41 (book pp.381–382), together with complete-event recovery data,
full- and observed-data IPW formulas, and their `L²₀` pairing properties.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Operators.CompleteCaseIPW

open AsymptoticStatistics.Core
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Operators.InformationLoss
open AsymptoticStatistics.ForMathlib.CondExpL2

variable {𝓨 𝓓 𝓧 : Type*}
  [MeasurableSpace 𝓨] [MeasurableSpace 𝓓] [MeasurableSpace 𝓧]

/-- Complete-case observation data for a coarsening map `M`.

Constitutive (vdV §25.5.3, pp.381–382): `C`, `Cobs`, `recover`,
`complete_iff`, and `recover_complete` express that on the complete event the
observed datum contains the full response. The three measurability fields ensure
that the displayed IPW formulas are measurable; they do not assert positivity.
In particular, the book's
bounded-away-from-zero condition on `R(C | Y)` is deliberately not a field. -/
structure CompleteCaseData (M : 𝓨 × 𝓓 → 𝓧) where
  /-- Constitutive (vdV §25.5.3, pp.381–382): complete coarsening states. -/
  C : Set 𝓓
  /-- Constitutive (vdV §25.5.3, pp.381–382): observed complete cases. -/
  Cobs : Set 𝓧
  /-- Constitutive (vdV §25.5.3, pp.381–382): recovery of `Y` on complete cases. -/
  recover : 𝓧 → 𝓨
  /-- Measurability of the complete-state event. -/
  measurableSet_C : MeasurableSet C
  /-- Measurability of the observed complete-case event. -/
  measurableSet_Cobs : MeasurableSet Cobs
  /-- Measurability of the recovery map. -/
  measurable_recover : Measurable recover
  /-- Constitutive (vdV §25.5.3, pp.381–382): observed completeness is exactly
  membership of the coarsening state in `C`. -/
  complete_iff : ∀ y δ, M (y, δ) ∈ Cobs ↔ δ ∈ C
  /-- Constitutive (vdV §25.5.3, pp.381–382): a complete observation recovers
  the full response. -/
  recover_complete : ∀ y δ, δ ∈ C → recover (M (y, δ)) = y

/-- Selection probability `π(y) = R(C | y)` from vdV Lemma 25.41.

Edge behavior: `ENNReal.toReal` returns `0` at `∞`; Markov kernels make
`r y C ≤ 1`, so the book-relevant case is finite.  Positivity is not built into
the definition and is supplied only to the analytic theorem that needs it. -/
noncomputable def selectionProbability
    {M : 𝓨 × 𝓓 → 𝓧} (r : Kernel 𝓨 𝓓) (cc : CompleteCaseData M) : 𝓨 → ℝ :=
  fun y => (r y cc.C).toReal

/-- Full-data raw IPW formula
`1{δ∈C} χ(y) / R(C|y)` (vdV Lemma 25.41, pp.381–382).

Edge behavior: division by zero uses Lean's field convention.  The analytic and
theorems below assume the book's uniform positive lower bound, so this edge
case is outside their scope. -/
noncomputable def ipwFullRaw
    {M : 𝓨 × 𝓓 → 𝓧} (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (r : Kernel 𝓨 𝓓) (cc : CompleteCaseData M)
    (χ : ↥(L2ZeroMean Q)) : 𝓨 × 𝓓 → ℝ :=
  fun p => cc.C.indicator
    (fun _ => ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) p.1 / selectionProbability r cc p.1) p.2

/-- Observed-data raw IPW formula, using `recover` on the observed complete-case
event (vdV Lemma 25.41, pp.381–382).

Edge behavior: outside `Cobs` the value is zero; division by a zero selection
probability follows Lean's field convention and is excluded by the positivity
hypothesis of the analytic theorem. -/
noncomputable def ipwObsRaw
    {M : 𝓨 × 𝓓 → 𝓧} (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (r : Kernel 𝓨 𝓓) (cc : CompleteCaseData M)
    (χ : ↥(L2ZeroMean Q)) : 𝓧 → ℝ :=
  fun x => cc.Cobs.indicator
    (fun _ => ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) (cc.recover x) /
      selectionProbability r cc (cc.recover x)) x

/-- The observed raw IPW formula pulls back to the full-data raw formula under
the coarsening map (vdV Lemma 25.41, pp.381–382). -/
theorem ipwObsRaw_comp_ae_eq_ipwFullRaw
    {M : 𝓨 × 𝓓 → 𝓧}
    (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (r : Kernel 𝓨 𝓓)
    (cc : CompleteCaseData M) (χ : ↥(L2ZeroMean Q)) :
    ipwObsRaw Q r cc χ ∘ M =ᵐ[Q ⊗ₘ r] ipwFullRaw Q r cc χ := by
  apply Filter.Eventually.of_forall
  rintro ⟨y, δ⟩
  by_cases hδ : δ ∈ cc.C
  · simp [ipwObsRaw, ipwFullRaw, hδ, cc.complete_iff, cc.recover_complete]
  · simp [ipwObsRaw, ipwFullRaw, hδ, cc.complete_iff]

/-- Raw lift of a full-`Q` score to the joint law `Q ⊗ₘ r`, by composition with
the first coordinate (vdV §25.5.3, pp.380–382).

Edge behavior: none beyond the `Lp` representative choice; the resulting
`L²₀` element is independent of that choice. -/
noncomputable def qScoreLiftRaw
    (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (s : ↥(L2ZeroMean Q)) : 𝓨 × 𝓓 → ℝ :=
  fun p => ((s : Lp ℝ 2 Q) : 𝓨 → ℝ) p.1

/-- The raw first-coordinate lift of a `Q` score is square-integrable and
mean-zero under `Q ⊗ₘ r`. -/
theorem qScoreLiftRaw_analytic
    (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (r : Kernel 𝓨 𝓓) [IsMarkovKernel r]
    (s : ↥(L2ZeroMean Q)) :
    MemLp (qScoreLiftRaw Q s) 2 (Q ⊗ₘ r) ∧
      ∫ p, qScoreLiftRaw Q s p ∂(Q ⊗ₘ r) = 0 := by
  have hfst : MeasurePreserving Prod.fst (Q ⊗ₘ r) Q :=
    ⟨measurable_fst, Measure.fst_compProd Q r⟩
  have hs_mem : MemLp (((s : Lp ℝ 2 Q) : 𝓨 → ℝ)) 2 Q := Lp.memLp _
  constructor
  · simpa only [qScoreLiftRaw, Function.comp_apply] using!
      hs_mem.comp_measurePreserving hfst
  · have hs_zero : ∫ y, ((s : Lp ℝ 2 Q) : 𝓨 → ℝ) y ∂Q = 0 :=
      (mem_L2ZeroMean_iff Q (s : Lp ℝ 2 Q)).mp s.2
    change ∫ p, ((s : Lp ℝ 2 Q) : 𝓨 → ℝ) p.1 ∂(Q ⊗ₘ r) = 0
    rw [← integral_map measurable_fst.aemeasurable
      (hfst.map_eq.symm ▸ Lp.aestronglyMeasurable (s : Lp ℝ 2 Q)), hfst.map_eq]
    exact hs_zero

/-- Lift a full-`Q` score into `L²₀(Q ⊗ₘ r)` along the first coordinate
(vdV §25.5.3, pp.380–382). -/
noncomputable def qScoreLift
    (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (r : Kernel 𝓨 𝓓) [IsMarkovKernel r]
    (s : ↥(L2ZeroMean Q)) : ↥(L2ZeroMean (Q ⊗ₘ r)) :=
  (CandidateIF.toL2ZeroMean
    { raw := qScoreLiftRaw Q s
      memLp2 := (qScoreLiftRaw_analytic Q r s).1
      mean_zero := (qScoreLiftRaw_analytic Q r s).2 })

/-- Under the book's bounded-away-from-zero condition, the observed IPW raw
formula is square-integrable and mean-zero (vdV Lemma 25.41, pp.381–382).

`ε > 0` and `ε ≤ R(C|Y)` `Q`-a.e. are explicit regularity assumptions from
the lemma; positivity is intentionally not hidden in `CompleteCaseData`. -/
theorem completeCaseIPW_analytic
    {M : 𝓨 × 𝓓 → 𝓧} (hM : Measurable M)
    (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (r : Kernel 𝓨 𝓓) [IsMarkovKernel r]
    (cc : CompleteCaseData M) (χ : ↥(L2ZeroMean Q))
    (ε : ℝ) (hε : 0 < ε) -- vdV Lemma 25.41 bounded-away constant.
    (hπ : ∀ᵐ y ∂Q, ε ≤ selectionProbability r cc y) : -- vdV p.381.
    MemLp (ipwObsRaw Q r cc χ) 2 ((Q ⊗ₘ r).map M) ∧
      ∫ x, ipwObsRaw Q r cc χ x ∂((Q ⊗ₘ r).map M) = 0 ∧
      MemLp (ipwFullRaw Q r cc χ) 2 (Q ⊗ₘ r) ∧
      ∫ p, ipwFullRaw Q r cc χ p ∂(Q ⊗ₘ r) = 0 := by
  have hχ_meas : Measurable (((χ : Lp ℝ 2 Q) : 𝓨 → ℝ)) :=
    (Lp.stronglyMeasurable (χ : Lp ℝ 2 Q)).measurable
  have hπ_meas : Measurable (selectionProbability r cc) :=
    (r.measurable_coe cc.measurableSet_C).ennreal_toReal
  have hfull_meas : Measurable (ipwFullRaw Q r cc χ) := by
    change Measurable fun p : 𝓨 × 𝓓 =>
      (Prod.snd ⁻¹' cc.C).indicator
        (fun p => ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) p.1 /
          selectionProbability r cc p.1) p
    exact ((hχ_meas.comp measurable_fst).div (hπ_meas.comp measurable_fst)).indicator
      (cc.measurableSet_C.preimage measurable_snd)
  have hobs_meas : Measurable (ipwObsRaw Q r cc χ) := by
    exact ((hχ_meas.comp cc.measurable_recover).div
      (hπ_meas.comp cc.measurable_recover)).indicator cc.measurableSet_Cobs
  have hχ_sq : Integrable (fun y => ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y ^ 2) Q :=
    (Lp.memLp (χ : Lp ℝ 2 Q)).integrable_sq
  have hfibre_sq : ∀ᵐ y ∂Q,
      Integrable (fun δ => ipwFullRaw Q r cc χ (y, δ) ^ 2) (r y) := by
    filter_upwards with y
    have hconst : Integrable
        (fun _ : 𝓓 =>
          (((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y /
            selectionProbability r cc y) ^ 2) (r y) := integrable_const _
    refine (hconst.indicator cc.measurableSet_C).congr ?_
    apply Filter.Eventually.of_forall
    intro δ
    by_cases hδ : δ ∈ cc.C <;> simp [ipwFullRaw, hδ]
  have hsquare_fibre : ∀ᵐ y ∂Q,
      ∫ δ, ‖ipwFullRaw Q r cc χ (y, δ) ^ 2‖ ∂(r y) =
        ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y ^ 2 /
          selectionProbability r cc y := by
    filter_upwards [hπ] with y hy
    have hπ_pos : 0 < selectionProbability r cc y := hε.trans_le hy
    have hπ_ne : selectionProbability r cc y ≠ 0 := hπ_pos.ne'
    calc
      ∫ δ, ‖ipwFullRaw Q r cc χ (y, δ) ^ 2‖ ∂(r y) =
          ∫ δ, cc.C.indicator
            (fun _ => (((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y /
              selectionProbability r cc y) ^ 2) δ ∂(r y) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun δ => ?_)
        by_cases hδ : δ ∈ cc.C <;>
          simp [ipwFullRaw, hδ, Real.norm_of_nonneg (sq_nonneg _)]
      _ = (r y cc.C).toReal *
          (((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y /
            selectionProbability r cc y) ^ 2 := by
        rw [integral_indicator_const _ cc.measurableSet_C]
        simp only [Measure.real, smul_eq_mul]
      _ = ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y ^ 2 /
          selectionProbability r cc y := by
        change selectionProbability r cc y *
            (((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y /
              selectionProbability r cc y) ^ 2 = _
        field_simp
  have hratio_int : Integrable
      (fun y => ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y ^ 2 /
        selectionProbability r cc y) Q := by
    have hbound : Integrable
        (fun y => ε⁻¹ * ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y ^ 2) Q :=
      hχ_sq.const_mul ε⁻¹
    refine hbound.mono' ((hχ_meas.pow_const 2).div hπ_meas).aestronglyMeasurable ?_
    filter_upwards [hπ] with y hy
    have hπ_pos : 0 < selectionProbability r cc y := hε.trans_le hy
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hπ_pos.le), div_eq_mul_inv]
    calc
      _ ≤ ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y ^ 2 * ε⁻¹ :=
        mul_le_mul_of_nonneg_left ((inv_le_inv₀ hπ_pos hε).2 hy) (sq_nonneg _)
      _ = ε⁻¹ * ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y ^ 2 := mul_comm _ _
  have houter_sq : Integrable
      (fun y => ∫ δ, ‖ipwFullRaw Q r cc χ (y, δ) ^ 2‖ ∂(r y)) Q :=
    hratio_int.congr (Filter.EventuallyEq.symm hsquare_fibre)
  have hfull_mem : MemLp (ipwFullRaw Q r cc χ) 2 (Q ⊗ₘ r) := by
    rw [memLp_two_iff_integrable_sq hfull_meas.aestronglyMeasurable]
    exact (Measure.integrable_compProd_iff
      (hfull_meas.pow_const 2).aestronglyMeasurable).2
      ⟨hfibre_sq, houter_sq⟩
  have hmean_fibre : ∀ᵐ y ∂Q,
      ∫ δ, ipwFullRaw Q r cc χ (y, δ) ∂(r y) =
        ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y := by
    filter_upwards [hπ] with y hy
    have hπ_pos : 0 < selectionProbability r cc y := hε.trans_le hy
    calc
      ∫ δ, ipwFullRaw Q r cc χ (y, δ) ∂(r y) =
          (r y cc.C).toReal *
            (((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y /
              selectionProbability r cc y) := by
        rw [show (fun δ => ipwFullRaw Q r cc χ (y, δ)) =
            cc.C.indicator (fun _ =>
              ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y /
                selectionProbability r cc y) by rfl,
          integral_indicator_const _ cc.measurableSet_C]
        simp only [Measure.real, smul_eq_mul]
      _ = ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y := by
        change selectionProbability r cc y *
            (((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y /
              selectionProbability r cc y) = _
        exact mul_div_cancel₀ _ hπ_pos.ne'
  have hfull_mean : ∫ p, ipwFullRaw Q r cc χ p ∂(Q ⊗ₘ r) = 0 := by
    rw [Measure.integral_compProd (hfull_mem.integrable one_le_two),
      integral_congr_ae hmean_fibre]
    exact (mem_L2ZeroMean_iff Q (χ : Lp ℝ 2 Q)).mp χ.2
  have hpull_mem : MemLp (ipwObsRaw Q r cc χ ∘ M) 2 (Q ⊗ₘ r) :=
    hfull_mem.ae_eq (ipwObsRaw_comp_ae_eq_ipwFullRaw Q r cc χ).symm
  have hobs_mem : MemLp (ipwObsRaw Q r cc χ) 2 ((Q ⊗ₘ r).map M) :=
    (memLp_map_measure_iff hobs_meas.aestronglyMeasurable hM.aemeasurable).2 hpull_mem
  have hobs_mean : ∫ x, ipwObsRaw Q r cc χ x ∂((Q ⊗ₘ r).map M) = 0 := by
    rw [integral_map hM.aemeasurable hobs_meas.aestronglyMeasurable]
    change ∫ p, (ipwObsRaw Q r cc χ ∘ M) p ∂(Q ⊗ₘ r) = 0
    rw [integral_congr_ae (ipwObsRaw_comp_ae_eq_ipwFullRaw Q r cc χ)]
    exact hfull_mean
  exact ⟨hobs_mem, hobs_mean, hfull_mem, hfull_mean⟩

/-- The complete-case IPW element of observed `L²₀`, constructed from the
explicit raw formula and the bounded-away-from-zero condition of vdV Lemma
25.41 (pp.381–382). -/
noncomputable def completeCaseIPW
    {M : 𝓨 × 𝓓 → 𝓧} (hM : Measurable M)
    (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (r : Kernel 𝓨 𝓓) [IsMarkovKernel r]
    (cc : CompleteCaseData M) (χ : ↥(L2ZeroMean Q))
    (ε : ℝ) (hε : 0 < ε)
    (hπ : ∀ᵐ y ∂Q, ε ≤ selectionProbability r cc y) :
    ↥(L2ZeroMean ((Q ⊗ₘ r).map M)) :=
  CandidateIF.toL2ZeroMean
    { raw := ipwObsRaw Q r cc χ
      memLp2 := (completeCaseIPW_analytic hM Q r cc χ ε hε hπ).1
      mean_zero := (completeCaseIPW_analytic hM Q r cc χ ε hε hπ).2.1 }

/-- The explicit IPW formula represented in full-data `L²₀(Q ⊗ₘ r)`. Its
information-loss image is the observed-data formula `completeCaseIPW`. -/
noncomputable def completeCaseIPWFull
    {M : 𝓨 × 𝓓 → 𝓧} (hM : Measurable M)
    (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (r : Kernel 𝓨 𝓓) [IsMarkovKernel r]
    (cc : CompleteCaseData M) (χ : ↥(L2ZeroMean Q))
    (ε : ℝ) (hε : 0 < ε)
    (hπ : ∀ᵐ y ∂Q, ε ≤ selectionProbability r cc y) :
    ↥(L2ZeroMean (Q ⊗ₘ r)) :=
  CandidateIF.toL2ZeroMean
    { raw := ipwFullRaw Q r cc χ
      memLp2 := (completeCaseIPW_analytic hM Q r cc χ ε hε hπ).2.2.1
      mean_zero := (completeCaseIPW_analytic hM Q r cc χ ε hε hπ).2.2.2 }

/-- The Doob pullback of the observed complete-case IPW element is its explicit
full-data representative. -/
private theorem doobSymm_completeCaseIPW_eq_full
    {M : 𝓨 × 𝓓 → 𝓧} (hM : Measurable M)
    (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (r : Kernel 𝓨 𝓓) [IsMarkovKernel r]
    (cc : CompleteCaseData M) (χ : ↥(L2ZeroMean Q))
    (ε : ℝ) (hε : 0 < ε)
    (hπ : ∀ᵐ y ∂Q, ε ≤ selectionProbability r cc y) :
    ((((doobL2Equiv hM).symm
          (completeCaseIPW hM Q r cc χ ε hε hπ :
            Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
        lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
        Lp ℝ 2 (Q ⊗ₘ r))) =
      (completeCaseIPWFull hM Q r cc χ ε hε hπ : Lp ℝ 2 (Q ⊗ₘ r)) := by
  apply Lp.ext
  have hdoob := doobL2Equiv_comp_apply hM
    ((doobL2Equiv hM).symm
      (completeCaseIPW hM Q r cc χ ε hε hπ :
        Lp ℝ 2 ((Q ⊗ₘ r).map M)))
  rw [(doobL2Equiv hM).apply_symm_apply] at hdoob
  have hobs_raw :
      (((completeCaseIPW hM Q r cc χ ε hε hπ :
          Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ))
        =ᵐ[(Q ⊗ₘ r).map M] ipwObsRaw Q r cc χ := by
    unfold completeCaseIPW
    exact CandidateIF.coeFn_toL2ZeroMean _
  have hobs_pull :
      (((completeCaseIPW hM Q r cc χ ε hε hπ :
          Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) ∘ M)
        =ᵐ[Q ⊗ₘ r] ipwObsRaw Q r cc χ ∘ M :=
    ae_eq_comp hM.aemeasurable hobs_raw
  have hfull_raw :
      (((completeCaseIPWFull hM Q r cc χ ε hε hπ :
          Lp ℝ 2 (Q ⊗ₘ r)) : 𝓨 × 𝓓 → ℝ))
        =ᵐ[Q ⊗ₘ r] ipwFullRaw Q r cc χ := by
    unfold completeCaseIPWFull
    exact CandidateIF.coeFn_toL2ZeroMean _
  exact hdoob.symm.trans
    (hobs_pull.trans
      ((ipwObsRaw_comp_ae_eq_ipwFullRaw Q r cc χ).trans hfull_raw.symm))

/-- The information-loss image of the full-data IPW element is exactly the
observed complete-case IPW element.  This identity connects the explicit
Lemma 25.41 formula with the affine characterization. -/
theorem informationLoss_completeCaseIPWFull
    {M : 𝓨 × 𝓓 → 𝓧} (hM : Measurable M)
    (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (r : Kernel 𝓨 𝓓) [IsMarkovKernel r]
    (cc : CompleteCaseData M) (χ : ↥(L2ZeroMean Q))
    (ε : ℝ) (hε : 0 < ε)
    (hπ : ∀ᵐ y ∂Q, ε ≤ selectionProbability r cc y) :
    informationLossOperator hM (Q ⊗ₘ r)
        (completeCaseIPWFull hM Q r cc χ ε hε hπ) =
      completeCaseIPW hM Q r cc χ ε hε hπ := by
  have hlp_closed : IsClosed
      (↑(lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2
        (Q ⊗ₘ r)) : Set (Lp ℝ 2 (Q ⊗ₘ r))) :=
    isClosed_aestronglyMeasurable hM.comap_le
  haveI hlp_complete : CompleteSpace
      (lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :=
    @IsClosed.completeSpace_coe _ _ (inferInstance : CompleteSpace (Lp ℝ 2 (Q ⊗ₘ r)))
      _ hlp_closed
  haveI hlp_projection :
      (lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2
        (Q ⊗ₘ r)).HasOrthogonalProjection :=
    @Submodule.HasOrthogonalProjection.ofCompleteSpace ℝ _ _ _ _ _ hlp_complete
  have hcond :
      condExpL2 ℝ ℝ hM.comap_le
          (completeCaseIPWFull hM Q r cc χ ε hε hπ : Lp ℝ 2 (Q ⊗ₘ r)) =
        (doobL2Equiv hM).symm
          (completeCaseIPW hM Q r cc χ ε hε hπ :
            Lp ℝ 2 ((Q ⊗ₘ r).map M)) := by
    rw [← doobSymm_completeCaseIPW_eq_full hM Q r cc χ ε hε hπ]
    unfold condExpL2
    exact Submodule.orthogonalProjection_mem_subspace_eq_self _
  apply Subtype.ext
  change (informationLossOperator hM (Q ⊗ₘ r)
      (completeCaseIPWFull hM Q r cc χ ε hε hπ) :
        Lp ℝ 2 ((Q ⊗ₘ r).map M)) =
    (completeCaseIPW hM Q r cc χ ε hε hπ :
      Lp ℝ 2 ((Q ⊗ₘ r).map M))
  rw [informationLossOperator_coe_eq, hcond,
    (doobL2Equiv hM).apply_symm_apply]

/-- Exact IPW pairing: the observed complete-case IPW element paired with the
information-loss image of a lifted `Q` score equals the full-data pairing of
the representer with that `Q` score (vdV Lemma 25.41, pp.381–382). -/
theorem inner_completeCaseIPW_informationLoss_qScoreLift
    {M : 𝓨 × 𝓓 → 𝓧} (hM : Measurable M)
    (Q : Measure 𝓨) [IsProbabilityMeasure Q]
    (r : Kernel 𝓨 𝓓) [IsMarkovKernel r]
    (cc : CompleteCaseData M) (χ s : ↥(L2ZeroMean Q))
    (ε : ℝ) (hε : 0 < ε)
    (hπ : ∀ᵐ y ∂Q, ε ≤ selectionProbability r cc y) :
    ⟪(completeCaseIPW hM Q r cc χ ε hε hπ :
        Lp ℝ 2 ((Q ⊗ₘ r).map M)),
      (informationLossOperator hM (Q ⊗ₘ r) (qScoreLift Q r s) :
        Lp ℝ 2 ((Q ⊗ₘ r).map M))⟫_ℝ =
      ⟪(χ : Lp ℝ 2 Q), (s : Lp ℝ 2 Q)⟫_ℝ := by
  have hfull_mem : MemLp (ipwFullRaw Q r cc χ) 2 (Q ⊗ₘ r) :=
    (completeCaseIPW_analytic hM Q r cc χ ε hε hπ).2.2.1
  have hscore_mem : MemLp (qScoreLiftRaw Q s) 2 (Q ⊗ₘ r) :=
    (qScoreLiftRaw_analytic Q r s).1
  have hprod_int : Integrable
      (fun p => qScoreLiftRaw Q s p * ipwFullRaw Q r cc χ p) (Q ⊗ₘ r) := by
    simpa only [Pi.mul_apply] using! hscore_mem.integrable_mul hfull_mem
  have hfibre : ∀ᵐ y ∂Q,
      ∫ δ, qScoreLiftRaw Q s (y, δ) * ipwFullRaw Q r cc χ (y, δ) ∂(r y) =
        ((s : Lp ℝ 2 Q) : 𝓨 → ℝ) y * ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y := by
    filter_upwards [hπ] with y hy
    have hπ_pos : 0 < selectionProbability r cc y := hε.trans_le hy
    calc
      ∫ δ, qScoreLiftRaw Q s (y, δ) * ipwFullRaw Q r cc χ (y, δ) ∂(r y) =
          ∫ δ, cc.C.indicator
            (fun _ => ((s : Lp ℝ 2 Q) : 𝓨 → ℝ) y *
              (((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y /
                selectionProbability r cc y)) δ ∂(r y) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun δ => ?_)
        by_cases hδ : δ ∈ cc.C <;>
          simp [qScoreLiftRaw, ipwFullRaw, hδ]
      _ = (r y cc.C).toReal *
          (((s : Lp ℝ 2 Q) : 𝓨 → ℝ) y *
            (((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y /
              selectionProbability r cc y)) := by
        rw [integral_indicator_const _ cc.measurableSet_C]
        simp only [Measure.real, smul_eq_mul]
      _ = ((s : Lp ℝ 2 Q) : 𝓨 → ℝ) y *
          ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y := by
        change selectionProbability r cc y *
            (((s : Lp ℝ 2 Q) : 𝓨 → ℝ) y *
              (((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y /
                selectionProbability r cc y)) = _
        field_simp
  have hipw_raw :
      (((completeCaseIPWFull hM Q r cc χ ε hε hπ :
          Lp ℝ 2 (Q ⊗ₘ r)) : 𝓨 × 𝓓 → ℝ))
        =ᵐ[Q ⊗ₘ r] ipwFullRaw Q r cc χ := by
    unfold completeCaseIPWFull
    exact CandidateIF.coeFn_toL2ZeroMean _
  have hscore_raw :
      (((qScoreLift Q r s : Lp ℝ 2 (Q ⊗ₘ r)) : 𝓨 × 𝓓 → ℝ))
        =ᵐ[Q ⊗ₘ r] qScoreLiftRaw Q s := by
    unfold qScoreLift
    exact CandidateIF.coeFn_toL2ZeroMean _
  have hfull_pair :
      ⟪(completeCaseIPWFull hM Q r cc χ ε hε hπ : Lp ℝ 2 (Q ⊗ₘ r)),
        (qScoreLift Q r s : Lp ℝ 2 (Q ⊗ₘ r))⟫_ℝ =
        ⟪(χ : Lp ℝ 2 Q), (s : Lp ℝ 2 Q)⟫_ℝ := by
    rw [L2.inner_def, L2.inner_def]
    calc
      ∫ p, ⟪((completeCaseIPWFull hM Q r cc χ ε hε hπ :
              Lp ℝ 2 (Q ⊗ₘ r)) : 𝓨 × 𝓓 → ℝ) p,
            ((qScoreLift Q r s : Lp ℝ 2 (Q ⊗ₘ r)) : 𝓨 × 𝓓 → ℝ) p⟫_ℝ ∂(Q ⊗ₘ r) =
          ∫ p, qScoreLiftRaw Q s p * ipwFullRaw Q r cc χ p ∂(Q ⊗ₘ r) := by
        refine integral_congr_ae ?_
        filter_upwards [hipw_raw, hscore_raw] with p hp hs
        rw [hp, hs]
        rfl
      _ = ∫ y, ∫ δ, qScoreLiftRaw Q s (y, δ) *
          ipwFullRaw Q r cc χ (y, δ) ∂(r y) ∂Q :=
        Measure.integral_compProd hprod_int
      _ = ∫ y, ((s : Lp ℝ 2 Q) : 𝓨 → ℝ) y *
          ((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y ∂Q :=
        integral_congr_ae hfibre
      _ = ∫ y, ⟪((χ : Lp ℝ 2 Q) : 𝓨 → ℝ) y,
          ((s : Lp ℝ 2 Q) : 𝓨 → ℝ) y⟫_ℝ ∂Q := by rfl
  calc
    ⟪(completeCaseIPW hM Q r cc χ ε hε hπ :
        Lp ℝ 2 ((Q ⊗ₘ r).map M)),
      (informationLossOperator hM (Q ⊗ₘ r) (qScoreLift Q r s) :
        Lp ℝ 2 ((Q ⊗ₘ r).map M))⟫_ℝ =
        ⟪(informationLossOperator hM (Q ⊗ₘ r) (qScoreLift Q r s) :
            Lp ℝ 2 ((Q ⊗ₘ r).map M)),
          (completeCaseIPW hM Q r cc χ ε hε hπ :
            Lp ℝ 2 ((Q ⊗ₘ r).map M))⟫_ℝ := real_inner_comm _ _
    _ = ⟪(qScoreLift Q r s : Lp ℝ 2 (Q ⊗ₘ r)),
        ((((doobL2Equiv hM).symm
            (completeCaseIPW hM Q r cc χ ε hε hπ :
              Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
          lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
          Lp ℝ 2 (Q ⊗ₘ r)))⟫_ℝ := by
      rw [informationLossOperator_coe_eq,
        ← informationLossRaw_apply hM (Q ⊗ₘ r)]
      exact inner_informationLossRaw hM (Q ⊗ₘ r)
        (qScoreLift Q r s : Lp ℝ 2 (Q ⊗ₘ r))
        (completeCaseIPW hM Q r cc χ ε hε hπ :
          Lp ℝ 2 ((Q ⊗ₘ r).map M))
    _ = ⟪(qScoreLift Q r s : Lp ℝ 2 (Q ⊗ₘ r)),
        (completeCaseIPWFull hM Q r cc χ ε hε hπ :
          Lp ℝ 2 (Q ⊗ₘ r))⟫_ℝ := by
      rw [doobSymm_completeCaseIPW_eq_full hM Q r cc χ ε hε hπ]
    _ = ⟪(completeCaseIPWFull hM Q r cc χ ε hε hπ :
          Lp ℝ 2 (Q ⊗ₘ r)),
        (qScoreLift Q r s : Lp ℝ 2 (Q ⊗ₘ r))⟫_ℝ := real_inner_comm _ _
    _ = ⟪(χ : Lp ℝ 2 Q), (s : Lp ℝ 2 Q)⟫_ℝ := hfull_pair

end AsymptoticStatistics.Operators.CompleteCaseIPW
