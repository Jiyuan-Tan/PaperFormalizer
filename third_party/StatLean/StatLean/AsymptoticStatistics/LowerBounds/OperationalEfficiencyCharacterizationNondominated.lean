module
public import StatLean.AsymptoticStatistics.LowerBounds.NondominatedOperationalEfficiencyAnalytic
public import StatLean.AsymptoticStatistics.ForMathlib.SubsequenceLimit

@[expose] public section

/-! # Full nondominated scalar Lemma 25.23 -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace AsymptoticStatistics.LowerBounds.OperationalEfficiencyCharacterizationNondominated

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.Core.NondominatedTangent
open AsymptoticStatistics.Core.NondominatedPathwise
open AsymptoticStatistics.Core.NondominatedEfficiencyOperational
open AsymptoticStatistics.LowerBounds.NondominatedOperationalEfficiencyAnalytic
open AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Nondominated selected-path regularity derives the baseline weak limit.

Proof idea: select the derived zero carrier score, use `hpd.derivative_spec`
and linearity to show the local functional-center displacement is `o(1/√n)`,
then apply the zero-score local-product equivalence. -/
theorem hasLimitDistributionAt_of_isRegularAtND
    {T_n : ∀ n, (Fin n → Ω) → ℝ} {ψ : Measure Ω → ℝ}
    (C : NondominatedTangentCone P) (L : Measure ℝ)
    (hpd : NondominatedPathwiseDifferentiableAt P C ψ)
    (hT : ∀ n, Measurable (T_n n))
    (hreg : IsRegularAtND C T_n ψ L) :
    HasLimitDistributionAt T_n P (ψ P) L := by
  let z : {g : ↥(L2ZeroMean P) // g ∈ C.carrier} := ⟨0, zero_mem C⟩
  let γ := C.selectedPath z
  have hγscore : γ.score = 0 := by
    simpa only [γ, z] using C.selectedPath_score z
  let Q : (n : ℕ) → Measure (Fin n → Ω) := fun n =>
    Measure.pi (fun _ : Fin n => γ.curve ((Real.sqrt n)⁻¹))
  let Xinner : ∀ n, (Fin n → Ω) → ℝ := fun n X =>
    Real.sqrt n * (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹)))
  let Xouter : ∀ n, (Fin n → Ω) → ℝ := fun n =>
    centeredEstimator T_n (ψ P) n
  haveI hQprob : ∀ n, IsProbabilityMeasure (Q n) := fun n => by
    letI : IsProbabilityMeasure (γ.curve ((Real.sqrt n)⁻¹)) :=
      γ.curve_isProbability _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    infer_instance
  have hXinnerMeas : ∀ n, Measurable (Xinner n) := fun n =>
    Measurable.const_mul ((hT n).sub_const _) _
  have hXouterMeas : ∀ n, Measurable (Xouter n) := fun n =>
    Measurable.const_mul ((hT n).sub_const _) _
  have hlocal : AsymptoticStatistics.WeakConverges
      (fun n => (Q n).map (Xinner n)) L := by
    simpa only [Q, Xinner, γ] using hreg z
  haveI hlocalProb : ∀ n, IsProbabilityMeasure ((Q n).map (Xinner n)) := fun n =>
    Measure.isProbabilityMeasure_map (hXinnerMeas n).aemeasurable
  have hLreal : L.real Set.univ = 1 := by
    have h := hlocal (BoundedContinuousFunction.const ℝ (1 : ℝ))
    have h' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
        (nhds (L.real Set.univ)) := by
      simpa only [BoundedContinuousFunction.const_apply', integral_const, smul_eq_mul,
        mul_one, probReal_univ] using h
    exact (tendsto_nhds_unique tendsto_const_nhds h').symm
  letI : IsProbabilityMeasure L :=
    MeasureTheory.isProbabilityMeasure_iff_real.mpr hLreal
  have htzero : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (nhds 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have htpos : ∀ᶠ n : ℕ in atTop, 0 < (Real.sqrt n)⁻¹ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact inv_pos.mpr (Real.sqrt_pos.mpr hnR)
  have htright : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htzero, htpos⟩
  have hquot := (hpd.derivative_spec z).comp htright
  have hderiv : hpd.derivative
      ⟨(z : ↥(L2ZeroMean P)), selected_mem_tangentSpace C z⟩ = 0 := by
    simpa only [z] using! hpd.derivative.map_zero
  have hshift : Tendsto (fun n : ℕ => Real.sqrt n *
      (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P)) atTop (nhds 0) := by
    rw [← hderiv]
    have heq : (fun n : ℕ => Real.sqrt n *
        (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P)) =
        (fun n : ℕ => (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P) /
          (Real.sqrt n)⁻¹) := by
      funext n
      by_cases hn : Real.sqrt n = 0
      · simp [hn]
      · field_simp
    rw [heq]
    simpa only [Function.comp_apply, γ] using! hquot
  have hdist : ∀ ε > 0, Tendsto (fun n => (Q n).real
      {X | ε ≤ dist (Xinner n X) (Xouter n X)}) atTop (nhds 0) := by
    intro ε hε
    have hev : ∀ᶠ n : ℕ in atTop,
        |Real.sqrt n * (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P)| < ε := by
      simpa only [Real.dist_eq, sub_zero] using
        (Metric.tendsto_nhds.mp hshift) ε hε
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [hev] with n hn
    have hset : {X | ε ≤ dist (Xinner n X) (Xouter n X)} =
        (∅ : Set (Fin n → Ω)) := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le,
        Real.dist_eq]
      rw [show Xinner n X - Xouter n X =
          -Real.sqrt n * (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P) by
        simp only [Xinner, Xouter, centeredEstimator]
        ring]
      simpa only [neg_mul, abs_neg] using hn
    rw [hset, measureReal_empty]
  have hlocalOuter : AsymptoticStatistics.WeakConverges
      (fun n => (Q n).map (Xouter n)) L :=
    AsymptoticStatistics.WeakConverges.slutsky_of_tendstoInMeasure_dist
      (fun n => (hXinnerMeas n).aemeasurable)
      (fun n => (hXouterMeas n).aemeasurable) hlocal hdist
  intro f
  have hlocalInt : Tendsto (fun n => ∫ X, f (Xouter n X) ∂(Q n)) atTop
      (nhds (∫ x, f x ∂L)) := by
    have h := hlocalOuter f
    convert h using 1
    funext n
    exact (integral_map (hXouterMeas n).aemeasurable
      f.continuous.aestronglyMeasurable).symm
  have hequiv := zero_score_local_product_equivalent γ hγscore
    (fun n X => f (Xouter n X)) ‖f‖
    (fun n => f.continuous.measurable.comp (hXouterMeas n))
    (fun n X => by
      simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (Xouter n X))
  have hbaseInt : Tendsto (fun n => ∫ X, f (Xouter n X)
      ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds (∫ x, f x ∂L)) := by
    have h := hlocalInt.sub hequiv
    simpa only [Q, γ, sub_sub_cancel, sub_zero] using h
  convert hbaseInt using 1
  funext n
  exact integral_map (hXouterMeas n).aemeasurable
    f.continuous.aestronglyMeasurable

/-- Asymptotic linearity by the EIF implies nondominated regularity with the
efficient Gaussian law.

Proof idea: local score CLT on every selected path, right pathwise
differentiability, contiguity transfer of the AL residual, and Slutsky. -/
theorem regular_and_gaussian_of_asymptoticallyLinearND
    {T_n : ∀ n, (Fin n → Ω) → ℝ} {ψ : Measure Ω → ℝ}
    (C : NondominatedTangentCone P)
    -- USER-INPUT: pathwise differentiability and its efficient influence function;
    -- vdV Lemma 25.23.
    (hpd : NondominatedPathwiseDifferentiableAt P C ψ)
    {φ : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace C) hpd.derivative φ)
    (hT : ∀ n, Measurable (T_n n))
    (hAL : AsymptoticallyLinearAt T_n P φ (ψ P)) :
    IsRegularAtND C T_n ψ
      (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) := by
  intro g
  let γ := C.selectedPath g
  let Q : (n : ℕ) → Measure (Fin n → Ω) := fun n =>
    Measure.pi (fun _ : Fin n => γ.curve ((Real.sqrt n)⁻¹))
  let score : ∀ n, (Fin n → Ω) → ℝ := fun n => normalizedScoreSum φ n
  let base : ∀ n, (Fin n → Ω) → ℝ := fun n =>
    centeredEstimator T_n (ψ P) n
  let c : ℝ := ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ
  let score0 : ∀ n, (Fin n → Ω) → ℝ := fun n X => score n X - c
  let temp : ∀ n, (Fin n → Ω) → ℝ := fun n X => base n X - c
  let localEst : ∀ n, (Fin n → Ω) → ℝ := fun n X =>
    Real.sqrt n * (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹)))
  haveI hQprob : ∀ n, IsProbabilityMeasure (Q n) := fun n => by
    letI : IsProbabilityMeasure (γ.curve ((Real.sqrt n)⁻¹)) :=
      γ.curve_isProbability _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    infer_instance
  have hscoreMeas : ∀ n, Measurable (score n) := by
    intro n
    unfold score normalizedScoreSum
    exact Measurable.const_mul
      (Finset.measurable_sum _ fun i _ =>
        (Lp.stronglyMeasurable (φ : Lp ℝ 2 P)).measurable.comp
          (measurable_pi_apply i)) _
  have hbaseMeas : ∀ n, Measurable (base n) := fun n =>
    Measurable.const_mul ((hT n).sub_const _) _
  have hscore0Meas : ∀ n, Measurable (score0 n) := fun n =>
    (hscoreMeas n).sub_const _
  have htempMeas : ∀ n, Measurable (temp n) := fun n =>
    (hbaseMeas n).sub_const _
  have hlocalMeas : ∀ n, Measurable (localEst n) := fun n =>
    Measurable.const_mul ((hT n).sub_const _) _
  have hscoreRaw : AsymptoticStatistics.WeakConverges
      (fun n => (Q n).map (score n))
      (gaussianReal c ⟨‖φ‖ ^ 2, sq_nonneg _⟩) := by
    have h := qmd_local_score_clt γ 1 zero_le_one φ
    simpa only [Q, score, γ, one_mul, c, C.selectedPath_score g] using h
  have hscore0 : AsymptoticStatistics.WeakConverges
      (fun n => (Q n).map (score0 n))
      (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) := by
    have hcont : Continuous (fun x : ℝ => x - c) := by fun_prop
    have hmeas : Measurable (fun x : ℝ => x - c) := hcont.measurable
    have h := hscoreRaw.map hcont hmeas
    have hmap : ∀ n, (Q n).map (score0 n) =
        ((Q n).map (score n)).map (fun x : ℝ => x - c) := by
      intro n
      rw [Measure.map_map hmeas (hscoreMeas n)]
      rfl
    have hlim :
        (gaussianReal c ⟨‖φ‖ ^ 2, sq_nonneg _⟩).map (fun x => x - c) =
          gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩ := by
      exact (ProbabilityTheory.gaussianReal_map_sub_const c).trans
        (congrArg (fun m => gaussianReal m _) (sub_self c))
    simpa only [hmap, hlim] using h
  let residual : ∀ n, (Fin n → Ω) → ℝ := fun n X => base n X - score n X
  have hresMeas : ∀ n, Measurable (residual n) := fun n =>
    (hbaseMeas n).sub (hscoreMeas n)
  have hresQ : ∀ ε > 0, Tendsto (fun n => (Q n) {X | ε ≤ |residual n X|})
      atTop (nhds 0) := by
    intro ε hε
    have hresP : Tendsto (fun n => (Measure.pi (fun _ : Fin n => P))
        {X | ε ≤ |residual n X|}) atTop (nhds 0) := by
      simpa only [residual, base, score, centeredEstimator, normalizedScoreSum] using
        hAL ε hε
    have hA : ∀ n, MeasurableSet {X | ε ≤ |residual n X|} := fun n =>
      measurableSet_le measurable_const (hresMeas n).abs
    have h := qmd_local_contiguous γ 1 zero_le_one
      (fun n => {X | ε ≤ |residual n X|}) hA hresP
    simpa only [Q, γ, one_mul] using h
  have hdist1 : ∀ ε > 0, Tendsto (fun n => (Q n).real
      {X | ε ≤ dist (score0 n X) (temp n X)}) atTop (nhds 0) := by
    intro ε hε
    have hset : ∀ n, {X | ε ≤ dist (score0 n X) (temp n X)} =
        {X | ε ≤ |residual n X|} := by
      intro n
      ext X
      simp only [Set.mem_setOf_eq, Real.dist_eq]
      rw [show score0 n X - temp n X = -residual n X by
        simp only [score0, temp, residual]
        ring, abs_neg]
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hresQ ε hε)
    simpa only [hset, Function.comp_apply, ENNReal.toReal_zero] using! h
  have htemp : AsymptoticStatistics.WeakConverges
      (fun n => (Q n).map (temp n))
      (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) :=
    AsymptoticStatistics.WeakConverges.slutsky_of_tendstoInMeasure_dist
      (fun n => (hscore0Meas n).aemeasurable)
      (fun n => (htempMeas n).aemeasurable) hscore0 hdist1
  have htzero : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (nhds 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have htpos : ∀ᶠ n : ℕ in atTop, 0 < (Real.sqrt n)⁻¹ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact inv_pos.mpr (Real.sqrt_pos.mpr hnR)
  have htright : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htzero, htpos⟩
  have hquot := (hpd.derivative_spec g).comp htright
  have hderiv : hpd.derivative
      ⟨(g : ↥(L2ZeroMean P)), selected_mem_tangentSpace C g⟩ = c := by
    calc
      hpd.derivative ⟨(g : ↥(L2ZeroMean P)), selected_mem_tangentSpace C g⟩ =
          ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ := (hEIF.1 _).symm
      _ = c := rfl
  have hshift : Tendsto (fun n : ℕ => Real.sqrt n *
      (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P)) atTop (nhds c) := by
    rw [← hderiv]
    have heq : (fun n : ℕ => Real.sqrt n *
        (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P)) =
        (fun n : ℕ => (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P) /
          (Real.sqrt n)⁻¹) := by
      funext n
      by_cases hn : Real.sqrt n = 0
      · simp [hn]
      · field_simp
    rw [heq]
    simpa only [Function.comp_apply, γ] using! hquot
  have hdist2 : ∀ ε > 0, Tendsto (fun n => (Q n).real
      {X | ε ≤ dist (temp n X) (localEst n X)}) atTop (nhds 0) := by
    intro ε hε
    have hclose : Tendsto (fun n : ℕ =>
        |Real.sqrt n * (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P) - c|)
        atTop (nhds 0) := by
      have hsub : Tendsto (fun n : ℕ => Real.sqrt n *
          (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P) - c) atTop
          (nhds (c - c)) := hshift.sub (tendsto_const_nhds (x := c))
      have h := hsub.abs
      simpa only [sub_self, abs_zero] using h
    have hev : ∀ᶠ n : ℕ in atTop,
        |Real.sqrt n * (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P) - c| < ε := by
      simpa only [Real.dist_eq, sub_zero, abs_abs] using
        (Metric.tendsto_nhds.mp hclose) ε hε
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [hev] with n hn
    have hset : {X | ε ≤ dist (temp n X) (localEst n X)} =
        (∅ : Set (Fin n → Ω)) := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le,
        Real.dist_eq]
      rw [show temp n X - localEst n X =
          Real.sqrt n * (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ P) - c by
        simp only [temp, base, localEst, centeredEstimator]
        ring]
      exact hn
    rw [hset, measureReal_empty]
  exact AsymptoticStatistics.WeakConverges.slutsky_of_tendstoInMeasure_dist
    (fun n => (htempMeas n).aemeasurable)
    (fun n => (hlocalMeas n).aemeasurable) htemp hdist2

/-- Nondominated regularity with the efficient Gaussian law forces the
asymptotically linear expansion.

Proof idea: baseline joint subsequences, nonnegative tilt rigidity, finite
carrier projection bounds, and outer projection exhaustion. -/
theorem asymptoticallyLinear_of_regular_and_gaussianND
    {T_n : ∀ n, (Fin n → Ω) → ℝ} {ψ : Measure Ω → ℝ}
    (C : NondominatedTangentCone P)
    (hpd : NondominatedPathwiseDifferentiableAt P C ψ)
    {φ : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace C) hpd.derivative φ)
    (hT : ∀ n, Measurable (T_n n))
    (hreg : IsRegularAtND C T_n ψ
      (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩)) :
    AsymptoticallyLinearAt T_n P φ (ψ P) := by
  classical
  let est : ∀ n, (Fin n → Ω) → ℝ := fun n => centeredEstimator T_n (ψ P) n
  let score : ∀ n, (Fin n → Ω) → ℝ := fun n => normalizedScoreSum φ n
  let pair : ∀ n, (Fin n → Ω) → ℝ × ℝ := fun n X => (est n X, score n X)
  let baseMeasure : (n : ℕ) → Measure (Fin n → Ω) := fun n =>
    Measure.pi (fun _ : Fin n => P)
  let estLaw : ℕ → Measure ℝ := fun n => (baseMeasure n).map (est n)
  let scoreLaw : ℕ → Measure ℝ := fun n => (baseMeasure n).map (score n)
  let jointLaw : ℕ → Measure (ℝ × ℝ) := fun n => (baseMeasure n).map (pair n)
  have hestMeas : ∀ n, Measurable (est n) := fun n =>
    Measurable.const_mul ((hT n).sub_const _) _
  have hscoreMeas : ∀ n, Measurable (score n) := by
    intro n
    unfold score normalizedScoreSum
    exact Measurable.const_mul
      (Finset.measurable_sum _ fun i _ =>
        (Lp.stronglyMeasurable (φ : Lp ℝ 2 P)).measurable.comp
          (measurable_pi_apply i)) _
  have hpairMeas : ∀ n, Measurable (pair n) := fun n =>
    (hestMeas n).prodMk (hscoreMeas n)
  have hresMeas : ∀ n, Measurable (fun X => est n X - score n X) := fun n =>
    (hestMeas n).sub (hscoreMeas n)
  haveI hestProb : ∀ n, IsProbabilityMeasure (estLaw n) := fun n =>
    Measure.isProbabilityMeasure_map (hestMeas n).aemeasurable
  haveI hscoreProb : ∀ n, IsProbabilityMeasure (scoreLaw n) := fun n =>
    Measure.isProbabilityMeasure_map (hscoreMeas n).aemeasurable
  haveI hjointProb : ∀ n, IsProbabilityMeasure (jointLaw n) := fun n =>
    Measure.isProbabilityMeasure_map (hpairMeas n).aemeasurable
  have hestWeak : AsymptoticStatistics.WeakConverges estLaw
      (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) := by
    simpa only [estLaw, baseMeasure, est, HasLimitDistributionAt] using!
      hasLimitDistributionAt_of_isRegularAtND C
        (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) hpd hT hreg
  let z : {g : ↥(L2ZeroMean P) // g ∈ C.carrier} := ⟨0, zero_mem C⟩
  have hscoreWeak : AsymptoticStatistics.WeakConverges scoreLaw
      (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) := by
    have h := qmd_local_score_clt (C.selectedPath z) 0 le_rfl φ
    simpa only [scoreLaw, baseMeasure, score, zero_mul,
      (C.selectedPath z).curve_at_zero] using h
  have hfst : ∀ n, (jointLaw n).map Prod.fst = estLaw n := by
    intro n
    simp only [jointLaw, estLaw, Measure.map_map measurable_fst (hpairMeas n)]
    rfl
  have hsnd : ∀ n, (jointLaw n).map Prod.snd = scoreLaw n := by
    intro n
    simp only [jointLaw, scoreLaw, Measure.map_map measurable_snd (hpairMeas n)]
    rfl
  have hfstImage :
      (fun μ : Measure (ℝ × ℝ) => μ.map Prod.fst) '' Set.range jointLaw =
        Set.range estLaw := by
    ext μ
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (hfst n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨jointLaw n, ⟨n, rfl⟩, hfst n⟩
  have hsndImage :
      (fun μ : Measure (ℝ × ℝ) => μ.map Prod.snd) '' Set.range jointLaw =
        Set.range scoreLaw := by
    ext μ
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (hsnd n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨jointLaw n, ⟨n, rfl⟩, hsnd n⟩
  have hjointTight : IsTightMeasureSet (Set.range jointLaw) :=
    Prohorov.tight_prod_of_tight_marginals _
      (hfstImage ▸ Prohorov.weakConverges_range_tight estLaw
        (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) hestWeak)
      (hsndImage ▸ Prohorov.weakConverges_range_tight scoreLaw
        (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) hscoreWeak)
  unfold AsymptoticallyLinearAt
  intro ε hε
  apply AsymptoticStatistics.SubsequenceLimit.tendsto_of_subseq_tendsto
  intro χ hχ
  have hsubTight : IsTightMeasureSet (Set.range (fun k => jointLaw (χ k))) :=
    hjointTight.subset (by
      rintro _ ⟨k, rfl⟩
      exact ⟨χ k, rfl⟩)
  obtain ⟨σ, hσ, π, hπprob, hπweak⟩ :=
    Prohorov.extract_weak_subseq (fun k => jointLaw (χ k)) hsubTight
  letI : IsProbabilityMeasure π := hπprob
  have hπweak' : AsymptoticStatistics.WeakConverges
      (fun k => (baseMeasure (χ (σ k))).map
        (fun X => (est (χ (σ k)) X, score (χ (σ k)) X))) π := by
    simpa only [jointLaw, pair] using hπweak
  have hdirac := residual_subseq_limit_eq_dirac_of_regular C hpd hEIF hT hreg
    (χ ∘ σ) (hχ.comp hσ) π (by
      simpa only [baseMeasure, est, score, Function.comp_apply] using hπweak')
  let sub : ℝ × ℝ → ℝ := fun q => q.1 - q.2
  have hresWeak0 := hπweak'.map (by fun_prop : Continuous sub) (by fun_prop : Measurable sub)
  have hresWeak : AsymptoticStatistics.WeakConverges
      (fun k => (baseMeasure (χ (σ k))).map
        (fun X => est (χ (σ k)) X - score (χ (σ k)) X))
      (Measure.dirac 0) := by
    rw [hdirac] at hresWeak0
    have hmap : ∀ k,
        ((baseMeasure (χ (σ k))).map
          (fun X => (est (χ (σ k)) X, score (χ (σ k)) X))).map sub =
        (baseMeasure (χ (σ k))).map
          (fun X => est (χ (σ k)) X - score (χ (σ k)) X) := by
      intro k
      rw [Measure.map_map (by fun_prop : Measurable sub) (hpairMeas _)]
      rfl
    simpa only [hmap] using hresWeak0
  let resLaw : ℕ → Measure ℝ := fun k =>
    (baseMeasure (χ (σ k))).map
      (fun X => est (χ (σ k)) X - score (χ (σ k)) X)
  haveI hresProb : ∀ k, IsProbabilityMeasure (resLaw k) := fun k =>
    Measure.isProbabilityMeasure_map (hresMeas _).aemeasurable
  let pres : ℕ → ProbabilityMeasure ℝ := fun k => ⟨resLaw k, inferInstance⟩
  let pzero : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩
  have hpTendsto : Tendsto pres atTop (nhds pzero) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    simpa only [pres, pzero, resLaw] using! hresWeak
  let tail : Set ℝ := {x | ε ≤ |x|}
  have htailClosed : IsClosed tail := isClosed_Ici.preimage continuous_abs
  have hzeroTail : (0 : ℝ) ∉ tail := by
    simpa only [tail, Set.mem_setOf_eq, abs_zero] using (not_le.mpr hε)
  have hzeroFrontier : (0 : ℝ) ∉ frontier tail := by
    intro hz
    apply hzeroTail
    rw [← htailClosed.closure_eq]
    exact frontier_subset_closure hz
  have hfrontierNull : (Measure.dirac 0) (frontier tail) = 0 := by
    rw [Measure.dirac_apply' 0 isClosed_frontier.measurableSet]
    simp [hzeroFrontier]
  have htail := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hpTendsto hfrontierNull
  have htailZero : (Measure.dirac 0) tail = 0 := by
    rw [Measure.dirac_apply' 0 htailClosed.measurableSet]
    simp [hzeroTail]
  have hresApply : ∀ k, resLaw k tail =
      baseMeasure (χ (σ k))
        {X | ε ≤ |est (χ (σ k)) X - score (χ (σ k)) X|} := by
    intro k
    rw [Measure.map_apply (hresMeas _ ) htailClosed.measurableSet]
    rfl
  refine ⟨σ, hσ, ?_⟩
  rw [show (pzero : Measure ℝ) tail = 0 by exact htailZero] at htail
  simp_rw [show ∀ k, (pres k : Measure ℝ) tail = resLaw k tail from fun _ => rfl,
    hresApply] at htail
  simpa only [baseMeasure, est, score, centeredEstimator, normalizedScoreSum,
    Function.comp_apply] using htail

/-- vdV Lemma 25.23, faithful scalar nondominated characterization.

Regularity, the efficient normal law, and asymptotic linearity appear as the
two sides of the equivalence; none is a field of pathwise differentiability.
Only tangent-cone data, pathwise differentiability, an EIF, and estimator
measurability are inputs. -/
theorem operational_efficiency_characterization_nondominated
    {T_n : ∀ n, (Fin n → Ω) → ℝ} {ψ : Measure Ω → ℝ}
    (C : NondominatedTangentCone P)
    -- USER-INPUT: pathwise differentiability and its efficient influence function;
    -- vdV Lemma 25.23.
    (hpd : NondominatedPathwiseDifferentiableAt P C ψ)
    {φ : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace C) hpd.derivative φ)
    -- LEAN-ONLY: measurability of each estimator.
    (hT : ∀ n, Measurable (T_n n)) :
    IsRegularAtND C T_n ψ
        (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) ↔
      AsymptoticallyLinearAt T_n P φ (ψ P) := by
  constructor
  · exact asymptoticallyLinear_of_regular_and_gaussianND C hpd hEIF hT
  · exact regular_and_gaussian_of_asymptoticallyLinearND C hpd hEIF hT

end AsymptoticStatistics.LowerBounds.OperationalEfficiencyCharacterizationNondominated
