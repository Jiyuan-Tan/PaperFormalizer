module
public import StatLean.TimeSeries.ForMathlib.Fourier.FejerKernel
public import StatLean.TimeSeries.ForMathlib.Fourier.MeasureFourierCoeff
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

@[expose] public section

/-!
# The Herglotz theorem on ℤ (FY Theorem 2.10, existence core)

**Herglotz/Bochner for ℤ**: a real sequence is even and positive semidefinite **iff** it
is the Fourier-coefficient sequence of a (negation-invariant) finite measure on the
circle `AddCircle (2π)`. This is the measure-theoretic core of FY Theorem 2.10
(Wiener–Khintchine): combined with FY Theorem 2.7 (`Process/Autocovariance.lean`) it
characterizes autocovariance functions of stationary time series; uniqueness of the
measure is `ext_of_measureFourierCoeff` (`MeasureFourierCoeff.lean`).

Proof route for existence (FY §2.7.4, self-contained): the Fejér densities
`fejerSum γ n ≥ 0` define measures `F_n` on the circle with trigonometric moments
`(1 − |j|/n) γ(j)` (FY eq. (2.71)) and total mass `γ(0)`; normalize, extract a weakly
convergent subsequence by compactness of `ProbabilityMeasure` on the compact circle
(pinned Prokhorov instance), and pass the moments to the limit
(`tendsto_measureFourierCoeff_of_tendsto`). The degenerate case `γ(0) = 0` forces
`γ ≡ 0` (`IsPosSemidefSeq.abs_le_of_even`) with `F = 0`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, Theorem 2.10
(p. 51) and §2.7.4 (pp. 80–81). (`FY §2.3.2 Thm 2.10; §2.7.4`.)

**Proof formalization notes.** FY states the result for the normalized ACF (`ρ`, a
probability distribution `F`); we state the unnormalized form (mass `γ(0)`), from which
the normalized version is scalar rescaling. The book's "symmetric distribution on
`[−π, π]`" is `NegInvariant` on the circle — symmetry of the constructed limit is
part of the statement here (glossed in the book; the Fejér densities are even).

**Bibliographic comments.** G. Herglotz, "Über Potenzreihen mit positivem, reellem Teil
im Einheitskreis", *Ber. Verh. Sächs. Akad. Wiss. Leipzig* **63** (1911), 501–511;
the ℝ-analogue is S. Bochner (1932). In time series the result enters through
A. Ya. Khinchin (1934) and H. Wold (1938); FY follow Brockwell & Davis (1991),
pp. 118–119.
-/

open MeasureTheory Filter
open scoped Real Topology NNReal ENNReal

namespace StatLean.TimeSeries

instance herglotzFactTwoPi : Fact (0 < 2 * π) := ⟨by positivity⟩

private lemma continuous_fejerSum_re (γ : ℤ → ℝ) (n : ℕ) :
    Continuous fun ω : ℝ => (fejerSum γ n ω).re := by
  simp only [fejerSum]
  fun_prop

/-- Density of the `n`-th Fejér measure, as an `ℝ≥0`-valued function of `ω`. -/
private noncomputable def fejerDensity (γ : ℤ → ℝ) (n : ℕ) (ω : ℝ) : ℝ≥0 :=
  Real.toNNReal (fejerSum γ n ω).re

private lemma measurable_fejerDensity (γ : ℤ → ℝ) (n : ℕ) :
    Measurable (fejerDensity γ n) :=
  continuous_real_toNNReal.measurable.comp (continuous_fejerSum_re γ n).measurable

private noncomputable def fejerMeasure (γ : ℤ → ℝ) (n : ℕ) : Measure (AddCircle (2 * π)) :=
  ((volume.restrict (Set.Ioc (-π) π)).withDensity
    (fun ω => (fejerDensity γ n ω : ℝ≥0∞))).map ((↑) : ℝ → AddCircle (2 * π))

private lemma fourier_coe_eq (j : ℤ) (ω : ℝ) :
    fourier (T := 2 * π) j (↑ω : AddCircle (2 * π))
      = Complex.exp (Complex.I * (ω : ℂ) * (j : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

private lemma measureFourierCoeff_fejerMeasure (γ : ℤ → ℝ) (h : IsPosSemidefSeq γ)
    (heven : ∀ k, γ (-k) = γ k) (n : ℕ) (j : ℤ) :
    measureFourierCoeff (fejerMeasure γ n) j
      = ∫ ω in (-π : ℝ)..π, fejerSum γ n ω * Complex.exp (Complex.I * (ω : ℂ) * (j : ℂ)) := by
  rw [measureFourierCoeff, fejerMeasure,
    integral_map AddCircle.measurable_mk'.aemeasurable
      ((map_continuous (fourier (T := 2 * π) j)).aestronglyMeasurable),
    integral_withDensity_eq_integral_smul (measurable_fejerDensity γ n),
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (-π : ℝ) ≤ π)]
  refine setIntegral_congr_fun measurableSet_Ioc fun ω _ => ?_
  rw [fourier_coe_eq, NNReal.smul_def, fejerDensity,
    Real.coe_toNNReal _ (fejerSum_re_nonneg γ h heven n ω)]
  have hz : ((fejerSum γ n ω).re : ℂ) = fejerSum γ n ω := by
    refine Complex.ext rfl ?_
    simp [fejerSum_im γ heven n ω]
  rw [← hz]
  exact Complex.real_smul

private lemma isFiniteMeasure_fejerMeasure (γ : ℤ → ℝ) (n : ℕ) :
    IsFiniteMeasure (fejerMeasure γ n) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -π) (b := π)).exists_bound_of_continuousOn
    (continuous_fejerSum_re γ n).continuousOn
  have hfin : IsFiniteMeasure ((volume.restrict (Set.Ioc (-π) π)).withDensity
      (fun ω => (fejerDensity γ n ω : ℝ≥0∞))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ ω in Set.Ioc (-π) π, (fejerDensity γ n ω : ℝ≥0∞)
        ≤ ∫⁻ _ω in Set.Ioc (-π) π, ENNReal.ofReal C := by
          refine setLIntegral_mono measurable_const fun ω hω => ?_
          rw [fejerDensity]
          refine ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) ?_)
          simpa [Real.norm_eq_abs] using hC ω (Set.Ioc_subset_Icc_self hω)
      _ = ENNReal.ofReal C * volume (Set.Ioc (-π) π) := setLIntegral_const _ _
      _ < ⊤ := by
          rw [Real.volume_Ioc]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  rw [fejerMeasure]
  exact Measure.isFiniteMeasure_map _ _

private lemma measureFourierCoeff_fejerMeasure_of_lt (γ : ℤ → ℝ) (h : IsPosSemidefSeq γ)
    (heven : ∀ k, γ (-k) = γ k) {n : ℕ} {j : ℤ} (hj : |j| < (n : ℤ)) :
    measureFourierCoeff (fejerMeasure γ n) j
      = (((((n : ℤ) - |j|) : ℤ) : ℂ) / (n : ℂ)) * (γ j : ℂ) := by
  rw [measureFourierCoeff_fejerMeasure γ h heven n j, integral_fejerSum_mul_exp_of_lt γ hj]

private lemma fejerMeasure_univ (γ : ℤ → ℝ) (h : IsPosSemidefSeq γ)
    (heven : ∀ k, γ (-k) = γ k) {n : ℕ} (hn : 0 < n) :
    (fejerMeasure γ n) Set.univ = ENNReal.ofReal (γ 0) := by
  haveI := isFiniteMeasure_fejerMeasure γ n
  have hzero : measureFourierCoeff (fejerMeasure γ n) 0 = (γ 0 : ℂ) := by
    rw [measureFourierCoeff_fejerMeasure_of_lt γ h heven (j := 0) (by simpa using hn)]
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp [div_self hnC]
  rw [measureFourierCoeff_zero] at hzero
  have : ((fejerMeasure γ n) Set.univ).toReal = γ 0 := by exact_mod_cast hzero
  rw [← this, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- `measureFourierCoeff` is scalar-linear in the measure. -/
private lemma measureFourierCoeff_smul (c : ℝ≥0∞) (F : Measure (AddCircle (2 * π))) (j : ℤ) :
    measureFourierCoeff (c • F) j = ((c.toReal : ℝ) : ℂ) * measureFourierCoeff F j := by
  rw [measureFourierCoeff, measureFourierCoeff, integral_smul_measure]
  exact Complex.real_smul

private lemma measureFourierCoeff_fejerProb (γ : ℤ → ℝ) (h : IsPosSemidefSeq γ)
    (heven : ∀ k, γ (-k) = γ k) (h0 : 0 < γ 0) {n : ℕ} {j : ℤ} (hj : |j| < (n : ℤ)) :
    measureFourierCoeff ((ENNReal.ofReal (γ 0))⁻¹ • fejerMeasure γ n) j
      = (((γ 0)⁻¹ * (1 - ((|j| : ℤ) : ℝ) / (n : ℝ)) * γ j : ℝ) : ℂ) := by
  have hn : (0 : ℤ) < (n : ℤ) := lt_of_le_of_lt (abs_nonneg j) hj
  have hnR : ((n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by exact_mod_cast hn.ne' : (n : ℕ) ≠ 0)
  have hnC : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by exact_mod_cast hn.ne' : (n : ℕ) ≠ 0)
  rw [measureFourierCoeff_smul, measureFourierCoeff_fejerMeasure_of_lt γ h heven hj,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal h0.le]
  have hg0 : ((γ 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
  obtain ⟨A, hA⟩ : ∃ A : ℤ, |j| = A := ⟨_, rfl⟩
  rw [hA]
  push_cast
  field_simp

private lemma measureFourierCoeff_map_neg (F : Measure (AddCircle (2 * π))) [IsFiniteMeasure F]
    (m : ℤ) :
    measureFourierCoeff (F.map (fun z => -z)) m = measureFourierCoeff F (-m) := by
  rw [measureFourierCoeff, measureFourierCoeff,
    integral_map measurable_neg.aemeasurable
      ((map_continuous (fourier (T := 2 * π) m)).aestronglyMeasurable)]
  have hpt : ∀ z : AddCircle (2 * π),
      fourier (T := 2 * π) (-m) z = fourier (T := 2 * π) m (-z) := by
    intro z
    rw [fourier_apply, fourier_apply, neg_zsmul, zsmul_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hpt z).symm)

/-- **Herglotz existence** (FY Theorem 2.10, "only if" core; proof route §2.7.4): an
even positive semidefinite sequence is the Fourier-coefficient sequence of a
negation-invariant finite measure on `AddCircle (2π)`. -/
theorem exists_measure_of_isPosSemidefSeq (γ : ℤ → ℝ)
    -- USER-INPUT: evenness of the sequence; FY §2.3.2 Thm 2.10
    (heven : ∀ k, γ (-k) = γ k)
    -- USER-INPUT: positive semidefiniteness, FY eq. (2.17); FY §2.3.2 Thm 2.10
    (hpsd : IsPosSemidefSeq γ) :
    ∃ F : Measure (AddCircle (2 * π)), IsFiniteMeasure F ∧ NegInvariant F ∧
      ∀ k : ℤ, measureFourierCoeff F k = (γ k : ℂ) := by
  rcases eq_or_lt_of_le hpsd.nonneg_zero with h0 | h0
  · -- degenerate case `γ 0 = 0`: `|γ k| ≤ γ 0 = 0` forces `γ ≡ 0`, take `F = 0`
    have hzero : ∀ k, γ k = 0 := by
      intro k
      have h1 := hpsd.abs_le_of_even heven k
      rw [← h0] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    refine ⟨0, inferInstance, by simp [NegInvariant], fun k => ?_⟩
    rw [measureFourierCoeff, integral_zero_measure, hzero k, Complex.ofReal_zero]
  · -- main case `0 < γ 0`
    have hne : ENNReal.ofReal (γ 0) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero]
      linarith
    have htop : ENNReal.ofReal (γ 0) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hg0C : ((γ 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
    -- the normalized Fejér measures are probability measures
    have hprob : ∀ m : ℕ, IsProbabilityMeasure
        ((ENNReal.ofReal (γ 0))⁻¹ • fejerMeasure γ (m + 1)) := by
      intro m
      refine ⟨?_⟩
      rw [Measure.smul_apply, smul_eq_mul, fejerMeasure_univ γ hpsd heven m.succ_pos,
        ENNReal.inv_mul_cancel hne htop]
    set Pn : ℕ → ProbabilityMeasure (AddCircle (2 * π)) :=
      fun m => ⟨(ENNReal.ofReal (γ 0))⁻¹ • fejerMeasure γ (m + 1), hprob m⟩ with hPndef
    have hPncoe : ∀ m : ℕ,
        ((Pn m : ProbabilityMeasure (AddCircle (2 * π))) : Measure (AddCircle (2 * π)))
          = (ENNReal.ofReal (γ 0))⁻¹ • fejerMeasure γ (m + 1) := fun _ => rfl
    -- compactness of the space of probability measures on the (compact, metrizable) circle
    haveI : SeqCompactSpace (ProbabilityMeasure (AddCircle (2 * π))) :=
      compactSpace_iff_seqCompactSpace.mp inferInstance
    obtain ⟨P, φ, hφ, hlim⟩ := SeqCompactSpace.tendsto_subseq Pn
    have hφtop : Filter.Tendsto (fun k => φ k + 1) atTop atTop :=
      Filter.tendsto_atTop_mono (fun k => Nat.le_succ (φ k)) hφ.tendsto_atTop
    -- the moments pass to the limit
    have hcoef : ∀ j : ℤ, measureFourierCoeff (P : Measure (AddCircle (2 * π))) j
        = ((γ j / γ 0 : ℝ) : ℂ) := by
      intro j
      have h1 := tendsto_measureFourierCoeff_of_tendsto hlim j
      have hev : (fun k => measureFourierCoeff ((Pn ∘ φ) k : Measure (AddCircle (2 * π))) j)
          =ᶠ[atTop] fun k =>
            (((γ 0)⁻¹ * (1 - ((|j| : ℤ) : ℝ) / ((φ k + 1 : ℕ) : ℝ)) * γ j : ℝ) : ℂ) := by
        filter_upwards [hφtop.eventually_ge_atTop (|j|.toNat + 1)] with k hk
        have hjk : |j| < ((φ k + 1 : ℕ) : ℤ) := by
          have htn : (|j|.toNat : ℤ) = |j| := Int.toNat_of_nonneg (abs_nonneg j)
          omega
        rw [Function.comp_apply, hPncoe, measureFourierCoeff_fejerProb γ hpsd heven h0 hjk]
      have h2 : Filter.Tendsto (fun k : ℕ => ((|j| : ℤ) : ℝ) / ((φ k + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
        (tendsto_const_div_atTop_nhds_zero_nat ((|j| : ℤ) : ℝ)).comp hφtop
      have h3 : Filter.Tendsto
          (fun k => (γ 0)⁻¹ * (1 - ((|j| : ℤ) : ℝ) / ((φ k + 1 : ℕ) : ℝ)) * γ j) atTop
          (𝓝 (γ j / γ 0)) := by
        have hlim2 : Filter.Tendsto
            (fun k => (γ 0)⁻¹ * (1 - ((|j| : ℤ) : ℝ) / ((φ k + 1 : ℕ) : ℝ)) * γ j) atTop
            (𝓝 ((γ 0)⁻¹ * (1 - 0) * γ j)) :=
          Filter.Tendsto.mul_const _ (Filter.Tendsto.const_mul _ (tendsto_const_nhds.sub h2))
        have hval : (γ 0)⁻¹ * (1 - 0) * γ j = γ j / γ 0 := by
          rw [sub_zero, mul_one, div_eq_inv_mul]
        rwa [hval] at hlim2
      exact tendsto_nhds_unique (h1.congr' hev) ((Complex.continuous_ofReal.tendsto _).comp h3)
    -- rescale by the mass `γ 0`
    have hFcoef : ∀ k : ℤ,
        measureFourierCoeff (ENNReal.ofReal (γ 0) • (P : Measure (AddCircle (2 * π)))) k
          = (γ k : ℂ) := by
      intro k
      rw [measureFourierCoeff_smul, hcoef k, ENNReal.toReal_ofReal h0.le]
      push_cast
      field_simp
    haveI hFfin : IsFiniteMeasure (ENNReal.ofReal (γ 0) • (P : Measure (AddCircle (2 * π)))) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]; exact htop.lt_top⟩
    refine ⟨_, hFfin, ?_, hFcoef⟩
    -- negation invariance from evenness of the coefficients (uniqueness)
    haveI := Measure.isFiniteMeasure_map
      (ENNReal.ofReal (γ 0) • (P : Measure (AddCircle (2 * π)))) (fun z => -z)
    refine ext_of_measureFourierCoeff _ _ fun m => ?_
    rw [measureFourierCoeff_map_neg, hFcoef (-m), hFcoef m, heven m]

/-- **Herglotz converse** (FY Theorem 2.10, "if" core): the real parts of the Fourier
coefficients of a finite measure form a positive semidefinite sequence
(`Σᵢⱼ aᵢaⱼ ∫ e^{i(tᵢ−tⱼ)z} dF = ∫ |Σᵢ aᵢ e^{itᵢz}|² dF ≥ 0`). -/
theorem isPosSemidefSeq_measureFourierCoeff (F : Measure (AddCircle (2 * π)))
    [IsFiniteMeasure F] :
    IsPosSemidefSeq fun k => (measureFourierCoeff F k).re := by
  haveI : Fact (0 < 2 * π) := ⟨by positivity⟩
  intro n t a
  have hint : ∀ m : ℤ, Integrable (fun z => fourier (T := 2 * π) m z) F := fun m =>
    (BoundedContinuousFunction.mkOfCompact (fourier (T := 2 * π) m)).integrable F
  -- pointwise: the Hermitian form of the characters is the squared modulus of `Σ aᵢ e^{itᵢz}`
  have hkey : ∀ z : AddCircle (2 * π),
      ∑ i, ∑ j, (((a i * a j : ℝ)) : ℂ) * fourier (T := 2 * π) (t i - t j) z
        = ((‖∑ i, ((a i : ℝ) : ℂ) * fourier (T := 2 * π) (t i) z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← fourier_neg, sub_eq_add_neg, fourier_add]
    push_cast
    ring
  -- the real quadratic form is the real part of the complex one
  have hre : ∑ i, ∑ j, a i * a j * (measureFourierCoeff F (t i - t j)).re
      = (∑ i, ∑ j, (((a i * a j : ℝ)) : ℂ) * measureFourierCoeff F (t i - t j)).re := by
    simp only [Complex.re_sum, Complex.re_ofReal_mul]
  have h2 : ∀ i j : Fin n, (((a i * a j : ℝ)) : ℂ) * measureFourierCoeff F (t i - t j)
      = ∫ z, (((a i * a j : ℝ)) : ℂ) * fourier (T := 2 * π) (t i - t j) z ∂F := by
    intro i j
    rw [measureFourierCoeff]
    exact (integral_const_mul _ _).symm
  -- swap the finite sum with the integral (characters are bounded continuous)
  have h3 : (∑ i, ∑ j, (((a i * a j : ℝ)) : ℂ) * measureFourierCoeff F (t i - t j))
      = ∫ z, ∑ i, ∑ j, (((a i * a j : ℝ)) : ℂ) * fourier (T := 2 * π) (t i - t j) z ∂F := by
    rw [integral_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => (hint (t i - t j)).const_mul _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => (hint (t i - t j)).const_mul _)]
    exact Finset.sum_congr rfl fun j _ => h2 i j
  rw [hre, h3, integral_congr_ae (Filter.Eventually.of_forall hkey), integral_complex_ofReal,
    Complex.ofReal_re]
  exact integral_nonneg fun z => by positivity

/-- Evenness of the coefficient sequence of a negation-invariant finite measure
(companion to the converse: together they say the coefficient sequence of a
`NegInvariant` finite measure is even and positive semidefinite). -/
theorem measureFourierCoeff_re_even (F : Measure (AddCircle (2 * π))) [IsFiniteMeasure F]
    (hF : NegInvariant F) (k : ℤ) :
    (measureFourierCoeff F (-k)).re = (measureFourierCoeff F k).re := by
  rw [measureFourierCoeff_neg F hF k]

end StatLean.TimeSeries
