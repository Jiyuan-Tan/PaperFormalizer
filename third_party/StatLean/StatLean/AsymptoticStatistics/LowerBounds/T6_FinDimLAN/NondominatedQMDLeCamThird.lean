module
public import StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLAN
public import StatLean.AsymptoticStatistics.Probability.ScoreCLT
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw
public import StatLean.AsymptoticStatistics.ForMathlib.Slutsky
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

/-! # Le Cam theory for nondominated QMD paths -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.NondominatedQMDPath
open AsymptoticStatistics.Core.NondominatedQMDPath.NondominatedQMDPath
open AsymptoticStatistics.Contiguity

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Normalized empirical sum; the empty sum is zero. -/
noncomputable def normalizedScoreSum
    (u : ↥(L2ZeroMean P)) (n : ℕ) (X : Fin n → Ω) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ i : Fin n, (u : Ω → ℝ) (X i)

/-- Possibly singular two-coordinate Gram Gaussian. -/
noncomputable def scorePairGaussian
    (γ : NondominatedQMDPath P) (u : ↥(L2ZeroMean P)) : Measure (ℝ × ℝ) :=
  let v : Fin 2 → ↥(L2ZeroMean P) := ![u, γ.score]
  (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (Matrix.gram ℝ v)).map
    (fun z => (z 0, z 1))

private lemma integral_l2ZeroMean_eq_zero (u : ↥(L2ZeroMean P)) :
    ∫ x, (u : Ω → ℝ) x ∂P = 0 := by
  have hu : integralL2 P (u : Lp ℝ 2 P) = 0 := by
    have hmem : (u : Lp ℝ 2 P) ∈ L2ZeroMean P := u.2
    change (u : Lp ℝ 2 P) ∈ LinearMap.ker (integralL2 P).toLinearMap at hmem
    rw [LinearMap.mem_ker] at hmem
    exact hmem
  change ⟪oneL2 P, (u : Lp ℝ 2 P)⟫_ℝ = 0 at hu
  rw [MeasureTheory.L2.inner_def] at hu
  have hone : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))
  rw [integral_congr_ae (hone.mono fun x hx => by
    change (u : Ω → ℝ) x * (oneL2 P : Ω → ℝ) x = (u : Ω → ℝ) x
    rw [hx, mul_one])] at hu
  exact hu

private lemma integral_l2ZeroMean_mul (u v : ↥(L2ZeroMean P)) :
    ∫ x, (u : Ω → ℝ) x * (v : Ω → ℝ) x ∂P = ⟪u, v⟫_ℝ := by
  change ∫ x, (u : Ω → ℝ) x * (v : Ω → ℝ) x ∂P =
    ⟪(u : Lp ℝ 2 P), (v : Lp ℝ 2 P)⟫_ℝ
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  change (u : Ω → ℝ) x * (v : Ω → ℝ) x =
    (v : Ω → ℝ) x * (u : Ω → ℝ) x
  ring_nf

private noncomputable def scoreVector
    (v : Fin 2 → ↥(L2ZeroMean P)) (x : Ω) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i => ((v i : Lp ℝ 2 P) : Ω → ℝ) x)

private lemma measurable_scoreVector (v : Fin 2 → ↥(L2ZeroMean P)) :
    Measurable (scoreVector (P := P) v) := by
  unfold scoreVector
  refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp ?_
  exact measurable_pi_lambda _ fun i => (Lp.stronglyMeasurable (v i : Lp ℝ 2 P)).measurable

private lemma inner_scoreVector (v : Fin 2 → ↥(L2ZeroMean P))
    (a : EuclideanSpace ℝ (Fin 2)) (x : Ω) :
    ⟪a, scoreVector v x⟫_ℝ = ∑ i, a i * (v i : Ω → ℝ) x := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (v i : Ω → ℝ) x * a i = a i * (v i : Ω → ℝ) x
  ring_nf

private noncomputable def actualLogLikelihood
    (γ : NondominatedQMDPath P) (a : ℝ) (n : ℕ) (X : Fin n → Ω) : ℝ :=
  Real.log (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal

private lemma measurable_acProductLikelihood_toReal
    (γ : NondominatedQMDPath P) (t : ℝ) (n : ℕ) :
    Measurable (fun X : Fin n → Ω => (γ.acProductLikelihood t n X).toReal) := by
  unfold acProductLikelihood
  exact (Finset.measurable_prod Finset.univ fun i _ =>
    (Measure.measurable_rnDeriv (γ.curve t) P).comp
      (measurable_pi_apply i)).ennreal_toReal

private lemma measurable_actualLogLikelihood
    (γ : NondominatedQMDPath P) (a : ℝ) (n : ℕ) :
    Measurable (actualLogLikelihood γ a n) := by
  exact (measurable_acProductLikelihood_toReal γ
    (a * (Real.sqrt n)⁻¹) n).log

private lemma acProductLikelihood_toReal_zero_mass_le
    (γ : NondominatedQMDPath P) (t : ℝ) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => P))
        {X | (γ.acProductLikelihood t n X).toReal = 0} ≤
      (n : ℝ≥0∞) * γ.baseZeroLikelihoodMass t := by
  classical
  let Z : Set Ω := {x | ((γ.curve t).rnDeriv P x).toReal = 0}
  let Zn : Set (Fin n → Ω) := {X | (γ.acProductLikelihood t n X).toReal = 0}
  have hsubset : Zn ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin n)),
      (fun X : Fin n → Ω => X i) ⁻¹' Z := by
    intro X hX
    simp only [Set.mem_iUnion, Finset.mem_univ]
    by_contra hall
    push Not at hall
    have hfactor : ∀ i : Fin n,
        ((γ.curve t).rnDeriv P (X i)).toReal ≠ 0 := by
      intro i hi
      exact hall i trivial
        (by simpa only [Z, Set.mem_preimage, Set.mem_setOf_eq] using hi)
    have hprod : (γ.acProductLikelihood t n X).toReal ≠ 0 := by
      rw [ENNReal.toReal_ne_zero]
      constructor
      · unfold acProductLikelihood
        rw [Finset.prod_ne_zero_iff]
        intro i _
        exact (ENNReal.toReal_ne_zero.mp (hfactor i)).1
      · unfold acProductLikelihood
        exact ENNReal.prod_ne_top fun i _ =>
          (ENNReal.toReal_ne_zero.mp (hfactor i)).2
    exact hprod hX
  have hZmeas : MeasurableSet Z := by
    exact (measurableSet_singleton 0).preimage
      (Measure.measurable_rnDeriv (γ.curve t) P).ennreal_toReal
  have hcoord : ∀ i : Fin n,
      (Measure.pi (fun _ : Fin n => P)) ((fun X : Fin n → Ω => X i) ⁻¹' Z) =
        γ.baseZeroLikelihoodMass t := by
    intro i
    calc
      (Measure.pi (fun _ : Fin n => P)) ((fun X : Fin n → Ω => X i) ⁻¹' Z) =
          ((Measure.pi (fun _ : Fin n => P)).map (fun X => X i)) Z := by
            rw [Measure.map_apply (measurable_pi_apply i) hZmeas]
      _ = P Z := by rw [Measure.pi_map_eval]; simp
      _ = γ.baseZeroLikelihoodMass t := by rfl
  calc
    (Measure.pi (fun _ : Fin n => P))
          {X | (γ.acProductLikelihood t n X).toReal = 0} =
        (Measure.pi (fun _ : Fin n => P)) Zn := rfl
    _ ≤ (Measure.pi (fun _ : Fin n => P))
          (⋃ i ∈ (Finset.univ : Finset (Fin n)),
            (fun X : Fin n → Ω => X i) ⁻¹' Z) := measure_mono hsubset
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)),
          (Measure.pi (fun _ : Fin n => P))
            ((fun X : Fin n → Ω => X i) ⁻¹' Z) :=
      measure_biUnion_finset_le Finset.univ _
    _ = (n : ℝ≥0∞) * γ.baseZeroLikelihoodMass t := by
      simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

private lemma integrable_exp_actualLogLikelihood
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    Integrable (fun X => Real.exp (actualLogLikelihood γ a n X))
      (Measure.pi (fun _ : Fin n => P)) := by
  let t := a * (Real.sqrt n)⁻¹
  have ht : 0 ≤ t := mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hL := (γ.integrable_acProductLikelihood_and_integral t ht n).1
  have hmajor : Integrable
      (fun X : Fin n → Ω =>
        (γ.acProductLikelihood t n X).toReal + 1)
      (Measure.pi (fun _ : Fin n => P)) := hL.add (integrable_const 1)
  refine hmajor.mono' ((measurable_actualLogLikelihood γ a n).exp.aestronglyMeasurable) ?_
  filter_upwards with X
  by_cases hzero : (γ.acProductLikelihood t n X).toReal = 0
  · norm_num [actualLogLikelihood, t, hzero]
  · rw [show actualLogLikelihood γ a n X =
        Real.log (γ.acProductLikelihood t n X).toReal by rfl,
      Real.exp_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero))]
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact le_add_of_nonneg_right zero_le_one

private lemma integral_exp_actualLogLikelihood_sub_likelihood
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (∫ X, Real.exp (actualLogLikelihood γ a n X)
        ∂(Measure.pi (fun _ : Fin n => P))) -
      ∫ X, (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal
        ∂(Measure.pi (fun _ : Fin n => P)) =
      ((Measure.pi (fun _ : Fin n => P))
        {X | (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal = 0}).toReal := by
  let t := a * (Real.sqrt n)⁻¹
  let Z : Set (Fin n → Ω) :=
    {X | (γ.acProductLikelihood t n X).toReal = 0}
  have ht : 0 ≤ t := mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hexp := integrable_exp_actualLogLikelihood γ a ha n
  have hL := (γ.integrable_acProductLikelihood_and_integral t ht n).1
  have hZmeas : MeasurableSet Z :=
    (measurableSet_singleton 0).preimage
      (measurable_acProductLikelihood_toReal γ t n)
  rw [← MeasureTheory.integral_sub hexp hL]
  have hpw : (fun X : Fin n → Ω =>
      Real.exp (actualLogLikelihood γ a n X) -
        (γ.acProductLikelihood t n X).toReal) = Z.indicator (fun _ => (1 : ℝ)) := by
    funext X
    by_cases hzero : (γ.acProductLikelihood t n X).toReal = 0
    · simp [Z, hzero, actualLogLikelihood, t]
    · simp only [Z, Set.indicator_of_notMem, Set.mem_setOf_eq, hzero, not_false_eq_true]
      rw [show actualLogLikelihood γ a n X =
          Real.log (γ.acProductLikelihood t n X).toReal by rfl,
        Real.exp_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero))]
      simp
  rw [hpw, MeasureTheory.integral_indicator hZmeas]
  simp only [integral_const, smul_eq_mul, mul_one,
    Measure.real_def, Z, t]
  rw [Measure.restrict_apply_univ]

private lemma integral_acProductLikelihood_localScale_tendsto_one
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n =>
      ∫ X, (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal
        ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 1) := by
  have hint : ∀ n,
      ∫ X, (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal
          ∂(Measure.pi (fun _ : Fin n => P)) =
        (1 - (γ.singularMass (a * (Real.sqrt n)⁻¹)).toReal) ^ n := by
    intro n
    exact (γ.integrable_acProductLikelihood_and_integral _
      (mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _))) n).2
  have hs := γ.singular_mass_localScale_tendsto a ha
  have hsreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hs
  have hsreal' : Tendsto (fun n : ℕ =>
      ((n : ℝ≥0∞) * γ.singularMass (a * (Real.sqrt n)⁻¹)).toReal)
      atTop (nhds 0) := by simpa only [Function.comp_apply, ENNReal.toReal_zero] using! hsreal
  have hndiff : Tendsto (fun n : ℕ => (n : ℝ) *
      ((1 - (γ.singularMass (a * (Real.sqrt n)⁻¹)).toReal) - 1))
      atTop (nhds 0) := by
    convert hsreal'.neg using 1
    · funext n
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
      ring_nf
    · simp
  have hpow := Real.tendsto_one_add_pow_exp_of_tendsto hndiff
  simp only [Real.exp_zero] at hpow
  refine hpow.congr' ?_
  filter_upwards with n
  rw [hint n]
  congr 1
  ring_nf

private lemma integral_exp_actualLogLikelihood_tendsto_one
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n => ∫ X, Real.exp (actualLogLikelihood γ a n X)
      ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 1) := by
  have hzero := γ.base_zeroLikelihood_localScale_tendsto a ha
  have hzero_real := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hzero
  have hbad : Tendsto (fun n =>
      ((Measure.pi (fun _ : Fin n => P))
        {X | (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal = 0}).toReal)
      atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hzero_real (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_
    filter_upwards with n
    exact ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n)
        (measure_ne_top P _))
      (acProductLikelihood_toReal_zero_mass_le γ _ n)
  have hsum := (integral_acProductLikelihood_localScale_tendsto_one γ a ha).add hbad
  simpa only [add_zero] using hsum.congr' (Filter.Eventually.of_forall fun n => by
    rw [← integral_exp_actualLogLikelihood_sub_likelihood γ a ha n]
    ring_nf)

private lemma actualLog_integral_comparison_bound
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a)
    (Y : ∀ n, (Fin n → Ω) → ℝ) (hY : ∀ n, Measurable (Y n))
    (f : BoundedContinuousFunction ℝ ℝ) (n : ℕ) :
    |∫ X, f (Y n X) ∂(Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))) -
      ∫ X, f (Y n X) * Real.exp (actualLogLikelihood γ a n X)
        ∂(Measure.pi (fun _ : Fin n => P))| ≤
      ‖f‖ * ((((n : ℝ≥0∞) *
          γ.singularMass (a * (Real.sqrt n)⁻¹)).toReal) +
        (((n : ℝ≥0∞) *
          γ.baseZeroLikelihoodMass (a * (Real.sqrt n)⁻¹)).toReal)) := by
  classical
  let t := a * (Real.sqrt n)⁻¹
  have ht : 0 ≤ t := mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _))
  letI : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  let Q : Measure Ω := γ.curve t
  let A : Measure Ω := γ.acPart t
  let ν : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => Q)
  let ρ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => A)
  let Pn : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => P)
  let L : (Fin n → Ω) → ℝ≥0∞ := γ.acProductLikelihood t n
  let F : (Fin n → Ω) → ℝ := fun X => f (Y n X)
  have hAQ : A ≤ Q := by
    simpa only [A, Q, acPart] using
      Measure.withDensity_rnDeriv_le (γ.curve t) P
  letI : IsFiniteMeasure A := isFiniteMeasure_of_le Q hAQ
  have hAac : A ≪ Q := hAQ.absolutelyContinuous
  have hρν : ρ ≤ ν := by
    let D : (Fin n → Ω) → ℝ≥0∞ :=
      fun X => ∏ i : Fin n, A.rnDeriv Q (X i)
    have hcoord : ∀ i : Fin n, A.rnDeriv Q ≤ᵐ[Q] 1 :=
      fun _ => Measure.rnDeriv_le_one_of_le hAQ
    have hall : (fun X : Fin n → Ω => fun i : Fin n => A.rnDeriv Q (X i))
        ≤ᵐ[ν] (fun _ => fun _ : Fin n => (1 : ℝ≥0∞)) := by
      simpa only [ν] using! Measure.ae_le_pi hcoord
    have hDle : D ≤ᵐ[ν] 1 := by
      filter_upwards [hall] with X hX
      exact Finset.prod_le_one (fun _ _ => zero_le)
        (fun i _ => hX i)
    have htilt : ν.withDensity D = ρ := by
      have hcoordtilt : Q.withDensity (A.rnDeriv Q) = A :=
        Measure.withDensity_rnDeriv_eq A Q hAac
      calc
        ν.withDensity D =
            Measure.pi (fun _ : Fin n => Q.withDensity (A.rnDeriv Q)) := by
          simpa only [ν, D] using MeasureTheory.pi_withDensity_prod
            (fun _ : Fin n => Measure.measurable_rnDeriv A Q)
        _ = ρ := by simp only [hcoordtilt, ρ]
    rw [← htilt]
    simpa using withDensity_mono hDle
  let R : Measure (Fin n → Ω) := ν - ρ
  have hRρ : R + ρ = ν := Measure.sub_add_cancel_of_le hρν
  have hFmeas : Measurable F := f.continuous.measurable.comp (hY n)
  have hFν : Integrable F ν := by
    refine Integrable.of_bound hFmeas.aestronglyMeasurable ‖f‖ ?_
    exact Filter.Eventually.of_forall fun X => f.norm_coe_le_norm (Y n X)
  have hFρ : Integrable F ρ := hFν.mono_measure hρν
  have hRν : R ≤ ν := Measure.sub_le
  have hFR : Integrable F R := hFν.mono_measure hRν
  have hfull : ∫ X, F X ∂ν = (∫ X, F X ∂R) + ∫ X, F X ∂ρ := by
    rw [← hRρ, integral_add_measure hFR hFρ]
  have hρbase : ρ = Pn.withDensity L := by
    simpa only [ρ, Pn, L, A] using
      γ.pi_acPart_eq_withDensity_acProductLikelihood t ht n
  have hLmeas : Measurable L := by
    dsimp only [L, acProductLikelihood]
    exact Finset.measurable_prod _ fun i _ =>
      (Measure.measurable_rnDeriv (γ.curve t) P).comp
        (measurable_pi_apply i)
  have hLfin : ∀ᵐ X ∂Pn, L X < ⊤ := by
    have hcoordfin : ∀ i : Fin n,
        (fun _ : Ω => True) ≤ᵐ[P]
          (fun ω => (γ.curve t).rnDeriv P ω ≠ ⊤) := by
      intro i
      filter_upwards [Measure.rnDeriv_ne_top (γ.curve t) P] with ω hω
      exact fun _ => hω
    have hall : (fun X : Fin n → Ω => fun _ : Fin n => True)
        ≤ᵐ[Pn] (fun X i => (γ.curve t).rnDeriv P (X i) ≠ ⊤) := by
      simpa only [Pn] using Measure.ae_le_pi hcoordfin
    filter_upwards [hall] with X hX
    exact lt_top_iff_ne_top.mpr (by
      dsimp only [L, acProductLikelihood]
      exact ENNReal.prod_ne_top fun i _ => hX i trivial)
  have hweighted : ∫ X, F X * (L X).toReal ∂Pn = ∫ X, F X ∂ρ := by
    rw [hρbase,
      integral_withDensity_eq_integral_toReal_smul hLmeas hLfin F]
    apply integral_congr_ae
    filter_upwards with X
    simp only [smul_eq_mul, mul_comm]
  have hdiff : (∫ X, F X ∂ν) - ∫ X, F X * (L X).toReal ∂Pn =
      ∫ X, F X ∂R := by rw [hweighted, hfull]; ring_nf
  have hboundR : |∫ X, F X ∂R| ≤ ‖f‖ * R.real Set.univ := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_of_norm_le_const
        (μ := R) (f := F) (C := ‖f‖)
        (Filter.Eventually.of_forall fun X => f.norm_coe_le_norm (Y n X)))
  have hsfin : γ.singularMass t ≠ ⊤ := ne_top_of_le_ne_top
    (measure_ne_top (γ.curve t) _)
    (Measure.singularPart_le (γ.curve t) P Set.univ)
  have hsle : (γ.singularMass t).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    apply (ENNReal.toReal_le_toReal hsfin ENNReal.one_ne_top).2
    exact (Measure.singularPart_le (γ.curve t) P Set.univ).trans_eq measure_univ
  have hA_mass : (A Set.univ).toReal = 1 - (γ.singularMass t).toReal := by
    have hdec := γ.curve_eq_singularPart_add_acPart t ht
    have happ := congrArg (fun M : Measure Ω => M Set.univ) hdec
    have hAfin : A Set.univ ≠ ⊤ := measure_ne_top _ _
    have happ' : (1 : ℝ≥0∞) = γ.singularMass t + A Set.univ := by
      simpa only [Measure.add_apply, measure_univ, singularMass, singularPart,
        acPart, A] using happ
    have hreal := congrArg ENNReal.toReal happ'
    rw [ENNReal.toReal_one, ENNReal.toReal_add hsfin hAfin] at hreal
    linarith
  have hρ_mass : ρ.real Set.univ =
      (1 - (γ.singularMass t).toReal) ^ n := by
    simp only [ρ, measureReal_def, Measure.pi_univ, Finset.prod_const,
      ENNReal.toReal_pow, hA_mass]
    rw [Finset.card_univ, Fintype.card_fin]
  have hR_mass : R.real Set.univ =
      1 - (1 - (γ.singularMass t).toReal) ^ n := by
    change ((ν - ρ) Set.univ).toReal = _
    rw [Measure.sub_apply MeasurableSet.univ hρν,
      ENNReal.toReal_sub_of_le (hρν Set.univ) (measure_ne_top ν Set.univ)]
    have hρ_mass' : (ρ Set.univ).toReal =
        (1 - (γ.singularMass t).toReal) ^ n := by
      simpa only [measureReal_def] using hρ_mass
    rw [measure_univ, ENNReal.toReal_one, hρ_mass']
  have hmissing : R.real Set.univ ≤
      ((n : ℝ≥0∞) * γ.singularMass t).toReal := by
    rw [hR_mass, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    have hsnonneg : 0 ≤ (γ.singularMass t).toReal := ENNReal.toReal_nonneg
    simpa only [sub_sub_cancel] using
      (AsymptoticStatistics.ForMathlib.HellingerProduct.one_sub_pow_le_nsmul_one_sub
        (x := 1 - (γ.singularMass t).toReal)
        (by linarith [hsle]) (by linarith [hsnonneg]) n)
  have hactual : |∫ X, F X ∂ν - ∫ X, F X * (L X).toReal ∂Pn| ≤
      ‖f‖ * (((n : ℝ≥0∞) * γ.singularMass t).toReal) := by
    rw [hdiff]
    exact hboundR.trans (mul_le_mul_of_nonneg_left hmissing (norm_nonneg f))
  have hLint := (γ.integrable_acProductLikelihood_and_integral t ht n).1
  have hFL : Integrable (fun X => F X * (L X).toReal) Pn :=
    hLint.bdd_mul hFmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => f.norm_coe_le_norm (Y n X))
  have hexp := integrable_exp_actualLogLikelihood γ a ha n
  have hFexp : Integrable (fun X => F X * Real.exp (actualLogLikelihood γ a n X)) Pn :=
    hexp.bdd_mul hFmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => f.norm_coe_le_norm (Y n X))
  let Z : Set (Fin n → Ω) := {X | (L X).toReal = 0}
  have hZmeas : MeasurableSet Z :=
    (measurableSet_singleton 0).preimage hLmeas.ennreal_toReal
  have hpw : (fun X => F X * Real.exp (actualLogLikelihood γ a n X) -
      F X * (L X).toReal) = Z.indicator F := by
    funext X
    by_cases hzero : (L X).toReal = 0
    · simp [Z, hzero, actualLogLikelihood, L, t]
    · simp only [Z, Set.indicator_of_notMem, Set.mem_setOf_eq, hzero, not_false_eq_true]
      rw [show actualLogLikelihood γ a n X = Real.log (L X).toReal by rfl,
        Real.exp_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero))]
      ring_nf
  have hexp_actual : |∫ X, F X * Real.exp (actualLogLikelihood γ a n X) ∂Pn -
      ∫ X, F X * (L X).toReal ∂Pn| ≤
      ‖f‖ * (((n : ℝ≥0∞) * γ.baseZeroLikelihoodMass t).toReal) := by
    rw [← MeasureTheory.integral_sub hFexp hFL, hpw]
    rw [MeasureTheory.integral_indicator hZmeas]
    have hset : |∫ X in Z, F X ∂Pn| ≤ ‖f‖ * (Pn Z).toReal := by
      simpa only [Real.norm_eq_abs, measureReal_def] using
        (MeasureTheory.norm_setIntegral_le_of_norm_le_const
          (μ := Pn) (f := F) (C := ‖f‖) (measure_lt_top Pn Z)
          (fun X _ => f.norm_coe_le_norm (Y n X)))
    refine hset.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg f))
    exact ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (measure_ne_top P _))
      (acProductLikelihood_toReal_zero_mass_le γ t n)
  change |∫ X, F X ∂ν -
      ∫ X, F X * Real.exp (actualLogLikelihood γ a n X) ∂Pn| ≤ _
  calc
    |∫ X, F X ∂ν - ∫ X, F X * Real.exp (actualLogLikelihood γ a n X) ∂Pn| ≤
        |∫ X, F X ∂ν - ∫ X, F X * (L X).toReal ∂Pn| +
          |∫ X, F X * Real.exp (actualLogLikelihood γ a n X) ∂Pn -
            ∫ X, F X * (L X).toReal ∂Pn| := by
      rw [abs_sub_comm (∫ X, F X * Real.exp (actualLogLikelihood γ a n X) ∂Pn)]
      exact abs_sub_le _ _ _
    _ ≤ ‖f‖ * (((n : ℝ≥0∞) * γ.singularMass t).toReal) +
        ‖f‖ * (((n : ℝ≥0∞) * γ.baseZeroLikelihoodMass t).toReal) :=
      add_le_add hactual hexp_actual
    _ = _ := by rw [mul_add]

private lemma actualLog_integral_comparison
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a)
    (Y : ∀ n, (Fin n → Ω) → ℝ) (hY : ∀ n, Measurable (Y n)) :
    ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (nhds 0) ∧
      ∀ (f : BoundedContinuousFunction ℝ ℝ) (n : ℕ),
        |∫ X, f (Y n X) ∂(Measure.pi (fun _ : Fin n =>
              γ.curve (a * (Real.sqrt n)⁻¹))) -
          ∫ X, f (Y n X) * Real.exp (actualLogLikelihood γ a n X)
            ∂(Measure.pi (fun _ : Fin n => P))| ≤ ‖f‖ * ρ n := by
  let ρ : ℕ → ℝ := fun n =>
    (((n : ℝ≥0∞) * γ.singularMass (a * (Real.sqrt n)⁻¹)).toReal) +
      (((n : ℝ≥0∞) * γ.baseZeroLikelihoodMass
        (a * (Real.sqrt n)⁻¹)).toReal)
  refine ⟨ρ, ?_, fun f n => actualLog_integral_comparison_bound γ a ha Y hY f n⟩
  have hs := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (γ.singular_mass_localScale_tendsto a ha)
  have hz := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (γ.base_zeroLikelihood_localScale_tendsto a ha)
  simpa only [ρ, Function.comp_apply, ENNReal.toReal_zero, zero_add] using hs.add hz

private lemma measurable_normalizedScoreSum
    (u : ↥(L2ZeroMean P)) (n : ℕ) :
    Measurable (normalizedScoreSum u n) := by
  unfold normalizedScoreSum
  exact Measurable.const_mul
    (Finset.measurable_sum _ fun i _ =>
      (Lp.stronglyMeasurable (u : Lp ℝ 2 P)).measurable.comp
        (measurable_pi_apply i)) _

private lemma scorePairGaussian_snd
    (γ : NondominatedQMDPath P) (u : ↥(L2ZeroMean P)) :
    (scorePairGaussian γ u).map Prod.snd =
      gaussianReal 0 ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩ := by
  classical
  let v : Fin 2 → ↥(L2ZeroMean P) := ![u, γ.score]
  let e : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]
  have he : (fun z : EuclideanSpace ℝ (Fin 2) => z 1) =
      fun z => ⟪e, z⟫_ℝ := by
    funext z
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    dsimp [e]
    change z 1 = z 0 * 0 + z 1 * 1
    ring_nf
  rw [scorePairGaussian, Measure.map_map measurable_snd (by fun_prop)]
  change (multivariateGaussian 0 (Matrix.gram ℝ v)).map
    (fun z : EuclideanSpace ℝ (Fin 2) => z 1) = _
  rw [he, ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal e
    (Matrix.posSemidef_gram ℝ v)]
  congr 2
  apply NNReal.eq
  have hq : 0 ≤ e.ofLp ⬝ᵥ (Matrix.gram ℝ v).mulVec e.ofLp := by
    simpa using (Matrix.posSemidef_gram ℝ v).re_dotProduct_nonneg e.ofLp
  rw [Real.coe_toNNReal _ hq]
  change e.ofLp ⬝ᵥ (Matrix.gram ℝ v).mulVec e.ofLp = ‖γ.score‖ ^ 2
  simp [e, dotProduct, Matrix.mulVec, Matrix.gram_apply, v, Fin.sum_univ_two]

private lemma scorePairGaussian_tilt_fst
    (γ : NondominatedQMDPath P) (a : ℝ) (u : ↥(L2ZeroMean P)) :
    ((scorePairGaussian γ u).withDensity (fun q => ENNReal.ofReal (Real.exp
      (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)))).map Prod.fst =
    gaussianReal (a * ⟪u, γ.score⟫_ℝ) ⟨‖u‖ ^ 2, sq_nonneg _⟩ := by
  classical
  let v : Fin 2 → ↥(L2ZeroMean P) := ![u, γ.score]
  let S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.gram ℝ v
  let coord : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun z => (z 0, z 1)
  let h : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, a]
  have hS : S.PosSemidef := Matrix.posSemidef_gram ℝ v
  have hcoord : Measurable coord := by fun_prop
  have hdens : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp
      (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2))) := by fun_prop
  rw [scorePairGaussian]
  change (((multivariateGaussian 0 S).map coord).withDensity _).map Prod.fst = _
  rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
    _ coord hcoord _ hdens]
  rw [Measure.map_map measurable_fst hcoord]
  have hdensity : ((fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp
      (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2))) ∘ coord) =
      fun z : EuclideanSpace ℝ (Fin 2) => ENNReal.ofReal (Real.exp
        (⟪h, z⟫_ℝ - (h.ofLp ⬝ᵥ S.mulVec h.ofLp) / 2)) := by
    funext z
    have hi : ⟪h, z⟫_ℝ = a * z 1 := by
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      dsimp [h]
      change z 0 * 0 + z 1 * a = a * z 1
      ring_nf
    have hq : h.ofLp ⬝ᵥ S.mulVec h.ofLp = a ^ 2 * ‖γ.score‖ ^ 2 := by
      simp [h, S, v, dotProduct, Matrix.mulVec, Matrix.gram_apply,
        Fin.sum_univ_two]
      ring_nf
    rw [hi, hq]
    dsimp only [coord, Function.comp_apply]
    ring_nf
  rw [hdensity, ProbabilityTheory.multivariateGaussian_withDensity_exp_shift hS h]
  change (multivariateGaussian (Matrix.toEuclideanCLM (𝕜 := ℝ) S h) S).map
    (fun z => z 0) = _
  rw [(ProbabilityTheory.measurePreserving_eval_multivariateGaussian hS
    (μ := Matrix.toEuclideanCLM (𝕜 := ℝ) S h) (i := (0 : Fin 2))).map_eq]
  have hmean : (Matrix.toEuclideanCLM (𝕜 := ℝ) S h) 0 =
      a * ⟪u, γ.score⟫_ℝ := by
    change (S.mulVec h.ofLp) 0 = _
    simp only [S, h, v, Matrix.mulVec, Matrix.gram_apply, dotProduct,
      Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Submodule.coe_inner, mul_zero, zero_add]
    change ⟪u, γ.score⟫_ℝ * a = a * ⟪u, γ.score⟫_ℝ
    ring_nf
  have hvar : (S (0 : Fin 2) 0).toNNReal =
      ⟨‖u‖ ^ 2, sq_nonneg _⟩ := by
    apply NNReal.eq
    have hdiag : 0 ≤ S (0 : Fin 2) 0 := hS.diag_nonneg
    rw [Real.coe_toNNReal _ hdiag]
    simp [S, v, Matrix.gram_apply] <;> rfl
  rw [hmean, hvar]

private lemma exp_affine_score_integrable_and_integral
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (γ : NondominatedQMDPath P) (a : ℝ)
    (hsnd : π.map Prod.snd =
      gaussianReal 0 ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩) :
    let tiltMap : ℝ × ℝ → ℝ × ℝ := fun q =>
      (q.1, a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)
    Integrable (fun q : ℝ × ℝ => Real.exp q.2) (π.map tiltMap) ∧
      ∫ q, Real.exp q.2 ∂(π.map tiltMap) = 1 := by
  dsimp only
  let c : ℝ := (a ^ 2 / 2) * ‖γ.score‖ ^ 2
  let g : ℝ → ℝ := fun x => Real.exp (a * x - c)
  let tiltMap : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, a * q.2 - c)
  have hg_meas : Measurable g := by fun_prop
  have htilt : Measurable tiltMap := by fun_prop
  have hgauss : Integrable g (gaussianReal 0 ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩) := by
    have hbase := ProbabilityTheory.integrable_exp_mul_gaussianReal
      (μ := (0 : ℝ)) (v := ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩) a
    have hmul := hbase.mul_const (Real.exp (-c))
    exact hmul.congr (Filter.Eventually.of_forall fun x => by
      dsimp only [g]
      rw [sub_eq_add_neg, Real.exp_add])
  have hgauss_int : ∫ x, g x
        ∂(gaussianReal 0 (NNReal.mk (‖γ.score‖ ^ 2) (sq_nonneg _))) = 1 := by
    dsimp only [g]
    simp_rw [sub_eq_add_neg, Real.exp_add]
    rw [integral_mul_const,
      ProbabilityTheory.integral_exp_mul_gaussianReal]
    dsimp only [c]
    rw [← Real.exp_add]
    simp
    ring_nf
  have hpull : Integrable (fun q : ℝ × ℝ => g q.2) π := by
    rw [← hsnd] at hgauss
    exact hgauss.comp_measurable measurable_snd
  constructor
  · refine (integrable_map_measure (by fun_prop) htilt.aemeasurable).mpr ?_
    simpa only [Function.comp_apply, tiltMap, g] using! hpull
  · rw [integral_map htilt.aemeasurable (by fun_prop)]
    change ∫ q, g q.2 ∂π = 1
    calc
      ∫ q, g q.2 ∂π = ∫ x, g x ∂(π.map Prod.snd) := by
        rw [integral_map measurable_snd.aemeasurable hg_meas.aestronglyMeasurable]
      _ = ∫ x, g x
          ∂(gaussianReal 0 ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩) := by rw [hsnd]
      _ = 1 := hgauss_int

/-- Baseline joint CLT for a score pair, including singular Gram covariance.

Proof idea: finite-dimensional iid CLT and the `L²₀` moment facts. -/
theorem weakConverges_scorePair_under_pi
    (γ : NondominatedQMDPath P) (u : ↥(L2ZeroMean P)) :
    AsymptoticStatistics.WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (fun X => (normalizedScoreSum u n X,
          normalizedScoreSum γ.score n X)))
      (scorePairGaussian γ u) := by
  classical
  let v : Fin 2 → ↥(L2ZeroMean P) := ![u, γ.score]
  let Pinf : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P)
  let Y : ℕ → (ℕ → Ω) → EuclideanSpace ℝ (Fin 2) :=
    fun i X => scoreVector v (X i)
  haveI : IsProbabilityMeasure Pinf := by dsimp [Pinf]; infer_instance
  have hYmeas : ∀ i, Measurable (Y i) := fun i =>
    (measurable_scoreVector v).comp (measurable_pi_apply i)
  have hiid : iIndepFun Y Pinf := by
    have heval : iIndepFun (fun i (X : ℕ → Ω) => X i) Pinf := by
      dsimp only [Pinf]
      exact iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id
    exact heval.comp (g := fun _ => scoreVector v) fun _ => measurable_scoreVector v
  have hevalLaw : ∀ i, Pinf.map (fun X : ℕ → Ω => X i) = P := fun i => by
    dsimp only [Pinf]
    exact Measure.infinitePi_map_eval (fun _ : ℕ => P) i
  have hYlaw : ∀ i, Pinf.map (Y i) = P.map (scoreVector v) := fun i => by
    rw [show Y i = scoreVector v ∘ fun X : ℕ → Ω => X i from rfl,
      ← Measure.map_map (measurable_scoreVector v) (measurable_pi_apply i), hevalLaw]
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) Pinf Pinf := fun i =>
    ⟨(hYmeas i).aemeasurable, (hYmeas 0).aemeasurable, by rw [hYlaw i, hYlaw 0]⟩
  have hzero : ∀ a : EuclideanSpace ℝ (Fin 2),
      ∫ X, ⟪a, Y 0 X⟫_ℝ ∂Pinf = 0 := by
    intro a
    have hasm : AEStronglyMeasurable
        (fun x : Ω => ⟪a, scoreVector v x⟫_ℝ)
        (Pinf.map (fun X : ℕ → Ω => X 0)) := by
      rw [hevalLaw 0]
      exact (((continuous_const.inner continuous_id).measurable.comp
        (measurable_scoreVector v)).aestronglyMeasurable)
    have hmap :
        ∫ x, ⟪a, scoreVector v x⟫_ℝ ∂(Pinf.map (fun X : ℕ → Ω => X 0)) =
          ∫ X, ⟪a, scoreVector v (X 0)⟫_ℝ ∂Pinf :=
      MeasureTheory.integral_map (measurable_pi_apply (0 : ℕ)).aemeasurable hasm
    rw [hevalLaw 0] at hmap
    rw [← hmap, integral_congr_ae (Filter.Eventually.of_forall fun x => inner_scoreVector v a x)]
    rw [MeasureTheory.integral_finset_sum _]
    · simp [MeasureTheory.integral_const_mul, integral_l2ZeroMean_eq_zero]
    · intro i _
      exact ((Lp.memLp (v i : Lp ℝ 2 P)).integrable (by norm_num)).const_mul (a i)
  have hcov : ∀ a b : EuclideanSpace ℝ (Fin 2),
      ∫ X, ⟪a, Y 0 X⟫_ℝ * ⟪b, Y 0 X⟫_ℝ ∂Pinf =
        a.ofLp ⬝ᵥ (Matrix.gram ℝ v).mulVec b.ofLp := by
    intro a b
    have hasm : AEStronglyMeasurable
        (fun x : Ω => ⟪a, scoreVector v x⟫_ℝ * ⟪b, scoreVector v x⟫_ℝ)
        (Pinf.map (fun X : ℕ → Ω => X 0)) := by
      rw [hevalLaw 0]
      exact (((((continuous_const.inner continuous_id).measurable.comp
          (measurable_scoreVector v))).mul
        (((continuous_const.inner continuous_id).measurable.comp
          (measurable_scoreVector v)))).aestronglyMeasurable)
    have hmap :
        ∫ x, ⟪a, scoreVector v x⟫_ℝ * ⟪b, scoreVector v x⟫_ℝ
            ∂(Pinf.map (fun X : ℕ → Ω => X 0)) =
          ∫ X, ⟪a, scoreVector v (X 0)⟫_ℝ *
            ⟪b, scoreVector v (X 0)⟫_ℝ ∂Pinf :=
      MeasureTheory.integral_map (measurable_pi_apply (0 : ℕ)).aemeasurable hasm
    rw [hevalLaw 0] at hmap
    rw [← hmap]
    have hpw : (fun x => ⟪a, scoreVector v x⟫_ℝ * ⟪b, scoreVector v x⟫_ℝ) =
        fun x => ∑ i, ∑ j, (a i * b j) * ((v i : Ω → ℝ) x * (v j : Ω → ℝ) x) := by
      funext x
      rw [inner_scoreVector v a x, inner_scoreVector v b x, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring_nf
    have hint : ∀ i j : Fin 2, MeasureTheory.Integrable
        (fun x : Ω => (a i * b j) * ((v i : Ω → ℝ) x * (v j : Ω → ℝ) x)) P := by
      intro i j
      exact ((Lp.memLp (v i : Lp ℝ 2 P)).integrable_mul
        (Lp.memLp (v j : Lp ℝ 2 P))).const_mul (a i * b j)
    rw [hpw, MeasureTheory.integral_finset_sum _]
    · simp only [dotProduct, Matrix.mulVec]
      apply Finset.sum_congr rfl
      intro i _
      rw [MeasureTheory.integral_finset_sum _ (fun j _ => hint i j)]
      simp_rw [MeasureTheory.integral_const_mul, integral_l2ZeroMean_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.gram_apply]
      ring_nf
    · intro i _
      apply MeasureTheory.integrable_finset_sum
      intro j _
      exact hint i j
  have hL2atom : MemLp (scoreVector v) 2 P := by
    apply MemLp.of_eval_piLp
    intro i
    exact Lp.memLp (v i : Lp ℝ 2 P)
  have hL2 : MemLp (Y 0) 2 Pinf := by
    change MemLp (scoreVector v ∘ fun X : ℕ → Ω => X 0) 2 Pinf
    refine (MeasureTheory.memLp_map_measure_iff ?_ (measurable_pi_apply (0 : ℕ)).aemeasurable).mp ?_
    · rw [hevalLaw 0]
      exact (measurable_scoreVector v).aestronglyMeasurable
    · rw [hevalLaw 0]
      exact hL2atom
  have hclt := AsymptoticStatistics.ScoreCLT.clt_finDim Pinf Y hYmeas hiid hident hzero
    (Matrix.gram ℝ v) (Matrix.posSemidef_gram ℝ v) hcov hL2
  let V : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin 2) := fun n X =>
    WithLp.toLp 2 (fun i => normalizedScoreSum (v i) n X)
  have hVmeas : ∀ n, Measurable (V n) := fun n => by
    dsimp only [V, normalizedScoreSum]
    refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp ?_
    exact measurable_pi_lambda _ fun i => Measurable.const_mul
      (Finset.measurable_sum _ fun j _ =>
        (Lp.stronglyMeasurable (v i : Lp ℝ 2 P)).measurable.comp
          (measurable_pi_apply j)) _
  have hrestrict : ∀ n, Measurable (fun X : ℕ → Ω => fun i : Fin n => X i.val) :=
    fun n => measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have heq : ∀ n, (Measure.pi (fun _ : Fin n => P)).map (V n) =
      Pinf.map (fun X => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i X) := by
    intro n
    rw [AsymptoticStatistics.pi_const_eq_infinitePi_map P n,
      Measure.map_map (hVmeas n) (hrestrict n)]
    congr 1
    funext X
    apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
    funext i
    change (Real.sqrt n)⁻¹ * ∑ j : Fin n, (v i : Ω → ℝ) (X j.val) =
      (((Real.sqrt n)⁻¹ • ∑ j ∈ Finset.range n, Y j X :
        EuclideanSpace ℝ (Fin 2)).ofLp) i
    have hsum : (((∑ j ∈ Finset.range n, Y j X) :
        EuclideanSpace ℝ (Fin 2)).ofLp) i =
        ∑ j ∈ Finset.range n, ((Y j X : EuclideanSpace ℝ (Fin 2)).ofLp) i := by
      have hlin : (((∑ j ∈ Finset.range n, Y j X) :
          EuclideanSpace ℝ (Fin 2)).ofLp) =
          ∑ j ∈ Finset.range n, ((Y j X : EuclideanSpace ℝ (Fin 2)).ofLp) :=
        map_sum (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap _ _
      rw [hlin]
      exact Finset.sum_apply i _ _
    rw [show (((Real.sqrt n)⁻¹ • ∑ j ∈ Finset.range n, Y j X :
        EuclideanSpace ℝ (Fin 2)).ofLp) i =
      (Real.sqrt n)⁻¹ * (((∑ j ∈ Finset.range n, Y j X :
        EuclideanSpace ℝ (Fin 2)).ofLp) i) from rfl, hsum]
    change (Real.sqrt n)⁻¹ * ∑ j : Fin n, (v i : Ω → ℝ) (X j.val) =
      (Real.sqrt n)⁻¹ * ∑ j ∈ Finset.range n, (v i : Ω → ℝ) (X j)
    congr 1
    exact Fin.sum_univ_eq_sum_range
      (fun j => ((v i : Lp ℝ 2 P) : Ω → ℝ) (X j)) n
  have hvec : WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map (V n))
      (multivariateGaussian 0 (Matrix.gram ℝ v)) := by
    intro f
    simpa only [heq] using hclt f
  have hcoord_cont : Continuous
      (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0).prodMk
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1)
  have hcoord_meas := hcoord_cont.measurable
  have hpair := hvec.map
    (f := fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1))
    hcoord_cont hcoord_meas
  change WeakConverges
      (fun n => ((Measure.pi (fun _ : Fin n => P)).map (V n)).map
        (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)))
      ((multivariateGaussian 0 (Matrix.gram ℝ v)).map
        (fun z => (z 0, z 1))) at hpair
  have hseq : ∀ n, ((Measure.pi (fun _ : Fin n => P)).map (V n)).map
      (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) =
      (Measure.pi (fun _ : Fin n => P)).map
        (fun X => (normalizedScoreSum u n X,
          normalizedScoreSum γ.score n X)) := by
    intro n
    rw [Measure.map_map hcoord_meas (hVmeas n)]
    congr 1
  simp_rw [hseq] at hpair
  simpa only [scorePairGaussian, v] using hpair

private lemma weakConverges_normalizedScore_under_pi
    (γ : NondominatedQMDPath P) :
    WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (normalizedScoreSum γ.score n))
      (gaussianReal 0 ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩) := by
  have hpair := weakConverges_scorePair_under_pi γ γ.score
  have hsnd := hpair.map (f := Prod.snd) continuous_snd measurable_snd
  rw [scorePairGaussian_snd] at hsnd
  have hpairMeas : ∀ n, Measurable (fun X : Fin n → Ω =>
      (normalizedScoreSum γ.score n X, normalizedScoreSum γ.score n X)) :=
    fun n => (measurable_normalizedScoreSum γ.score n).prodMk
      (measurable_normalizedScoreSum γ.score n)
  change WeakConverges
    (fun n => ((Measure.pi (fun _ : Fin n => P)).map
      (fun X => (normalizedScoreSum γ.score n X,
        normalizedScoreSum γ.score n X))).map Prod.snd) _ at hsnd
  simpa only [Measure.map_map measurable_snd (hpairMeas _)] using! hsnd

private lemma weakConverges_actualLogLikelihood_under_pi
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (actualLogLikelihood γ a n))
      (gaussianReal
        (-(⟨a ^ 2 * ‖γ.score‖ ^ 2,
          mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩ : NNReal) / 2)
        ⟨a ^ 2 * ‖γ.score‖ ^ 2,
          mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩) := by
  let c : ℝ := (a ^ 2 / 2) * ‖γ.score‖ ^ 2
  let vScore : NNReal := ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩
  let vLog : NNReal := NNReal.mk (a ^ 2 * ‖γ.score‖ ^ 2)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have haff : Measurable (fun x : ℝ => a * x - c) := by fun_prop
  letI : IsProbabilityMeasure
      ((gaussianReal 0 vScore).map (fun x : ℝ => a * x - c)) :=
    Measure.isProbabilityMeasure_map haff.aemeasurable
  have hscore := weakConverges_normalizedScore_under_pi γ
  have hlin0 := hscore.map
    (f := fun x : ℝ => a * x - c) (by fun_prop) (by fun_prop)
  have hlin : WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (fun X => a * normalizedScoreSum γ.score n X - c))
      ((gaussianReal 0 vScore).map (fun x : ℝ => a * x - c)) := by
    change WeakConverges
      (fun n => ((Measure.pi (fun _ : Fin n => P)).map
        (normalizedScoreSum γ.score n)).map (fun x : ℝ => a * x - c)) _ at hlin0
    simpa only [Measure.map_map haff
      (measurable_normalizedScoreSum γ.score _), Function.comp_apply,
      vScore] using! hlin0
  have hdist : ∀ ε > 0, Tendsto
      (fun n => (Measure.pi (fun _ : Fin n => P)).real
        {X | ε ≤ dist
          (a * normalizedScoreSum γ.score n X - c)
          (actualLogLikelihood γ a n X)})
      atTop (nhds 0) := by
    intro ε hε
    have hset : ∀ n,
        {X : Fin n → Ω | ε ≤ dist
          (a * normalizedScoreSum γ.score n X - c)
          (actualLogLikelihood γ a n X)} =
        {X | ε ≤ |actualLogLikelihood γ a n X -
          (a * (Real.sqrt n)⁻¹ *
              ∑ i : Fin n, (γ.score : Ω → ℝ) (X i) -
            (a ^ 2 / 2) * ‖γ.score‖ ^ 2)|} := by
      intro n
      ext X
      simp only [Set.mem_setOf_eq, Real.dist_eq, normalizedScoreSum,
        actualLogLikelihood, c]
      rw [abs_sub_comm]
      ring_nf
    have hlan :=
      NondominatedQMDLAN.log_acProductLikelihood_lan_tendstoInMeasure γ a ha ε hε
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlan
    simpa only [measureReal_def, hset, Function.comp_apply,
      ENNReal.toReal_zero] using! hreal
  have hactual := WeakConverges.slutsky_of_tendstoInMeasure_dist
    (fun n => ((measurable_normalizedScoreSum γ.score n).const_mul a).sub_const c |>.aemeasurable)
    (fun n => (measurable_actualLogLikelihood γ a n).aemeasurable)
    hlin hdist
  have hgauss : (gaussianReal 0 vScore).map (fun x : ℝ => a * x - c) =
      gaussianReal (-(vLog : ℝ) / 2) vLog := by
    calc
      (gaussianReal 0 vScore).map (fun x : ℝ => a * x - c) =
          ((gaussianReal 0 vScore).map (fun x : ℝ => a * x)).map
            (fun x : ℝ => x - c) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = gaussianReal (-(vLog : ℝ) / 2) vLog := by
        rw [ProbabilityTheory.gaussianReal_map_const_mul,
          ProbabilityTheory.gaussianReal_map_sub_const]
        congr 2
        dsimp only [c, vLog]
        simp
        ring_nf
  rw [hgauss] at hactual
  simpa only [vLog] using! hactual

/-- Subsequence Le Cam third lemma using the actual RN product likelihood.

Proof idea: bounded-test product comparison, actual-likelihood LAN,
truncation, normalization, and uniform integrability. -/
theorem qmd_lecamThird_along_subseq
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a)
    (Y : ∀ n, (Fin n → Ω) → ℝ) (hY : ∀ n, Measurable (Y n))
    (χ : ℕ → ℕ) (hχ : StrictMono χ)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hπ : AsymptoticStatistics.WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (Y (χ k) X, normalizedScoreSum γ.score (χ k) X))) π) :
    AsymptoticStatistics.WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) =>
        γ.curve (a * (Real.sqrt (χ k))⁻¹))).map (Y (χ k)))
      ((π.withDensity (fun q => ENNReal.ofReal (Real.exp
        (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)))).map Prod.fst) := by
  let c : ℝ := (a ^ 2 / 2) * ‖γ.score‖ ^ 2
  let vScore : NNReal := ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩
  let vLog : NNReal := NNReal.mk (a ^ 2 * ‖γ.score‖ ^ 2)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  let tiltMap : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, a * q.2 - c)
  have htilt_cont : Continuous tiltMap := by fun_prop
  have htilt : Measurable tiltMap := htilt_cont.measurable
  haveI : IsProbabilityMeasure (π.map tiltMap) :=
    Measure.isProbabilityMeasure_map htilt.aemeasurable
  have hpairMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
      (Y (χ k) X, normalizedScoreSum γ.score (χ k) X)) := fun k =>
    (hY (χ k)).prodMk (measurable_normalizedScoreSum γ.score (χ k))
  have hscore_sub : WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (normalizedScoreSum γ.score (χ k)))
      (gaussianReal 0 vScore) := by
    simpa only [vScore] using
      (weakConverges_normalizedScore_under_pi γ).comp hχ
  have hscore_as_snd : WeakConverges
      (fun k => ((Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (Y (χ k) X, normalizedScoreSum γ.score (χ k) X))).map Prod.snd)
      (gaussianReal 0 vScore) := by
    simpa only [Measure.map_map measurable_snd (hpairMeas _)] using! hscore_sub
  have hπsnd : π.map Prod.snd = gaussianReal 0 vScore :=
    WeakConverges.snd_eq hπ hscore_as_snd
  have hlin := hπ.map htilt_cont htilt
  change WeakConverges
      (fun k => ((Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (Y (χ k) X, normalizedScoreSum γ.score (χ k) X))).map tiltMap)
      (π.map tiltMap) at hlin
  have hlinMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
      (Y (χ k) X, a * normalizedScoreSum γ.score (χ k) X - c)) := fun k =>
    (hY (χ k)).prodMk
      (((measurable_normalizedScoreSum γ.score (χ k)).const_mul a).sub_const c)
  have hlin' : WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (Y (χ k) X,
          a * normalizedScoreSum γ.score (χ k) X - c)))
      (π.map tiltMap) := by
    simpa only [Measure.map_map htilt (hpairMeas _), tiltMap, Function.comp_apply] using! hlin
  have hactualMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
      (Y (χ k) X, actualLogLikelihood γ a (χ k) X)) := fun k =>
    (hY (χ k)).prodMk (measurable_actualLogLikelihood γ a (χ k))
  have hdist : ∀ ε > 0, Tendsto
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).real
        {X | ε ≤ dist
          (Y (χ k) X, a * normalizedScoreSum γ.score (χ k) X - c)
          (Y (χ k) X, actualLogLikelihood γ a (χ k) X)})
      atTop (nhds 0) := by
    intro ε hε
    have hset : ∀ k,
        {X : Fin (χ k) → Ω | ε ≤ dist
          (Y (χ k) X, a * normalizedScoreSum γ.score (χ k) X - c)
          (Y (χ k) X, actualLogLikelihood γ a (χ k) X)} =
        {X | ε ≤ |actualLogLikelihood γ a (χ k) X -
          (a * (Real.sqrt (χ k))⁻¹ *
              ∑ i : Fin (χ k), (γ.score : Ω → ℝ) (X i) -
            (a ^ 2 / 2) * ‖γ.score‖ ^ 2)|} := by
      intro k
      ext X
      simp only [Set.mem_setOf_eq, dist_prod_same_left, Real.dist_eq,
        normalizedScoreSum, actualLogLikelihood, c]
      rw [abs_sub_comm]
      ring_nf
    have hlan :=
      NondominatedQMDLAN.log_acProductLikelihood_lan_tendstoInMeasure γ a ha ε hε
    have hlan_sub := hlan.comp hχ.tendsto_atTop
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlan_sub
    simpa only [measureReal_def, hset, Function.comp_apply, ENNReal.toReal_zero] using! hreal
  have hjointLog : WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (Y (χ k) X, actualLogLikelihood γ a (χ k) X)))
      (π.map tiltMap) :=
    WeakConverges.slutsky_of_tendstoInMeasure_dist
      (fun k => (hlinMeas k).aemeasurable)
      (fun k => (hactualMeas k).aemeasurable) hlin' hdist
  have htilt_snd : (π.map tiltMap).map Prod.snd =
      gaussianReal (-(vLog : ℝ) / 2) vLog := by
    calc
      (π.map tiltMap).map Prod.snd =
          π.map (fun q : ℝ × ℝ => a * q.2 - c) := by
        rw [Measure.map_map measurable_snd htilt]
        rfl
      _ = (π.map Prod.snd).map (fun x : ℝ => a * x - c) := by
        rw [Measure.map_map (by fun_prop) measurable_snd]
        rfl
      _ = (gaussianReal 0 vScore).map (fun x : ℝ => a * x - c) := by rw [hπsnd]
      _ = ((gaussianReal 0 vScore).map (fun x : ℝ => a * x)).map
          (fun x : ℝ => x - c) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = gaussianReal (-(vLog : ℝ) / 2) vLog := by
        rw [ProbabilityTheory.gaussianReal_map_const_mul,
          ProbabilityTheory.gaussianReal_map_sub_const]
        congr 2
        dsimp only [c, vLog]
        simp
        ring_nf
  have hlogWeak : WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (actualLogLikelihood γ a (χ k)))
      (gaussianReal (-(vLog : ℝ) / 2) vLog) := by
    have hsnd := hjointLog.map (f := Prod.snd) continuous_snd measurable_snd
    rw [htilt_snd] at hsnd
    simpa only [Measure.map_map measurable_snd (hactualMeas _)] using! hsnd
  have h_exp_int : ∀ k, Integrable
      (fun X => Real.exp (actualLogLikelihood γ a (χ k) X))
      (Measure.pi (fun _ : Fin (χ k) => P)) := fun k =>
    integrable_exp_actualLogLikelihood γ a ha (χ k)
  have h_mass : Tendsto (fun k =>
      ∫ X, Real.exp (actualLogLikelihood γ a (χ k) X)
        ∂(Measure.pi (fun _ : Fin (χ k) => P))) atTop (nhds 1) :=
    (integral_exp_actualLogLikelihood_tendsto_one γ a ha).comp hχ.tendsto_atTop
  letI : ∀ k, IsProbabilityMeasure
      (Measure.pi (fun _ : Fin (χ k) => γ.curve (a * (Real.sqrt (χ k))⁻¹))) :=
    fun k => by
      letI : IsProbabilityMeasure (γ.curve (a * (Real.sqrt (χ k))⁻¹)) :=
        γ.curve_isProbability _
          (mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      infer_instance
  have hUI := uniform_integrability_exp_L_of_integral_tendsto_one
    (Ω := fun k => Fin (χ k) → Ω)
    (fun k => Measure.pi (fun _ : Fin (χ k) => P))
    (fun k => Measure.pi (fun _ : Fin (χ k) =>
      γ.curve (a * (Real.sqrt (χ k))⁻¹)))
    (fun k => actualLogLikelihood γ a (χ k))
    (fun k => measurable_actualLogLikelihood γ a (χ k))
    h_exp_int h_mass vLog hlogWeak
  obtain ⟨ρ, hρ, hcmp⟩ := actualLog_integral_comparison γ a ha Y hY
  have hcmp_sub : ∃ ρ' : ℕ → ℝ, Tendsto ρ' atTop (nhds 0) ∧
      ∀ (f : BoundedContinuousFunction ℝ ℝ) (k : ℕ),
        |∫ X, f (Y (χ k) X) ∂(Measure.pi (fun _ : Fin (χ k) =>
              γ.curve (a * (Real.sqrt (χ k))⁻¹))) -
          ∫ X, f (Y (χ k) X) * Real.exp (actualLogLikelihood γ a (χ k) X)
            ∂(Measure.pi (fun _ : Fin (χ k) => P))| ≤ ‖f‖ * ρ' k :=
    ⟨ρ ∘ χ, hρ.comp hχ.tendsto_atTop, fun f k => hcmp f (χ k)⟩
  have hmgf := exp_affine_score_integrable_and_integral π γ a (by
    simpa only [vScore] using hπsnd)
  have hlecam := weak_limit_under_Q_of_lecam_third_of_integral_comparison
    (Ω := fun k => Fin (χ k) → Ω) (E := ℝ)
    (fun k => Measure.pi (fun _ : Fin (χ k) => P))
    (fun k => Measure.pi (fun _ : Fin (χ k) =>
      γ.curve (a * (Real.sqrt (χ k))⁻¹)))
    (fun k => Y (χ k)) (fun k => actualLogLikelihood γ a (χ k))
    (fun k => hY (χ k))
    (fun k => measurable_actualLogLikelihood γ a (χ k))
    hcmp_sub (π.map tiltMap) hjointLog hUI hmgf.1 hmgf.2
  have htarget :
      ((π.map tiltMap).withDensity
        (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.2))).map Prod.fst =
      (π.withDensity (fun q => ENNReal.ofReal (Real.exp
        (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)))).map Prod.fst := by
    have hdens : Measurable
        (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.2)) := by fun_prop
    rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
      π tiltMap htilt _ hdens]
    rw [Measure.map_map measurable_fst htilt]
    rfl
  rw [← htarget]
  exact hlecam

/-- Local score CLT under a nonnegative one-sided QMD tilt.

Proof idea: score-pair CLT, `qmd_lecamThird_along_subseq`, and the tilted
possibly-singular Gram-Gaussian calculation. -/
theorem qmd_local_score_clt
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a)
    (u : ↥(L2ZeroMean P)) :
    AsymptoticStatistics.WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))).map (normalizedScoreSum u n))
      (gaussianReal (a * ⟪u, γ.score⟫_ℝ)
        ⟨‖u‖ ^ 2, sq_nonneg _⟩) := by
  letI : IsProbabilityMeasure (scorePairGaussian γ u) := by
    unfold scorePairGaussian
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have h := qmd_lecamThird_along_subseq γ a ha
    (fun n => normalizedScoreSum u n)
    (fun n => measurable_normalizedScoreSum u n)
    id strictMono_id (scorePairGaussian γ u)
    (by simpa only [Function.id_def] using weakConverges_scorePair_under_pi γ u)
  rw [scorePairGaussian_tilt_fst] at h
  simpa only [Function.id_def] using h

/-- Every fixed nonnegative local path law is contiguous to the baseline.

Proof idea: actual LAN and Le Cam's first lemma, including the zero-score
normalization split. -/
theorem qmd_local_contiguous
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    Contiguous atTop
      (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n => Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))) := by
  let vLog : NNReal := NNReal.mk (a ^ 2 * ‖γ.score‖ ^ 2)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  letI : ∀ n, IsProbabilityMeasure
      (Measure.pi (fun _ : Fin n => γ.curve (a * (Real.sqrt n)⁻¹))) :=
    fun n => by
      letI : IsProbabilityMeasure (γ.curve (a * (Real.sqrt n)⁻¹)) :=
        γ.curve_isProbability _
          (mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      infer_instance
  have hlog : WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (actualLogLikelihood γ a n))
      (gaussianReal (-(vLog : ℝ) / 2) vLog) := by
    simpa only [vLog] using! weakConverges_actualLogLikelihood_under_pi γ a ha
  have h_exp_int : ∀ n, Integrable
      (fun X => Real.exp (actualLogLikelihood γ a n X))
      (Measure.pi (fun _ : Fin n => P)) :=
    fun n => integrable_exp_actualLogLikelihood γ a ha n
  have hUI := uniform_integrability_exp_L_of_integral_tendsto_one
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n => Measure.pi (fun _ : Fin n =>
      γ.curve (a * (Real.sqrt n)⁻¹)))
    (actualLogLikelihood γ a)
    (measurable_actualLogLikelihood γ a)
    h_exp_int (integral_exp_actualLogLikelihood_tendsto_one γ a ha)
    vLog hlog
  intro A hA hPA
  have hPAreal : Tendsto (fun n =>
      ((Measure.pi (fun _ : Fin n => P)) (A n)).toReal) atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hPA
    simpa only [Function.comp_apply, ENNReal.toReal_zero] using! h
  let Y : ∀ n, (Fin n → Ω) → ℝ := fun n => (A n).indicator (fun _ => 1)
  have hY : ∀ n, Measurable (Y n) := fun n => measurable_one.indicator (hA n)
  let clip : BoundedContinuousFunction ℝ ℝ :=
    { toFun := fun x => min (max x 0) 1
      continuous_toFun := (continuous_id.max continuous_const).min continuous_const
      map_bounded' := ⟨1, fun x y => by
        rw [Real.dist_eq]
        have hx0 : 0 ≤ min (max x 0) 1 :=
          le_min (le_max_right _ _) zero_le_one
        have hy0 : 0 ≤ min (max y 0) 1 :=
          le_min (le_max_right _ _) zero_le_one
        have hx1 : min (max x 0) 1 ≤ 1 := min_le_right _ _
        have hy1 : min (max y 0) 1 ≤ 1 := min_le_right _ _
        rw [abs_le]
        constructor <;> linarith⟩ }
  have hclipY : ∀ n X, clip (Y n X) = Y n X := by
    intro n X
    by_cases hX : X ∈ A n <;> simp [clip, Y, hX]
  obtain ⟨ρ, hρ, hcmp⟩ := actualLog_integral_comparison γ a ha Y hY
  have hweighted : Tendsto (fun n =>
      ∫ X, Y n X * Real.exp (actualLogLikelihood γ a n X)
        ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨M, hM, N₁, hN₁⟩ := hUI (ε / 2) (by linarith)
    have hM1 : 0 < M + 1 := by linarith
    have hthreshold : 0 < ε / (2 * (M + 1)) := by positivity
    have hPsmall := (Metric.tendsto_nhds.mp hPAreal)
      (ε / (2 * (M + 1))) hthreshold
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hPsmall
    rw [Filter.eventually_atTop]
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hn₁ : N₁ ≤ n := le_of_max_le_left hn
    have hn₂ : N₂ ≤ n := le_of_max_le_right hn
    have hYnonneg : ∀ X, 0 ≤ Y n X := by
      intro X
      by_cases hX : X ∈ A n <;> simp [Y, hX]
    have hYle : ∀ X, Y n X ≤ 1 := by
      intro X
      by_cases hX : X ∈ A n <;> simp [Y, hX]
    have htrunc : Integrable (fun X =>
        min (Real.exp (actualLogLikelihood γ a n X)) M)
        (Measure.pi (fun _ : Fin n => P)) := by
      refine (h_exp_int n).mono' ?_ ?_
      · exact (((measurable_actualLogLikelihood γ a n).exp).min
          measurable_const).aestronglyMeasurable
      · filter_upwards with X
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact min_le_left _ _
        · exact le_min (Real.exp_pos _).le hM
    have htail : Integrable (fun X =>
        Real.exp (actualLogLikelihood γ a n X) -
          min (Real.exp (actualLogLikelihood γ a n X)) M)
        (Measure.pi (fun _ : Fin n => P)) := (h_exp_int n).sub htrunc
    have hYint : Integrable (Y n) (Measure.pi (fun _ : Fin n => P)) := by
      exact (integrable_const (1 : ℝ)).indicator (hA n)
    have hMY : Integrable (fun X => M * Y n X)
        (Measure.pi (fun _ : Fin n => P)) := hYint.const_mul M
    have hright := hMY.add htail
    have hmono :
        ∫ X, Y n X * Real.exp (actualLogLikelihood γ a n X)
            ∂(Measure.pi (fun _ : Fin n => P)) ≤
          ∫ X, M * Y n X +
              (Real.exp (actualLogLikelihood γ a n X) -
                min (Real.exp (actualLogLikelihood γ a n X)) M)
            ∂(Measure.pi (fun _ : Fin n => P)) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun X =>
          mul_nonneg (hYnonneg X) (Real.exp_pos _).le
      · exact hright
      · filter_upwards with X
        by_cases hX : X ∈ A n
        · have hmin := min_le_right
              (Real.exp (actualLogLikelihood γ a n X)) M
          simp only [Y, Set.indicator_of_mem hX, one_mul]
          linarith
        · simp only [Y, Set.indicator_of_notMem hX,
            zero_mul, mul_zero, zero_add, sub_nonneg]
          exact min_le_left _ _
    have htail_bound := hN₁ n hn₁
    have hPbound :
        ((Measure.pi (fun _ : Fin n => P)) (A n)).toReal <
          ε / (2 * (M + 1)) := by
      have hn' := hN₂ n hn₂
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hn'
      exact hn'
    have hMP : M * ((Measure.pi (fun _ : Fin n => P)) (A n)).toReal < ε / 2 := by
      calc
        M * ((Measure.pi (fun _ : Fin n => P)) (A n)).toReal ≤
            (M + 1) * ((Measure.pi (fun _ : Fin n => P)) (A n)).toReal := by
              gcongr
              linarith
        _ < (M + 1) * (ε / (2 * (M + 1))) := by
              exact mul_lt_mul_of_pos_left hPbound hM1
        _ = ε / 2 := by field_simp
    have hweighted_nonneg : 0 ≤
        ∫ X, Y n X * Real.exp (actualLogLikelihood γ a n X)
          ∂(Measure.pi (fun _ : Fin n => P)) :=
      integral_nonneg fun X => mul_nonneg (hYnonneg X) (Real.exp_pos _).le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hweighted_nonneg]
    calc
      ∫ X, Y n X * Real.exp (actualLogLikelihood γ a n X)
          ∂(Measure.pi (fun _ : Fin n => P)) ≤
          ∫ X, M * Y n X +
              (Real.exp (actualLogLikelihood γ a n X) -
                min (Real.exp (actualLogLikelihood γ a n X)) M)
            ∂(Measure.pi (fun _ : Fin n => P)) := hmono
      _ = M * ((Measure.pi (fun _ : Fin n => P)) (A n)).toReal +
          ∫ X, Real.exp (actualLogLikelihood γ a n X) -
              min (Real.exp (actualLogLikelihood γ a n X)) M
            ∂(Measure.pi (fun _ : Fin n => P)) := by
            rw [integral_add hMY htail, integral_const_mul]
            congr 2
            simpa only [Y, measureReal_def] using!
              (integral_indicator_one
                (μ := Measure.pi (fun _ : Fin n => P)) (hA n))
      _ < ε := by linarith
  have herror : Tendsto (fun n =>
      (∫ X, Y n X ∂(Measure.pi (fun _ : Fin n =>
          γ.curve (a * (Real.sqrt n)⁻¹)))) -
        ∫ X, Y n X * Real.exp (actualLogLikelihood γ a n X)
          ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 0) := by
    have hρscaled : Tendsto (fun n => ‖clip‖ * ρ n) atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hρ :
          Tendsto (fun n => ‖clip‖ * ρ n) atTop (nhds (‖clip‖ * 0)))
    rw [Metric.tendsto_nhds]
    intro ε hε
    have herr := (Metric.tendsto_nhds.mp
      hρscaled) ε hε
    filter_upwards [herr] with n hn
    have hc := hcmp clip n
    simp_rw [hclipY] at hc
    rw [Real.dist_eq, sub_zero]
    exact hc.trans_lt ((le_abs_self _).trans_lt (by
      simpa only [Real.dist_eq, sub_zero] using hn))
  have hQreal : Tendsto (fun n =>
      ((Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))) (A n)).toReal)
      atTop (nhds 0) := by
    have hsum := herror.add hweighted
    have hQrepr : ∀ n,
        ((Measure.pi (fun _ : Fin n =>
          γ.curve (a * (Real.sqrt n)⁻¹))) (A n)).toReal =
        ∫ X, Y n X ∂(Measure.pi (fun _ : Fin n =>
          γ.curve (a * (Real.sqrt n)⁻¹))) := by
      intro n
      simpa only [Y, measureReal_def] using!
        (integral_indicator_one
          (μ := Measure.pi (fun _ : Fin n =>
            γ.curve (a * (Real.sqrt n)⁻¹))) (hA n)).symm
    simpa only [hQrepr, sub_add_cancel, zero_add] using hsum
  have hofReal := (ENNReal.continuous_ofReal.tendsto 0).comp hQreal
  have heq : (fun n => ENNReal.ofReal
      ((Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))) (A n)).toReal) =
      fun n => (Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))) (A n) := by
    funext n
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  change Tendsto (fun n => ENNReal.ofReal
      ((Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))) (A n)).toReal)
      atTop (nhds (ENNReal.ofReal 0)) at hofReal
  rw [heq] at hofReal
  simpa only [ENNReal.ofReal_zero] using hofReal

/-- A zero-score QMD path is asymptotically equivalent to baseline for all
uniformly bounded measurable tests.

Proof idea: combine contiguity in both directions with the zero-score LAN
limit and actual product comparison. -/
theorem zero_score_local_product_equivalent
    (γ : NondominatedQMDPath P) (hscore : γ.score = 0)
    (f : ∀ n, (Fin n → Ω) → ℝ) (C : ℝ)
    (hf : ∀ n, Measurable (f n)) (hbound : ∀ n X, |f n X| ≤ C) :
    Tendsto (fun n =>
      (∫ X, f n X ∂(Measure.pi (fun _ : Fin n => γ.curve ((Real.sqrt n)⁻¹))))
        - ∫ X, f n X ∂(Measure.pi (fun _ : Fin n => P)))
      atTop (nhds 0) := by
  have hC : 0 ≤ C :=
    (abs_nonneg (f 0 (fun i => Fin.elim0 i))).trans
      (hbound 0 (fun i => Fin.elim0 i))
  have hlog0 : WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (actualLogLikelihood γ 1 n))
      (Measure.dirac 0) := by
    let v₀ : NNReal := ⟨1 ^ 2 * ‖γ.score‖ ^ 2,
      mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩
    have h : WeakConverges
        (fun n => (Measure.pi (fun _ : Fin n => P)).map
          (actualLogLikelihood γ 1 n))
        (gaussianReal (-(v₀ : ℝ) / 2) v₀) := by
      simpa only [v₀] using!
        weakConverges_actualLogLikelihood_under_pi γ 1 zero_le_one
    have hv₀ : v₀ = 0 := by
      apply NNReal.eq
      (norm_num [v₀, hscore]; rfl)
    rw [hv₀] at h
    simpa only [NNReal.coe_zero, neg_zero, zero_div,
      ProbabilityTheory.gaussianReal_zero_var] using h
  let truncExp : BoundedContinuousFunction ℝ ℝ :=
    { toFun := fun x => min (Real.exp x) 1
      continuous_toFun := Real.continuous_exp.min continuous_const
      map_bounded' := ⟨1, fun x y => by
        rw [Real.dist_eq]
        have hx0 : 0 ≤ min (Real.exp x) 1 :=
          le_min (Real.exp_pos _).le zero_le_one
        have hy0 : 0 ≤ min (Real.exp y) 1 :=
          le_min (Real.exp_pos _).le zero_le_one
        have hx1 : min (Real.exp x) 1 ≤ 1 := min_le_right _ _
        have hy1 : min (Real.exp y) 1 ≤ 1 := min_le_right _ _
        rw [abs_le]
        constructor <;> linarith⟩ }
  have htrunc : Tendsto (fun n =>
      ∫ X, min (Real.exp (actualLogLikelihood γ 1 n X)) 1
        ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 1) := by
    have h := hlog0 truncExp
    have hmap : ∀ n,
        ∫ x, truncExp x
            ∂((Measure.pi (fun _ : Fin n => P)).map
              (actualLogLikelihood γ 1 n)) =
          ∫ X, truncExp (actualLogLikelihood γ 1 n X)
            ∂(Measure.pi (fun _ : Fin n => P)) := by
      intro n
      exact integral_map
        (measurable_actualLogLikelihood γ 1 n).aemeasurable
        truncExp.continuous.aestronglyMeasurable
    simp_rw [hmap] at h
    dsimp only [truncExp] at h
    rw [MeasureTheory.integral_dirac] at h
    norm_num at h
    exact h
  have hmass := integral_exp_actualLogLikelihood_tendsto_one γ 1 zero_le_one
  have hExpL1_eq : ∀ n,
      ∫ X, |Real.exp (actualLogLikelihood γ 1 n X) - 1|
          ∂(Measure.pi (fun _ : Fin n => P)) =
        (∫ X, Real.exp (actualLogLikelihood γ 1 n X)
          ∂(Measure.pi (fun _ : Fin n => P))) + 1 -
          2 * (∫ X, min (Real.exp (actualLogLikelihood γ 1 n X)) 1
            ∂(Measure.pi (fun _ : Fin n => P))) := by
    intro n
    have hexp := integrable_exp_actualLogLikelihood γ 1 zero_le_one n
    have hone : Integrable (fun _ : Fin n → Ω => (1 : ℝ))
        (Measure.pi (fun _ : Fin n => P)) := integrable_const 1
    have hmin : Integrable (fun X =>
        min (Real.exp (actualLogLikelihood γ 1 n X)) 1)
        (Measure.pi (fun _ : Fin n => P)) := by
      refine hexp.mono' ?_ ?_
      · exact (((measurable_actualLogLikelihood γ 1 n).exp).min
          measurable_const).aestronglyMeasurable
      · filter_upwards with X
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact min_le_left _ _
        · exact le_min (Real.exp_pos _).le zero_le_one
    have hpw : (fun X =>
        |Real.exp (actualLogLikelihood γ 1 n X) - 1|) =
        fun X => Real.exp (actualLogLikelihood γ 1 n X) + 1 -
          2 * min (Real.exp (actualLogLikelihood γ 1 n X)) 1 := by
      funext X
      by_cases hz : Real.exp (actualLogLikelihood γ 1 n X) ≤ 1
      · rw [min_eq_left hz, abs_of_nonpos (sub_nonpos.mpr hz)]
        ring_nf
      · have hz' : 1 ≤ Real.exp (actualLogLikelihood γ 1 n X) :=
          (lt_of_not_ge hz).le
        rw [min_eq_right hz', abs_of_nonneg (sub_nonneg.mpr hz')]
        ring_nf
    rw [hpw]
    calc
      ∫ X, Real.exp (actualLogLikelihood γ 1 n X) + 1 -
          2 * min (Real.exp (actualLogLikelihood γ 1 n X)) 1
          ∂(Measure.pi (fun _ : Fin n => P)) =
          (∫ X, Real.exp (actualLogLikelihood γ 1 n X) + 1
            ∂(Measure.pi (fun _ : Fin n => P))) -
          ∫ X, 2 * min (Real.exp (actualLogLikelihood γ 1 n X)) 1
            ∂(Measure.pi (fun _ : Fin n => P)) :=
        integral_sub (hexp.add hone) (hmin.const_mul 2)
      _ = _ := by
        rw [integral_add hexp hone, integral_const_mul, integral_const]
        have hOne : (Measure.pi (fun _ : Fin n => P)).real Set.univ = 1 := by
          simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
        rw [hOne]
        simp only [smul_eq_mul, mul_one]
  have hExpL1 : Tendsto (fun n =>
      ∫ X, |Real.exp (actualLogLikelihood γ 1 n X) - 1|
        ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 0) := by
    have hcalc := (hmass.add_const 1).sub (htrunc.const_mul 2)
    have hcalc' : Tendsto (fun n =>
        (∫ X, Real.exp (actualLogLikelihood γ 1 n X)
          ∂(Measure.pi (fun _ : Fin n => P))) + 1 -
          2 * (∫ X, min (Real.exp (actualLogLikelihood γ 1 n X)) 1
            ∂(Measure.pi (fun _ : Fin n => P)))) atTop (nhds 0) := by
      simpa only [one_add_one_eq_two, mul_one, sub_self] using hcalc
    exact hcalc'.congr' (Filter.Eventually.of_forall fun n => (hExpL1_eq n).symm)
  have hbad : Tendsto (fun n =>
      ((Measure.pi (fun _ : Fin n => P))
        {X | (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal = 0}).toReal)
      atTop (nhds 0) := by
    have hz := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (γ.base_zeroLikelihood_localScale_tendsto 1 zero_le_one)
    refine squeeze_zero
      (fun _ => ENNReal.toReal_nonneg)
      (fun n => ENNReal.toReal_mono
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (measure_ne_top P _))
        (by simpa only [one_mul] using!
          acProductLikelihood_toReal_zero_mass_le γ ((Real.sqrt n)⁻¹) n)) ?_
    simpa only [one_mul, Function.comp_apply, ENNReal.toReal_zero] using! hz
  have hExpActualL1_eq : ∀ n,
      ∫ X, |Real.exp (actualLogLikelihood γ 1 n X) -
          (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal|
          ∂(Measure.pi (fun _ : Fin n => P)) =
        ((Measure.pi (fun _ : Fin n => P))
          {X | (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal = 0}).toReal := by
    intro n
    have hexp := integrable_exp_actualLogLikelihood γ 1 zero_le_one n
    have hR := (γ.integrable_acProductLikelihood_and_integral
      ((Real.sqrt n)⁻¹) (inv_nonneg.mpr (Real.sqrt_nonneg _)) n).1
    rw [integral_congr_ae (Filter.Eventually.of_forall fun X => by
      rw [abs_of_nonneg]
      by_cases hzero :
          (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal = 0
      · simp [hzero, actualLogLikelihood]
      · rw [show actualLogLikelihood γ 1 n X = Real.log
            (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal by
            simp only [actualLogLikelihood, one_mul]]
        rw [Real.exp_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero))]
        exact sub_nonneg.mpr le_rfl
      )]
    rw [integral_sub hexp hR]
    simpa only [one_mul] using
      integral_exp_actualLogLikelihood_sub_likelihood γ 1 zero_le_one n
  have hExpActualL1 : Tendsto (fun n =>
      ∫ X, |Real.exp (actualLogLikelihood γ 1 n X) -
          (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal|
        ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 0) :=
    hbad.congr' (Filter.Eventually.of_forall fun n => (hExpActualL1_eq n).symm)
  have hActualL1 : Tendsto (fun n =>
      ∫ X, |(γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal - 1|
        ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact integral_nonneg fun _ => abs_nonneg _
    · intro n
      have hR := (γ.integrable_acProductLikelihood_and_integral
        ((Real.sqrt n)⁻¹) (inv_nonneg.mpr (Real.sqrt_nonneg _)) n).1
      have hexp := integrable_exp_actualLogLikelihood γ 1 zero_le_one n
      have hleft := (hR.sub (integrable_const 1)).abs
      have hfirst : Integrable (fun X =>
          |Real.exp (actualLogLikelihood γ 1 n X) -
            (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal|)
          (Measure.pi (fun _ : Fin n => P)) := (hexp.sub hR).abs
      have hsecond : Integrable (fun X =>
          |Real.exp (actualLogLikelihood γ 1 n X) - 1|)
          (Measure.pi (fun _ : Fin n => P)) :=
        (hexp.sub (integrable_const 1)).abs
      calc
        ∫ X, |(γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal - 1|
            ∂(Measure.pi (fun _ : Fin n => P)) ≤
          ∫ X, |Real.exp (actualLogLikelihood γ 1 n X) -
              (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal| +
              |Real.exp (actualLogLikelihood γ 1 n X) - 1|
            ∂(Measure.pi (fun _ : Fin n => P)) := by
              apply integral_mono hleft (hfirst.add hsecond)
              intro X
              calc
                |(γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal - 1| ≤
                    |(γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal -
                      Real.exp (actualLogLikelihood γ 1 n X)| +
                    |Real.exp (actualLogLikelihood γ 1 n X) - 1| :=
                  abs_sub_le _ _ _
                _ = _ := by
                  rw [abs_sub_comm
                    (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal]
                  rfl
        _ = (∫ X, |Real.exp (actualLogLikelihood γ 1 n X) -
              (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal|
            ∂(Measure.pi (fun _ : Fin n => P))) +
              ∫ X, |Real.exp (actualLogLikelihood γ 1 n X) - 1|
              ∂(Measure.pi (fun _ : Fin n => P)) := by
                rw [integral_add hfirst hsecond]
    · simpa only [zero_add] using hExpActualL1.add hExpL1
  obtain ⟨error, herror, hcomparison⟩ :=
    γ.product_integral_comparison 1 C zero_le_one f hf hbound
  have hweighted : Tendsto (fun n =>
      (∫ X, f n X *
          (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal
          ∂(Measure.pi (fun _ : Fin n => P))) -
        ∫ X, f n X ∂(Measure.pi (fun _ : Fin n => P)))
      atTop (nhds 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    change Tendsto (fun n =>
      |(∫ X, f n X *
          (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal
          ∂(Measure.pi (fun _ : Fin n => P))) -
        ∫ X, f n X ∂(Measure.pi (fun _ : Fin n => P))|)
      atTop (nhds 0)
    apply squeeze_zero (g := fun n => C *
      ∫ X, |(γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal - 1|
        ∂(Measure.pi (fun _ : Fin n => P)))
    · exact fun _ => abs_nonneg _
    · intro n
      let R : (Fin n → Ω) → ℝ := fun X =>
        (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal
      have hR : Integrable R (Measure.pi (fun _ : Fin n => P)) :=
        (γ.integrable_acProductLikelihood_and_integral
          ((Real.sqrt n)⁻¹) (inv_nonneg.mpr (Real.sqrt_nonneg _)) n).1
      have hfint : Integrable (f n) (Measure.pi (fun _ : Fin n => P)) := by
        refine Integrable.of_bound (hf n).aestronglyMeasurable C ?_
        exact Filter.Eventually.of_forall fun X => by
          simpa only [Real.norm_eq_abs] using hbound n X
      have hfR : Integrable (fun X => f n X * R X)
          (Measure.pi (fun _ : Fin n => P)) :=
        hR.bdd_mul (hf n).aestronglyMeasurable
          (Filter.Eventually.of_forall fun X => by
            simpa only [Real.norm_eq_abs] using hbound n X)
      have hrewrite :
          (∫ X, f n X * R X ∂(Measure.pi (fun _ : Fin n => P))) -
              ∫ X, f n X ∂(Measure.pi (fun _ : Fin n => P)) =
            ∫ X, f n X * (R X - 1) ∂(Measure.pi (fun _ : Fin n => P)) := by
        rw [← integral_sub hfR hfint]
        apply integral_congr_ae
        filter_upwards with X
        ring_nf
      change |(∫ X, f n X * R X ∂(Measure.pi (fun _ : Fin n => P))) -
        ∫ X, f n X ∂(Measure.pi (fun _ : Fin n => P))| ≤ _
      rw [hrewrite]
      have hmajor : Integrable (fun X => C * |R X - 1|)
          (Measure.pi (fun _ : Fin n => P)) :=
        ((hR.sub (integrable_const 1)).abs).const_mul C
      have hb := MeasureTheory.norm_integral_le_of_norm_le hmajor
        (Filter.Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hbound n X) (abs_nonneg _))
      rw [integral_const_mul] at hb
      simpa only [Real.norm_eq_abs, R] using hb
    · simpa only [mul_zero] using hActualL1.const_mul C
  have hcomparison' : Tendsto (fun n =>
      (∫ X, f n X ∂(Measure.pi (fun _ : Fin n =>
          γ.curve ((Real.sqrt n)⁻¹)))) -
        ∫ X, f n X *
          (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal
          ∂(Measure.pi (fun _ : Fin n => P)))
      atTop (nhds 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    change Tendsto (fun n =>
      |(∫ X, f n X ∂(Measure.pi (fun _ : Fin n =>
          γ.curve ((Real.sqrt n)⁻¹)))) -
        ∫ X, f n X *
          (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n X).toReal
          ∂(Measure.pi (fun _ : Fin n => P))|) atTop (nhds 0)
    apply squeeze_zero (fun _ => abs_nonneg _)
    · intro n
      simpa only [one_mul] using hcomparison n
    · exact herror
  have hsum := hcomparison'.add hweighted
  convert hsum using 1
  · funext n
    ring_nf
  · ring_nf

end AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird
