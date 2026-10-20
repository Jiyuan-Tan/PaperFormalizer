module
public import StatLean.AsymptoticStatistics.LowerBounds.GaussianConeBayes
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.Outer
public import StatLean.AsymptoticStatistics.ForMathlib.Prohorov
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

public import Mathlib.Probability.Kernel.Composition.RadonNikodym

@[expose] public section

/-! # Compactification of finite loss profiles

The compact object is the finite vector of bounded-UC losses, not a new
global estimator sequence.  This is the finite-experiment compactification
used in the nondominated proof of vdV Theorem 25.21.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics.Experiment.FiniteRiskCompactification

open AsymptoticStatistics
open AsymptoticStatistics.LowerBounds.GaussianConeBayes

/-- Finite vector of centered real loss values, packaged in Mathlib's
`EuclideanSpace` model. -/
noncomputable def finiteLossProfile {d r : ℕ}
    (center : Fin r → EuclideanSpace ℝ (Fin d))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (a : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin r) :=
  (WithLp.equiv 2 _).symm (fun i => (ℓ (a - center i)).toReal)

/-- A bounded uniformly-continuous loss has a uniformly-continuous finite
loss-profile map whose range lies in a compact finite cube.

The proof takes the coordinatewise loss profile and the closed cube supplied
by the common finite bound. -/
theorem finiteLossProfile_uniform_center {d r : ℕ}
    (center : Fin r → EuclideanSpace ℝ (Fin d))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (_hfinite : ∀ x, ℓ x ≠ ∞)
    (_hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (_huc : UniformContinuous fun x => (ℓ x).toReal) :
    UniformContinuous (finiteLossProfile center ℓ) ∧
      ∃ K : Set (EuclideanSpace ℝ (Fin r)), IsCompact K ∧
        Set.range (finiteLossProfile center ℓ) ⊆ K := by
  obtain ⟨B, hBtop, hB⟩ := _hbdd
  have hBreal : ∀ x, (ℓ x).toReal ≤ B.toReal := by
    intro x
    exact (ENNReal.toReal_le_toReal (_hfinite x) hBtop.ne).2 (hB x)
  have hcoord : ∀ i : Fin r,
      UniformContinuous fun a : EuclideanSpace ℝ (Fin d) =>
        (ℓ (a - center i)).toReal := by
    intro i
    exact _huc.comp (uniformContinuous_id.sub uniformContinuous_const)
  have hprofile : UniformContinuous (finiteLossProfile center ℓ) := by
    unfold finiteLossProfile
    exact (PiLp.uniformContinuous_toLp 2 (fun _ : Fin r => ℝ)).comp
      (uniformContinuous_pi.mpr hcoord)
  let Q : Set (Fin r → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 0 B.toReal)
  let K : Set (EuclideanSpace ℝ (Fin r)) :=
    (PiLp.homeomorph 2 (fun _ : Fin r => ℝ)).symm '' Q
  have hQ : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have hK : IsCompact K :=
    hQ.image (PiLp.homeomorph 2 (fun _ : Fin r => ℝ)).symm.continuous
  refine ⟨hprofile, K, hK, ?_⟩
  rintro _ ⟨a, rfl⟩
  refine ⟨fun i => (ℓ (a - center i)).toReal, ?_, rfl⟩
  intro i _
  exact ⟨ENNReal.toReal_nonneg, hBreal _⟩

/-- Joint weak convergence with a fixed first marginal transfers through any
absolutely-continuous change of that marginal.  The proof approximates the
Radon--Nikodym density in `L¹` by bounded continuous functions. -/
private theorem weakConverges_bind_of_compProd
    {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X]
    [MeasurableSpace Y] [PseudoMetricSpace Y] [BorelSpace Y]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [nu.WeaklyRegular] (hmunu : mu ≪ nu)
    (etaN : ℕ → Kernel X Y) [∀ n, IsMarkovKernel (etaN n)]
    (eta : Kernel X Y) [IsMarkovKernel eta]
    (hjoint : WeakConverges (fun n => nu ⊗ₘ etaN n) (nu ⊗ₘ eta)) :
    WeakConverges (fun n => mu.bind (etaN n)) (mu.bind eta) := by
  intro g
  let p : X → ℝ := fun x => (mu.rnDeriv nu x).toReal
  have hp : Integrable p nu := by
    simpa [p] using (Measure.integrable_toReal_rnDeriv (μ := mu) (ν := nu))
  have hbind_weighted (zeta : Kernel X Y) [IsMarkovKernel zeta] :
      ∫ y, g y ∂(mu.bind zeta) =
        ∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ zeta) := by
    have hmap : ∫ y, g y ∂(mu.bind zeta) =
        ∫ z, g z.2 ∂(mu ⊗ₘ zeta) := by
      rw [← Measure.snd_compProd mu zeta, Measure.snd]
      exact MeasureTheory.integral_map measurable_snd.aemeasurable
        g.continuous.aestronglyMeasurable
    have hrn := ProbabilityTheory.rnDeriv_measure_compProd_left mu nu zeta
    calc
      ∫ y, g y ∂(mu.bind zeta) = ∫ z, g z.2 ∂(mu ⊗ₘ zeta) := hmap
      _ = ∫ z, ((mu ⊗ₘ zeta).rnDeriv (nu ⊗ₘ zeta) z).toReal * g z.2
          ∂(nu ⊗ₘ zeta) := by
        simpa [smul_eq_mul] using
          (MeasureTheory.integral_rnDeriv_smul
            (hmunu.compProd_left zeta) (f := fun z : X × Y => g z.2)).symm
      _ = ∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ zeta) := by
        apply integral_congr_ae
        filter_upwards [hrn] with z hz
        simp only [hz, p]
  rw [Metric.tendsto_atTop]
  intro e he
  let delta : ℝ := e / (4 * (‖g‖ + 1))
  have hdelta : 0 < delta := by positivity
  obtain ⟨h, hh, _hhInt⟩ := hp.exists_boundedContinuous_integral_sub_le hdelta
  let gh : BoundedContinuousFunction (X × Y) ℝ :=
    (h.compContinuous ⟨Prod.fst, continuous_fst⟩) *
      (g.compContinuous ⟨Prod.snd, continuous_snd⟩)
  have hconv := hjoint gh
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv (e / 4) (by positivity)
  refine ⟨N, fun n hnN => ?_⟩
  have hn := hN n hnN
  have herror (zeta : Kernel X Y) [IsMarkovKernel zeta] :
      |∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ zeta) -
          ∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ zeta)|
        ≤ ‖g‖ * ∫ x, ‖p x - h x‖ ∂nu := by
    have hlift (q : X → ℝ) (hq : Integrable q nu) :
        Integrable (fun z : X × Y => q z.1) (nu ⊗ₘ zeta) := by
      have hfst : (nu ⊗ₘ zeta).map Prod.fst = nu := by
        change (nu ⊗ₘ zeta).fst = nu
        exact Measure.fst_compProd nu zeta
      have hq' : Integrable q ((nu ⊗ₘ zeta).map Prod.fst) := by
        rw [hfst]
        exact hq
      exact (integrable_map_measure hq'.aestronglyMeasurable
        measurable_fst.aemeasurable).mp hq'
    have hpLift := hlift p hp
    have hhLift := hlift (fun x => h x) (h.integrable nu)
    have hgMeas : AEStronglyMeasurable (fun z : X × Y => g z.2)
        (nu ⊗ₘ zeta) :=
      (g.continuous.measurable.comp measurable_snd).aestronglyMeasurable
    have hpg : Integrable (fun z : X × Y => p z.1 * g z.2) (nu ⊗ₘ zeta) :=
      hpLift.mul_bdd hgMeas (Eventually.of_forall fun z => g.norm_coe_le_norm z.2)
    have hhg : Integrable (fun z : X × Y => h z.1 * g z.2) (nu ⊗ₘ zeta) :=
      hhLift.mul_bdd hgMeas (Eventually.of_forall fun z => g.norm_coe_le_norm z.2)
    have hq : Integrable (fun x => p x - h x) nu := hp.sub (h.integrable nu)
    have hboundInt : Integrable
        (fun z : X × Y => ‖g‖ * ‖p z.1 - h z.1‖) (nu ⊗ₘ zeta) :=
      (hlift (fun x => p x - h x) hq).norm.const_mul ‖g‖
    calc
      |∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ zeta) -
          ∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ zeta)|
          = ‖∫ z, p z.1 * g z.2 - h z.1 * g z.2 ∂(nu ⊗ₘ zeta)‖ := by
            rw [integral_sub hpg hhg, Real.norm_eq_abs]
      _ ≤ ∫ z, ‖g‖ * ‖p z.1 - h z.1‖ ∂(nu ⊗ₘ zeta) := by
        apply norm_integral_le_of_norm_le hboundInt
        exact Eventually.of_forall fun z => by
          rw [← sub_mul]
          calc
            ‖(p z.1 - h z.1) * g z.2‖ = ‖p z.1 - h z.1‖ * ‖g z.2‖ := norm_mul _ _
            _ ≤ ‖p z.1 - h z.1‖ * ‖g‖ :=
              mul_le_mul_of_nonneg_left (g.norm_coe_le_norm z.2) (norm_nonneg _)
            _ = ‖g‖ * ‖p z.1 - h z.1‖ := mul_comm _ _
      _ = ‖g‖ * ∫ x, ‖p x - h x‖ ∂nu := by
        rw [integral_const_mul]
        have hfst : (nu ⊗ₘ zeta).map Prod.fst = nu := by
          change (nu ⊗ₘ zeta).fst = nu
          exact Measure.fst_compProd nu zeta
        have hqmap : Integrable (fun x => ‖p x - h x‖)
            ((nu ⊗ₘ zeta).map Prod.fst) := by
          rw [hfst]
          exact hq.norm
        have hm := MeasureTheory.integral_map (μ := nu ⊗ₘ zeta)
          (f := fun x : X => ‖p x - h x‖) measurable_fst.aemeasurable
          hqmap.aestronglyMeasurable
        rw [hfst] at hm
        exact congrArg (‖g‖ * ·) hm.symm
  have herrlt : ‖g‖ * ∫ x, ‖p x - h x‖ ∂nu < e / 4 := by
    calc
      ‖g‖ * ∫ x, ‖p x - h x‖ ∂nu ≤ ‖g‖ * delta :=
        mul_le_mul_of_nonneg_left hh (norm_nonneg g)
      _ < (‖g‖ + 1) * delta :=
        mul_lt_mul_of_pos_right (lt_add_one ‖g‖) hdelta
      _ = e / 4 := by
        dsimp [delta]
        field_simp
  rw [hbind_weighted (etaN n), hbind_weighted eta]
  change |∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ etaN n) -
      ∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ eta)| < e
  have hn : |∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ etaN n) -
      ∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ eta)| < e / 4 := by
    simpa [gh, Real.dist_eq] using hn
  calc
    |∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ etaN n) -
        ∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ eta)|
      ≤ |∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ etaN n) -
          ∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ etaN n)| +
        |∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ etaN n) -
          ∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ eta)| +
        |∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ eta) -
          ∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ eta)| := by
        calc
          _ ≤ |∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ etaN n) -
                ∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ etaN n)| +
              |∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ etaN n) -
                ∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ eta)| := abs_sub_le _ _ _
          _ ≤ |∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ etaN n) -
                ∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ etaN n)| +
              (|∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ etaN n) -
                  ∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ eta)| +
                |∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ eta) -
                  ∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ eta)|) := by
            apply add_le_add_right
            exact abs_sub_le
              (∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ etaN n))
              (∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ eta))
              (∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ eta))
          _ = _ := by ring
    _ < e := by
      have hleft := lt_of_le_of_lt (herror (etaN n)) herrlt
      have hright : |∫ z, h z.1 * g z.2 ∂(nu ⊗ₘ eta) -
          ∫ z, p z.1 * g z.2 ∂(nu ⊗ₘ eta)| < e / 4 := by
        rw [abs_sub_comm]
        exact lt_of_le_of_lt (herror eta) herrlt
      linarith

/-- For a fixed finite experiment, a sequence of action kernels has a joint
subsequence whose finite loss profiles are represented by one Markov kernel
into a compact profile cube.

The proof dominates the finitely many source laws by their uniform mixture,
extract the joint weak subsequence, and disintegrate its limit. -/
theorem finiteLossProfile_kernel_subsequence {m d r : ℕ}
    (μ : Fin r → Measure (EuclideanSpace ℝ (Fin m)))
    (_hprob : ∀ i, IsProbabilityMeasure (μ i))
    (center : Fin r → EuclideanSpace ℝ (Fin d))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (_hfinite : ∀ x, ℓ x ≠ ∞)
    (_hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (_huc : UniformContinuous fun x => (ℓ x).toReal)
    (K : Set (EuclideanSpace ℝ (Fin r))) (_hK : IsCompact K)
    (_hrange : Set.range (finiteLossProfile center ℓ) ⊆ K)
    (κn : ℕ → MarkovDecision (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin d))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∃ κProfile : MarkovDecision (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin r)),
        (∀ i, AsymptoticStatistics.WeakConverges
          (fun k => ((μ i).bind (κn (ns k)).1).map
            (finiteLossProfile center ℓ))
          ((μ i).bind κProfile.1)) ∧
        ∀ i, ((μ i).bind κProfile.1) K = 1 := by
  classical
  by_cases hr : r = 0
  · subst r
    let eta : Kernel (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 0)) :=
      Kernel.deterministic (fun _ => 0) measurable_const
    haveI : IsMarkovKernel eta := by dsimp [eta]; infer_instance
    refine ⟨id, strictMono_id, ⟨eta, inferInstance⟩, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  · letI hmuProb (i : Fin r) : IsProbabilityMeasure (μ i) := _hprob i
    letI hkappaN (n : ℕ) : IsMarkovKernel (κn n).1 := (κn n).2
    let profile := finiteLossProfile center ℓ
    have hprofile : Measurable profile := by
      exact (finiteLossProfile_uniform_center center ℓ _hfinite _hbdd _huc).1.continuous.measurable
    let etaN : ℕ → Kernel (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin r)) := fun n => (κn n).1.map profile
    letI hetaN (n : ℕ) : IsMarkovKernel (etaN n) := by
      dsimp [etaN]
      exact Kernel.IsMarkovKernel.map (κn n).1 hprofile
    let nu : Measure (EuclideanSpace ℝ (Fin m)) :=
      (r : ℝ≥0)⁻¹ • ∑ i, μ i
    haveI hnuProb : IsProbabilityMeasure nu := by
      refine ⟨?_⟩
      change (((r : ℝ≥0)⁻¹ • ∑ i, μ i) Set.univ) = 1
      rw [Measure.smul_apply]
      rw [ENNReal.smul_def, smul_eq_mul]
      have hsum : (∑ i, μ i) Set.univ = (r : ℝ≥0∞) := by
        rw [Measure.finset_sum_apply]
        simp only [measure_univ, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one, Fintype.card_fin]
      rw [hsum]
      rw [ENNReal.coe_inv (Nat.cast_ne_zero.mpr hr)]
      exact ENNReal.inv_mul_cancel
        (show (r : ℝ≥0∞) ≠ 0 by exact_mod_cast hr)
        (show (r : ℝ≥0∞) ≠ ∞ by exact ENNReal.natCast_ne_top r)
    have hscale : (r : ℝ≥0) • nu = ∑ i, μ i := by
      have hrNN : (r : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hr
      ext s
      simp [nu, Measure.smul_apply, hrNN]
    have hmuNu (i : Fin r) : μ i ≪ nu := by
      intro s hs
      have hle : μ i ≤ ∑ j, μ j :=
        Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
      have hsumZero : (∑ j, μ j) s = 0 := by
        rw [← hscale, Measure.smul_apply, hs]
        simp
      exact bot_unique ((hle s).trans_eq hsumZero)
    let joint : ℕ → Measure
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin r)) :=
      fun n => nu ⊗ₘ etaN n
    letI hjointProb (n : ℕ) : IsProbabilityMeasure (joint n) := by
      dsimp [joint]
      infer_instance
    have hfst (n : ℕ) : (joint n).map Prod.fst = nu := by
      change (joint n).fst = nu
      dsimp [joint]
      exact Measure.fst_compProd nu (etaN n)
    have hsnd (n : ℕ) : (joint n).map Prod.snd = nu.bind (etaN n) := by
      change (joint n).snd = nu.bind (etaN n)
      dsimp [joint]
      exact Measure.snd_compProd nu (etaN n)
    have hpreimage : profile ⁻¹' K = Set.univ := by
      apply Set.eq_univ_of_forall
      intro a
      exact _hrange ⟨a, rfl⟩
    have hsndK (n : ℕ) : ((joint n).map Prod.snd) K = 1 := by
      rw [hsnd]
      change (nu.bind ((κn n).1.map profile)) K = 1
      rw [← Measure.map_comp nu (κn n).1 hprofile]
      rw [Measure.map_apply hprofile _hK.measurableSet, hpreimage]
      simp
    have hfstTight : IsTightMeasureSet
        ((fun rho : Measure (EuclideanSpace ℝ (Fin m) ×
          EuclideanSpace ℝ (Fin r)) => rho.map Prod.fst) '' Set.range joint) := by
      rw [show (fun rho : Measure (EuclideanSpace ℝ (Fin m) ×
          EuclideanSpace ℝ (Fin r)) => rho.map Prod.fst) '' Set.range joint = {nu} by
        ext rho
        constructor
        · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
          exact Set.mem_singleton_iff.mpr (hfst n)
        · intro hrho
          rw [Set.mem_singleton_iff] at hrho
          subst rho
          exact ⟨joint 0, ⟨0, rfl⟩, hfst 0⟩]
      exact isTightMeasureSet_singleton
    have hsndTight : IsTightMeasureSet
        ((fun rho : Measure (EuclideanSpace ℝ (Fin m) ×
          EuclideanSpace ℝ (Fin r)) => rho.map Prod.snd) '' Set.range joint) := by
      rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
      intro e he
      refine ⟨K, _hK, ?_⟩
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      letI : IsProbabilityMeasure ((joint n).map Prod.snd) :=
        Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
      rw [(prob_compl_eq_zero_iff _hK.measurableSet).2 (hsndK n)]
      exact bot_le
    have hjointTight : IsTightMeasureSet (Set.range joint) :=
      Prohorov.tight_prod_of_tight_marginals _ hfstTight hsndTight
    obtain ⟨ns, hns, rho, hrhoProb₀, hrhoWeak⟩ :=
      Prohorov.extract_weak_subseq joint hjointTight
    letI hrhoProb : IsProbabilityMeasure rho := hrhoProb₀
    have hfstConst : WeakConverges
        (fun k => (joint (ns k)).map Prod.fst) nu := by
      intro f
      simp_rw [hfst]
      exact tendsto_const_nhds
    have hrhoFst : rho.fst = nu := by
      change rho.map Prod.fst = nu
      exact WeakConverges.unique
        (hrhoWeak.map continuous_fst measurable_fst) hfstConst
    let eta : Kernel (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin r)) := rho.condKernel
    haveI heta : IsMarkovKernel eta := by
      dsimp [eta]
      infer_instance
    have hdisintegrate : nu ⊗ₘ eta = rho := by
      rw [← hrhoFst]
      exact Measure.IsCondKernel.disintegrate
    have hjointLimit : WeakConverges
        (fun k => nu ⊗ₘ etaN (ns k)) (nu ⊗ₘ eta) := by
      simpa [joint, hdisintegrate] using hrhoWeak
    have hrhoSndK : rho.snd K = 1 := by
      let Pn : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin r)) :=
        fun k => ⟨(joint (ns k)).map Prod.snd,
          Measure.isProbabilityMeasure_map measurable_snd.aemeasurable⟩
      let P : ProbabilityMeasure (EuclideanSpace ℝ (Fin r)) :=
        ⟨rho.map Prod.snd,
          Measure.isProbabilityMeasure_map measurable_snd.aemeasurable⟩
      have hsndWeak := hrhoWeak.map continuous_snd measurable_snd
      have htend : Tendsto Pn atTop (nhds P) := by
        apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
        simpa [Pn, P] using! hsndWeak
      have hclosed :=
        ProbabilityMeasure.limsup_measure_closed_le_of_tendsto htend _hK.isClosed
      have hlimsup : limsup (fun k => ((Pn k : ProbabilityMeasure
          (EuclideanSpace ℝ (Fin r))) : Measure _) K) atTop = 1 := by
        simp [Pn, hsndK]
      have hone : (1 : ℝ≥0∞) ≤ (rho.map Prod.snd) K := by
        simpa [P, hlimsup] using hclosed
      change (rho.map Prod.snd) K = 1
      have hle : (rho.map Prod.snd) K ≤ (rho.map Prod.snd) Set.univ :=
        measure_mono (Set.subset_univ K)
      have huniv : (rho.map Prod.snd) Set.univ = 1 := by
        rw [Measure.map_apply measurable_snd MeasurableSet.univ]
        exact IsProbabilityMeasure.measure_univ
      exact le_antisymm (hle.trans_eq huniv) hone
    have hnuEtaK : (nu.bind eta) K = 1 := by
      rw [← Measure.snd_compProd nu eta, hdisintegrate]
      exact hrhoSndK
    refine ⟨ns, hns, ⟨eta, inferInstance⟩, ?_, ?_⟩
    · intro i
      have hi := weakConverges_bind_of_compProd (μ i) nu (hmuNu i)
        (fun k => etaN (ns k)) eta hjointLimit
      convert! hi using 1
      funext k
      dsimp [etaN]
      exact Measure.map_comp (μ i) (κn (ns k)).1 hprofile
    · intro i
      have hac : (μ i).bind eta ≪ nu.bind eta := (hmuNu i).comp_right eta
      have hzeroNu : (nu.bind eta) Kᶜ = 0 :=
        (prob_compl_eq_zero_iff _hK.measurableSet).2 hnuEtaK
      exact (prob_compl_eq_zero_iff _hK.measurableSet).1 (hac hzeroNu)

/-- A finite family of genuine profile points admits a Borel rounding map to
corresponding actions. -/
private theorem exists_measurable_rounding_of_finite_cover
    {A Y : Type*} [MeasurableSpace A] [Nonempty A]
    [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (profile : A → Y) (t : Set Y) (ht : t.Finite)
    (htRange : t ⊆ Set.range profile) (e : ℝ) :
    ∃ q : Y → A, Measurable q ∧
      ∀ z, z ∈ ⋃ y ∈ t, Metric.ball y e → dist z (profile (q z)) < e := by
  classical
  induction t, ht using Set.Finite.induction_on with
  | empty =>
      refine ⟨fun _ => Classical.arbitrary A, measurable_const, ?_⟩
      simp
  | @insert y s hy hs ih =>
      obtain ⟨ay, hay⟩ := htRange (Set.mem_insert y s)
      obtain ⟨q, hq, hqRound⟩ := ih (fun z hz => htRange (Set.mem_insert_of_mem y hz))
      let q' : Y → A := fun z => if z ∈ Metric.ball y e then ay else q z
      have hq' : Measurable q' := by
        exact Measurable.ite Metric.isOpen_ball.measurableSet measurable_const hq
      refine ⟨q', hq', ?_⟩
      intro z hz
      by_cases hzy : z ∈ Metric.ball y e
      · change dist z (profile (if z ∈ Metric.ball y e then ay else q z)) < e
        rw [if_pos hzy, hay]
        exact hzy
      · have hz' : z ∈ ⋃ x ∈ s, Metric.ball x e := by
          simpa [hzy] using hz
        change dist z (profile (if z ∈ Metric.ball y e then ay else q z)) < e
        rw [if_neg hzy]
        exact hqRound z hz'

/-- A compact profile-valued Markov kernel supported on the closure of genuine
action profiles can be approximated, simultaneously for the finite experiment,
by one action-valued Markov kernel.

The proof chooses a finite net in the genuine profile range and measurably
round the profile kernel to corresponding actions. -/
theorem actionKernel_approx_of_lossProfileKernel {m d r : ℕ}
    (μ : Fin r → Measure (EuclideanSpace ℝ (Fin m)))
    (_hprob : ∀ i, IsProbabilityMeasure (μ i))
    (center : Fin r → EuclideanSpace ℝ (Fin d))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (_hfinite : ∀ x, ℓ x ≠ ∞)
    (_hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (_huc : UniformContinuous fun x => (ℓ x).toReal)
    (κProfile : MarkovDecision (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin r)))
    (_hsupp : ∀ i, ((μ i).bind κProfile.1)
      (closure (Set.range (finiteLossProfile center ℓ))) = 1)
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ κ : MarkovDecision (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin d)),
      ∀ i j,
        |(∫ z, z j ∂((μ i).bind κProfile.1)) -
          ∫ a, (ℓ (a - center j)).toReal ∂((μ i).bind κ.1)| < ε := by
  classical
  letI hμprob (i : Fin r) : IsProbabilityMeasure (μ i) := _hprob i
  letI hκProfile : IsMarkovKernel κProfile.1 := κProfile.2
  let profile := finiteLossProfile center ℓ
  obtain ⟨hprofile_uc, K, hK, hprofileK⟩ :=
    finiteLossProfile_uniform_center center ℓ _hfinite _hbdd _huc
  have hclosureK : closure (Set.range profile) ⊆ K :=
    closure_minimal hprofileK hK.isClosed
  have hclosureCompact : IsCompact (closure (Set.range profile)) :=
    hK.of_isClosed_subset isClosed_closure hclosureK
  have hquarter : 0 < ε / 4 := by linarith
  obtain ⟨t, htRange, htFinite, htCover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure hclosureCompact hquarter
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨round, hroundMeas, hround⟩ :=
    exists_measurable_rounding_of_finite_cover profile t htFinite htRange (ε / 2)
  have hclosureCover : closure (Set.range profile) ⊆
      ⋃ y ∈ t, Metric.ball y (ε / 2) := by
    intro z hz
    obtain ⟨y, hyRange, hzy⟩ := Metric.mem_closure_iff.1 hz (ε / 4) hquarter
    have hyCover := htCover hyRange
    simp only [Set.mem_iUnion] at hyCover ⊢
    obtain ⟨c, hc, hyc⟩ := hyCover
    change dist y c < ε / 4 at hyc
    exact ⟨c, hc, lt_of_le_of_lt (dist_triangle z y c) (by linarith)⟩
  let κKernel : Kernel (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin d)) :=
    κProfile.1.map round
  haveI hκKernel : IsMarkovKernel κKernel :=
    Kernel.IsMarkovKernel.map κProfile.1 hroundMeas
  refine ⟨⟨κKernel, inferInstance⟩, ?_⟩
  intro i j
  let ρ : Measure (EuclideanSpace ℝ (Fin r)) := (μ i).bind κProfile.1
  haveI hρprob : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have hsupp_i : ∀ᵐ z ∂ρ, z ∈ closure (Set.range profile) := by
    apply (ae_mem_iff_measure_eq
      (isClosed_closure.measurableSet.nullMeasurableSet)).2
    simpa [ρ, profile] using _hsupp i
  have hdist_i : ∀ᵐ z ∂ρ, dist z (profile (round z)) ≤ ε / 2 := by
    filter_upwards [hsupp_i] with z hz
    exact (hround z (hclosureCover hz)).le
  have hcoord_i : ∀ᵐ z ∂ρ,
      |z j - (profile (round z)) j| ≤ ε / 2 := by
    filter_upwards [hdist_i] with z hz
    calc
      |z j - (profile (round z)) j|
          = ‖(z - profile (round z)) j‖ := by simp [Real.norm_eq_abs]
      _ ≤ ‖z - profile (round z)‖ := PiLp.norm_apply_le _ _
      _ = dist z (profile (round z)) := by rw [dist_eq_norm]
      _ ≤ ε / 2 := hz
  obtain ⟨B, hBtop, hB⟩ := _hbdd
  have hBreal : ∀ x, (ℓ x).toReal ≤ B.toReal := by
    intro x
    exact (ENNReal.toReal_le_toReal (_hfinite x) hBtop.ne).2 (hB x)
  have hprofile_bound : ∀ a k, |(profile a) k| ≤ B.toReal := by
    intro a k
    change |(ℓ (a - center k)).toReal| ≤ B.toReal
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact hBreal _
  have hclosure_bound : ∀ z ∈ closure (Set.range profile), |z j| ≤ B.toReal := by
    have hclosed : IsClosed {z : EuclideanSpace ℝ (Fin r) | |z j| ≤ B.toReal} :=
      isClosed_le (continuous_abs.comp
        (PiLp.continuous_apply 2 (fun _ : Fin r => ℝ) j)) continuous_const
    have hrange : Set.range profile ⊆
        {z : EuclideanSpace ℝ (Fin r) | |z j| ≤ B.toReal} := by
      rintro _ ⟨a, rfl⟩
      exact hprofile_bound a j
    exact fun z hz => closure_minimal hrange hclosed hz
  have hzInt : Integrable (fun z : EuclideanSpace ℝ (Fin r) => z j) ρ := by
    refine Integrable.of_bound
      (PiLp.continuous_apply 2 (fun _ : Fin r => ℝ) j).aestronglyMeasurable B.toReal ?_
    filter_upwards [hsupp_i] with z hz
    simpa [Real.norm_eq_abs] using hclosure_bound z hz
  have hroundInt : Integrable
      (fun z : EuclideanSpace ℝ (Fin r) => (ℓ (round z - center j)).toReal) ρ := by
    refine Integrable.of_bound
      ((_huc.continuous.measurable.comp
        (hroundMeas.sub measurable_const)).aestronglyMeasurable) B.toReal ?_
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact hBreal _
  have hsecond :
      ∫ a, (ℓ (a - center j)).toReal ∂((μ i).bind κKernel) =
        ∫ z, (ℓ (round z - center j)).toReal ∂ρ := by
    change ∫ a, (ℓ (a - center j)).toReal
        ∂((μ i).bind (κProfile.1.map round)) = _
    rw [← Measure.map_comp (μ i) κProfile.1 hroundMeas]
    change ∫ a, (ℓ (a - center j)).toReal ∂(ρ.map round) = _
    exact MeasureTheory.integral_map (f := fun a => (ℓ (a - center j)).toReal)
      hroundMeas.aemeasurable
      ((_huc.continuous.measurable.comp
        (measurable_id.sub measurable_const)).aestronglyMeasurable)
  rw [hsecond]
  change |∫ z, z j ∂ρ - ∫ z, (ℓ (round z - center j)).toReal ∂ρ| < ε
  rw [← integral_sub hzInt hroundInt]
  calc
    |∫ z, z j - (ℓ (round z - center j)).toReal ∂ρ|
        ≤ ∫ _ : EuclideanSpace ℝ (Fin r), ε / 2 ∂ρ := by
      have hdiff : ∀ᵐ z ∂ρ,
          ‖z j - (ℓ (round z - center j)).toReal‖ ≤ ε / 2 := by
        simpa [profile, Real.norm_eq_abs] using! hcoord_i
      exact norm_integral_le_of_norm_le (integrable_const (ε / 2)) hdiff
    _ = ε / 2 := by simp
    _ < ε := by linarith

end AsymptoticStatistics.Experiment.FiniteRiskCompactification
