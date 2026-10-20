module
public import StatLean.AsymptoticStatistics.Examples.MARMean.Model
public import StatLean.AsymptoticStatistics.ForMathlib.LpDominatedConvergence
public import StatLean.AsymptoticStatistics.Operators.CoarseningScoreIdentification
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.StrongLaw

@[expose] public section

/-!
# The concrete MAR observed tangent

This file realizes the concrete observation `(X,R,RY)` as the pushforward of
the latent full-data/kernel model on `(X × ℝ) × Bool`, then specializes the
maximal coarsening-score identification of vdV Theorem 25.40. It deliberately
introduces no tangent-identification field or hypothesis.

Reference: van der Vaart, *Asymptotic Statistics* (1998), §25.5.3,
Theorem 25.40 (p.380) and Example 25.43 (p.383).
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal
open AsymptoticStatistics.Core
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Operators.CAR
open AsymptoticStatistics.Operators.CoarseningScoreIdentification

namespace AsymptoticStatistics.Examples.MARMean

variable {X : Type*} [MeasurableSpace X]

/-- The concrete MAR observation map from latent `(X,Y)` and response indicator
`R` to `(X,R,RY)` (vdV Example 25.43).

Edge behavior: on the missing fibre `R = false`, the unobserved response is
replaced by the fixed junk value `0`; all public MAR formulas multiply it by
the response indicator. -/
def marObsMap (p : (X × ℝ) × Bool) : MARObs X :=
  ⟨p.1.1, p.2, if p.2 then p.1.2 else 0⟩

/-- Measurability of the concrete MAR observation map. -/
theorem measurable_marObsMap : Measurable (marObsMap (X := X)) := by
  rw [measurable_comap_iff]
  change Measurable fun p : (X × ℝ) × Bool =>
    (p.1.1, p.2, if p.2 then p.1.2 else 0)
  have hr : Measurable (fun p : (X × ℝ) × Bool => p.2) := measurable_snd
  have hx : Measurable (fun p : (X × ℝ) × Bool => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hry : Measurable (fun p : (X × ℝ) × Bool =>
      if p.2 = true then p.1.2 else 0) :=
    Measurable.ite (hr (MeasurableSet.singleton true)) measurable_fst.snd measurable_const
  exact Measurable.prodMk hx (Measurable.prodMk hr hry)

/-- The observed MAR law induced by a latent full-data law `Q` and response
kernel `r`, as the pushforward `(Q ⊗ₘ r).map marObsMap`.

Edge behavior is inherited from `marObsMap`: missing responses are recorded as
zero, while the latent response remains present in the full-data law. -/
noncomputable def marObsMeasure (Q : Measure (X × ℝ))
    (r : Kernel (X × ℝ) Bool) : Measure (MARObs X) :=
  (Q ⊗ₘ r).map marObsMap

/-- An induced MAR observed law is a probability measure whenever its latent
law is a probability measure and its response kernel is Markov. -/
noncomputable instance instIsProbabilityMeasureMarObsMeasure
    (Q : Measure (X × ℝ)) [IsProbabilityMeasure Q]
    (r : Kernel (X × ℝ) Bool) [IsMarkovKernel r] :
    IsProbabilityMeasure (marObsMeasure Q r) := by
  exact Measure.isProbabilityMeasure_map
    (measurable_marObsMap (X := X)).aemeasurable

/-- The genuine MAR kernel/propensity linkage: conditionally on latent
`(X,Y)=y`, the response probability is `π(y.1)`.

Constitutive (vdV Example 25.43 p.383): this relates the supplied response
kernel to the propensity and contains no tangent or score-space assertion. -/
def MARResponseKernel (π : X → ℝ) (r : Kernel (X × ℝ) Bool) : Prop :=
  ∀ y, (r y {true}).toReal = π y.1

/-- Under the MAR response-kernel linkage, the missing-response mass is
`1 - π(x)` on every latent fibre. -/
theorem MARResponseKernel.false_mass
    {r : Kernel (X × ℝ) Bool} [IsMarkovKernel r]
    {π : X → ℝ} (hπr : MARResponseKernel π r) (y : X × ℝ) :
    (r y {false}).toReal = 1 - π y.1 := by
  have hfalse : ({false} : Set Bool) = ({true} : Set Bool)ᶜ := by
    ext b
    cases b <;> simp
  rw [hfalse, prob_compl_eq_one_sub (MeasurableSet.singleton true),
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one, hπr y]

/-- Package one admissible Example-25.43 MAR coarsening score as a mean-zero
`L²` element of the induced observed law. -/
noncomputable def marMeanCoarseningCandidate
    (Q : Measure (X × ℝ)) [IsProbabilityMeasure Q]
    (r : Kernel (X × ℝ) Bool) [IsMarkovKernel r]
    (π : X → ℝ) (hπr : MARResponseKernel π r)
    (c : X → ℝ)
    (hc_int : Integrable (fun o : MARObs X ↦ c o.x) (marObsMeasure Q r))
    (hc_lp : MemLp (marMean_coarseningScore π c) 2 (marObsMeasure Q r)) :
    CandidateIF (marObsMeasure Q r) := by
  by_cases hc : Integrable (fun o : MARObs X ↦ c o.x) (marObsMeasure Q r)
  swap
  · exact (hc hc_int).elim
  refine
    { raw := marMean_coarseningScore π c
      memLp2 := hc_lp
      mean_zero := ?_ }
  have hmp : MeasurePreserving (marObsMap (X := X)) (Q ⊗ₘ r) (marObsMeasure Q r) :=
    ⟨measurable_marObsMap (X := X), rfl⟩
  have hscore_int :
      Integrable (marMean_coarseningScore π c ∘ marObsMap) (Q ⊗ₘ r) :=
    (hc_lp.comp_measurePreserving hmp).integrable one_le_two
  rw [marObsMeasure, integral_map (measurable_marObsMap (X := X)).aemeasurable
    hc_lp.aestronglyMeasurable]
  change ∫ x, (marMean_coarseningScore π c ∘ marObsMap) x ∂(Q ⊗ₘ r) = 0
  rw [Measure.integral_compProd hscore_int]
  have hfibre : ∀ y : X × ℝ,
      ∫ b, (marMean_coarseningScore π c ∘ marObsMap) (y, b) ∂(r y) = 0 := by
    intro y
    rw [integral_fintype Integrable.of_finite]
    rw [Fintype.sum_bool]
    simp only [Function.comp_apply, Measure.real, marMean_coarseningScore, marObsMap,
      ind_false, ind_true, if_true, MARResponseKernel.false_mass hπr y,
      hπr y, smul_eq_mul]
    by_cases hπ : π y.1 = 0
    · simp [hπ]
    · field_simp
      ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hfibre), integral_zero]

/-- The closed span of all admissible concrete MAR coarsening scores
`((R-π)/π)c(X)` from vdV Example 25.43.

Edge behavior: degenerate fibres with `π=0` or `π=1` are retained; their
null response atom is handled in `L²` rather than excluded by a positivity
hypothesis. -/
noncomputable def marMeanCoarseningSpace
    (Q : Measure (X × ℝ)) [IsProbabilityMeasure Q]
    (r : Kernel (X × ℝ) Bool) [IsMarkovKernel r]
    (π : X → ℝ) (hπr : MARResponseKernel π r) :
    Submodule ℝ ↥(L2ZeroMean (marObsMeasure Q r)) :=
  (Submodule.span ℝ {b | ∃ (c : X → ℝ)
      (hc_int : Integrable (fun o : MARObs X ↦ c o.x) (marObsMeasure Q r))
      (hc_lp : MemLp (marMean_coarseningScore π c) 2 (marObsMeasure Q r)),
      b = (marMeanCoarseningCandidate Q r π hπr c hc_int hc_lp).toL2ZeroMean}).topologicalClosure

/-- The abstract fibre-mean-zero coarsening space for the latent MAR model is
exactly the closed span of the concrete Example-25.43 scores.

The difficult reverse inclusion uses bounded clipping of the recovered
covariate function and dominated `L²` convergence; it does not assume a
quantitative upper bound away from `π=1`. -/
theorem concreteCoarseningScores_eq_marMeanCoarseningSpace
    (Q : Measure (X × ℝ)) [IsProbabilityMeasure Q]
    (r : Kernel (X × ℝ) Bool) [IsMarkovKernel r]
    (π : X → ℝ) (hπr : MARResponseKernel π r)
    (hπ : ∀ x, π x ≠ 0) :
    concreteCoarseningScores Q r (measurable_marObsMap (X := X))
      = marMeanCoarseningSpace Q r π hπr := by
  have he : Measurable (fun o : MARObs X => (o.x, o.r, o.ry)) := by
    rw [measurable_iff_comap_le]
    exact le_rfl
  have hx : Measurable (fun o : MARObs X => o.x) := measurable_fst.comp he
  have hr : Measurable (fun o : MARObs X => o.r) :=
    measurable_fst.comp (measurable_snd.comp he)
  have hπ_meas : Measurable π := by
    have hr' : Measurable (fun y : X × ℝ => (r y {true}).toReal) :=
      (r.measurable_coe (MeasurableSet.singleton true)).ennreal_toReal
    have hcomp : Measurable (fun x : X => (r (x, 0) {true}).toReal) :=
      hr'.comp (by fun_prop)
    have heq : (fun x : X => (r (x, 0) {true}).toReal) = π :=
      funext fun x => hπr (x, 0)
    rw [← heq]
    exact hcomp
  have recoveredScore_ae
      (b : ↥(L2ZeroMean (marObsMeasure Q r)))
      (hb : b ∈ concreteCoarseningScores Q r (measurable_marObsMap (X := X))) :
      let c : X → ℝ := fun x =>
        -((b : Lp ℝ 2 (marObsMeasure Q r)) : MARObs X → ℝ) ⟨x, false, 0⟩
      marMean_coarseningScore π c =ᵐ[marObsMeasure Q r]
        ((b : Lp ℝ 2 (marObsMeasure Q r)) : MARObs X → ℝ) := by
    let braw : MARObs X → ℝ :=
      ((b : Lp ℝ 2 (marObsMeasure Q r)) : MARObs X → ℝ)
    let c : X → ℝ := fun x => -braw ⟨x, false, 0⟩
    have hb_fibre : ∀ᵐ y ∂Q, ∫ δ, braw (marObsMap (y, δ)) ∂(r y) = 0 := by
      simpa only [braw, marObsMeasure] using
        (mem_concreteCoarseningScores_iff Q r (measurable_marObsMap (X := X)) b).1 hb
    have hfun : (fun y : X × ℝ => fun δ =>
        marMean_coarseningScore π c (marObsMap (y, δ))) =ᵐ[Q]
        fun y => fun δ => braw (marObsMap (y, δ)) := by
      filter_upwards [hb_fibre] with y hy
      rw [integral_fintype Integrable.of_finite, Fintype.sum_bool] at hy
      simp only [Measure.real, smul_eq_mul] at hy
      rw [hπr y, hπr.false_mass y] at hy
      funext δ
      cases δ
      · simp only [marObsMap, marMean_coarseningScore, ind_false, c]
        field_simp [hπ y.1]
        simp only [Bool.false_eq_true, if_false]
        ring
      · simp only [marObsMap, if_true, marMean_coarseningScore, ind_true, c] at ⊢ hy
        simp only [Bool.false_eq_true, if_false] at ⊢ hy
        field_simp [hπ y.1]
        linear_combination -hy
    have hfst : MeasurePreserving (Prod.fst : (X × ℝ) × Bool → X × ℝ)
        (Q ⊗ₘ r) Q := ⟨measurable_fst, Measure.fst_compProd Q r⟩
    have hlift := hfst.quasiMeasurePreserving.ae_eq_comp hfun
    have hpull : (fun p : (X × ℝ) × Bool =>
        marMean_coarseningScore π c (marObsMap p)) =ᵐ[Q ⊗ₘ r]
        fun p => braw (marObsMap p) := by
      filter_upwards [hlift] with p hp
      exact congrFun hp p.2
    have hbraw_meas : StronglyMeasurable braw := by
      simpa only [braw] using Lp.stronglyMeasurable (b : Lp ℝ 2 (marObsMeasure Q r))
    have hc_meas : StronglyMeasurable c := by
      have hmiss : Measurable (fun x : X => (⟨x, false, 0⟩ : MARObs X)) := by
        rw [measurable_iff_comap_le]
        unfold instMeasurableSpaceMARObs
        rw [MeasurableSpace.comap_comp]
        exact (by fun_prop : Measurable (fun x : X => (x, false, (0 : ℝ)))).comap_le
      exact (hbraw_meas.comp_measurable hmiss).neg
    have hscore_meas : Measurable (marMean_coarseningScore π c) := by
      unfold marMean_coarseningScore
      exact ((((measurable_of_finite ind).comp hr).sub (hπ_meas.comp hx)).div
        (hπ_meas.comp hx)).mul (hc_meas.measurable.comp hx)
    have hmap : marMean_coarseningScore π c =ᵐ[(Q ⊗ₘ r).map marObsMap] braw := by
      rw [Filter.EventuallyEq, ae_map_iff (measurable_marObsMap (X := X)).aemeasurable
        (measurableSet_eq_fun hscore_meas hbraw_meas.measurable)]
      simpa only using! hpull
    simpa only [marObsMeasure] using! hmap
  apply le_antisymm
  · intro b hb
    let b0 : ↥(L2ZeroMean (marObsMeasure Q r)) := by
      simpa only [marObsMeasure] using! b
    have hb0 : b0 ∈ concreteCoarseningScores Q r
        (measurable_marObsMap (X := X)) := by
      simpa only [b0, marObsMeasure] using! hb
    let braw : MARObs X → ℝ :=
      ((b0 : Lp ℝ 2 (marObsMeasure Q r)) : MARObs X → ℝ)
    let c : X → ℝ := fun x => -braw ⟨x, false, 0⟩
    let u : MARObs X → ℝ := marMean_coarseningScore π c
    let cn : ℕ → X → ℝ := fun n => truncation c (n : ℝ)
    let un : ℕ → MARObs X → ℝ := fun n => marMean_coarseningScore π (cn n)
    have hraw : u =ᵐ[marObsMeasure Q r] braw := by
      simpa only [u, c, braw] using recoveredScore_ae b0 hb0
    have hbraw_mem : MemLp braw 2 (marObsMeasure Q r) := by
      simpa only [braw] using Lp.memLp (b0 : Lp ℝ 2 (marObsMeasure Q r))
    have hu_mem : MemLp u 2 (marObsMeasure Q r) := hbraw_mem.ae_eq hraw.symm
    have hbraw_meas : StronglyMeasurable braw := by
      simpa only [braw] using Lp.stronglyMeasurable (b0 : Lp ℝ 2 (marObsMeasure Q r))
    have hc_meas : StronglyMeasurable c := by
      have hmiss : Measurable (fun x : X => (⟨x, false, 0⟩ : MARObs X)) := by
        rw [measurable_iff_comap_le]
        unfold instMeasurableSpaceMARObs
        rw [MeasurableSpace.comap_comp]
        exact (by fun_prop : Measurable (fun x : X => (x, false, (0 : ℝ)))).comap_le
      exact (hbraw_meas.comp_measurable hmiss).neg
    have hcn_int : ∀ n, Integrable (fun o : MARObs X => cn n o.x)
        (marObsMeasure Q r) := by
      intro n
      exact (hc_meas.comp_measurable hx).aestronglyMeasurable.integrable_truncation
    have hun_meas : ∀ n, AEStronglyMeasurable (un n) (marObsMeasure Q r) := by
      intro n
      unfold un marMean_coarseningScore
      exact (((((measurable_of_finite ind).comp hr).sub (hπ_meas.comp hx)).div
        (hπ_meas.comp hx)).aestronglyMeasurable.mul
          ((hc_meas.aestronglyMeasurable.truncation).comp_measurable hx))
    have hun_dom : ∀ n o, ‖un n o‖ ≤ ‖u o‖ := by
      intro n o
      simp only [un, u, cn, marMean_coarseningScore, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_truncation_le_abs_self c (n : ℝ) o.x)
        (abs_nonneg _)
    have hun_mem : ∀ n, MemLp (un n) 2 (marObsMeasure Q r) := by
      intro n
      exact hu_mem.of_le (hun_meas n) (Filter.Eventually.of_forall (hun_dom n))
    have hun_tend : ∀ o, Filter.Tendsto (fun n => un n o) Filter.atTop (nhds (u o)) := by
      intro o
      have hcn : Filter.Tendsto (fun n : ℕ => cn n o.x) Filter.atTop (nhds (c o.x)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop
          |c o.x|)] with n hn
        exact (truncation_eq_self hn).symm
      unfold un u marMean_coarseningScore
      exact tendsto_const_nhds.mul hcn
    have hnorm : Filter.Tendsto
        (fun n => eLpNorm (fun o => un n o - u o) 2 (marObsMeasure Q r))
        Filter.atTop (nhds 0) :=
      MeasureTheory.tendsto_eLpNorm_sub_zero_of_pointwise_of_memLp_dominator
        (marObsMeasure Q r) hun_meas hu_mem hun_dom hun_tend
    let cand : ℕ → ↥(L2ZeroMean (marObsMeasure Q r)) := fun n =>
      (marMeanCoarseningCandidate Q r π hπr (cn n) (hcn_int n) (hun_mem n)).toL2ZeroMean
    have hcand_tend : Filter.Tendsto cand Filter.atTop (nhds b0) := by
      rw [tendsto_subtype_rng, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
      convert hnorm using 1
      funext n
      apply eLpNorm_congr_ae
      have hcand_ae := CandidateIF.coeFn_toL2ZeroMean
        (marMeanCoarseningCandidate Q r π hπr (cn n) (hcn_int n) (hun_mem n))
      filter_upwards [hcand_ae, hraw] with o ho hbo
      simp only [Pi.sub_apply, cand] at ho ⊢
      rw [ho, hbo]
      simp only [marMeanCoarseningCandidate, hcn_int n, un, braw, ↓reduceDIte]
    unfold marMeanCoarseningSpace
    have hcand_mem : ∀ n, cand n ∈ Submodule.span ℝ
        {z : ↥(L2ZeroMean (marObsMeasure Q r)) | ∃ (c : X → ℝ)
          (hc_int : Integrable (fun o : MARObs X => c o.x) (marObsMeasure Q r))
          (hc_lp : MemLp (marMean_coarseningScore π c) 2 (marObsMeasure Q r)),
          z = (marMeanCoarseningCandidate Q r π hπr c hc_int hc_lp).toL2ZeroMean} := by
      intro n
      apply Submodule.subset_span
      exact ⟨cn n, hcn_int n, hun_mem n, rfl⟩
    have hb0_mem := mem_closure_of_tendsto hcand_tend
      (Filter.Eventually.of_forall hcand_mem)
    change b0 ∈ (Submodule.span ℝ
        {z : ↥(L2ZeroMean (marObsMeasure Q r)) | ∃ (c : X → ℝ)
          (hc_int : Integrable (fun o : MARObs X => c o.x) (marObsMeasure Q r))
          (hc_lp : MemLp (marMean_coarseningScore π c) 2 (marObsMeasure Q r)),
          z = (marMeanCoarseningCandidate Q r π hπr c hc_int hc_lp).toL2ZeroMean}
          ).topologicalClosure
    exact hb0_mem
  · unfold marMeanCoarseningSpace
    apply Submodule.topologicalClosure_minimal
    · refine Submodule.span_le.mpr ?_
      rintro b ⟨c, hc_int, hc_lp, rfl⟩
      have hcoe := CandidateIF.coeFn_toL2ZeroMean
        (marMeanCoarseningCandidate Q r π hπr c hc_int hc_lp)
      have hpull :
          (fun p : (X × ℝ) × Bool =>
            ((((marMeanCoarseningCandidate Q r π hπr c hc_int hc_lp).toL2ZeroMean :
                Lp ℝ 2 (marObsMeasure Q r)) : MARObs X → ℝ) (marObsMap p)))
            =ᵐ[Q ⊗ₘ r]
          fun p => marMean_coarseningScore π c (marObsMap p) := by
        unfold marObsMeasure at hcoe
        simpa only [Function.comp_apply, marMeanCoarseningCandidate, hc_int,
          ↓reduceDIte] using!
          ae_eq_comp (measurable_marObsMap (X := X)).aemeasurable hcoe
      have hfibre : ∀ᵐ y ∂Q,
          ∫ δ,
            ((((marMeanCoarseningCandidate Q r π hπr c hc_int hc_lp).toL2ZeroMean :
                Lp ℝ 2 (marObsMeasure Q r)) : MARObs X → ℝ)
              (marObsMap (y, δ))) ∂(r y) = 0 := by
        have hfib := Measure.ae_ae_of_ae_compProd hpull
        filter_upwards [hfib] with y hy
        calc
          ∫ δ,
              ((((marMeanCoarseningCandidate Q r π hπr c hc_int hc_lp).toL2ZeroMean :
                  Lp ℝ 2 (marObsMeasure Q r)) : MARObs X → ℝ)
                (marObsMap (y, δ))) ∂(r y) =
              ∫ δ, marMean_coarseningScore π c (marObsMap (y, δ)) ∂(r y) :=
            integral_congr_ae hy
          _ = 0 := by
            rw [integral_fintype Integrable.of_finite, Fintype.sum_bool]
            simp only [Measure.real, smul_eq_mul, marObsMap, marMean_coarseningScore,
              ind_true, ind_false, if_true]
            rw [hπr y, hπr.false_mass y]
            field_simp [hπ y.1]
            ring
      simpa only [marObsMeasure] using!
        (mem_concreteCoarseningScores_iff Q r (measurable_marObsMap (X := X))
          (marMeanCoarseningCandidate Q r π hπr c hc_int hc_lp).toL2ZeroMean).2 hfibre
    · have hc : IsClosed
          (↑(concreteCoarseningScores Q r (measurable_marObsMap (X := X))) :
            Set ↥(L2ZeroMean ((Q ⊗ₘ r).map marObsMap))) := by
        unfold concreteCoarseningScores
        exact ContinuousLinearMap.isClosed_ker _
      simpa only [marObsMeasure] using! hc

/-- The closed observed `Q`-tangent of the induced concrete MAR law, obtained
from the full latent `Q` tangent of vdV Theorem 25.40. -/
noncomputable def marObservedTangent
    (Q : Measure (X × ℝ)) [IsProbabilityMeasure Q]
    (r : Kernel (X × ℝ) Bool) [IsMarkovKernel r] :
    Submodule ℝ ↥(L2ZeroMean (marObsMeasure Q r)) :=
  (observedTangent (measurable_marObsMap (X := X)) (Q ⊗ₘ r)
    (fullQTangent Q r)).topologicalClosure

/-- Membership in the concrete closed MAR observed tangent is equivalent to
orthogonality against every admissible Example-25.43 coarsening score. -/
theorem mem_marObservedTangent_iff
    (Q : Measure (X × ℝ)) [IsProbabilityMeasure Q]
    (r : Kernel (X × ℝ) Bool) [IsMarkovKernel r]
    (π : X → ℝ) (hπr : MARResponseKernel π r)
    (hπ : ∀ x, π x ≠ 0)
    (w : ↥(L2ZeroMean (marObsMeasure Q r))) :
    w ∈ marObservedTangent Q r ↔
      ∀ (c : X → ℝ), Integrable (fun o : MARObs X ↦ c o.x) (marObsMeasure Q r) →
        MemLp (marMean_coarseningScore π c) 2 (marObsMeasure Q r) →
        ∫ o, ((w : Lp ℝ 2 (marObsMeasure Q r)) : MARObs X → ℝ) o
              * marMean_coarseningScore π c o ∂(marObsMeasure Q r) = 0 := by
  rw [marObservedTangent,
    closedObservedQTangent_eq_concreteOrthogonal Q r
      (measurable_marObsMap (X := X)),
    concreteCoarseningScores_eq_marMeanCoarseningSpace Q r π hπr hπ]
  unfold marMeanCoarseningSpace
  let G : Set ↥(L2ZeroMean (marObsMeasure Q r)) :=
    {b | ∃ (c : X → ℝ)
      (hc_int : Integrable (fun o : MARObs X => c o.x) (marObsMeasure Q r))
      (hc_lp : MemLp (marMean_coarseningScore π c) 2 (marObsMeasure Q r)),
      b = (marMeanCoarseningCandidate Q r π hπr c hc_int hc_lp).toL2ZeroMean}
  change w ∈ (Submodule.span ℝ G).topologicalClosureᗮ ↔ _
  have hcand_inner (c : X → ℝ)
      (hc_int : Integrable (fun o : MARObs X => c o.x) (marObsMeasure Q r))
      (hc_lp : MemLp (marMean_coarseningScore π c) 2 (marObsMeasure Q r)) :
      ⟪(marMeanCoarseningCandidate Q r π hπr c hc_int hc_lp).toL2ZeroMean, w⟫_ℝ =
        ∫ o, ((w : Lp ℝ 2 (marObsMeasure Q r)) : MARObs X → ℝ) o *
          marMean_coarseningScore π c o ∂(marObsMeasure Q r) := by
    change ⟪((marMeanCoarseningCandidate Q r π hπr c hc_int hc_lp).toL2ZeroMean :
      Lp ℝ 2 (marObsMeasure Q r)), (w : Lp ℝ 2 (marObsMeasure Q r))⟫_ℝ = _
    rw [L2.inner_def]
    apply integral_congr_ae
    have hcoe := CandidateIF.coeFn_toL2ZeroMean
      (marMeanCoarseningCandidate Q r π hπr c hc_int hc_lp)
    filter_upwards [hcoe] with o ho
    rw [ho]
    simp only [marMeanCoarseningCandidate, hc_int, ↓reduceDIte]
    rfl
  constructor
  · intro hw c hc_int hc_lp
    have hw_span : w ∈ (Submodule.span ℝ G)ᗮ :=
      Submodule.orthogonal_le (Submodule.le_topologicalClosure _) hw
    have hcand_mem :
        (marMeanCoarseningCandidate Q r π hπr c hc_int hc_lp).toL2ZeroMean ∈
          Submodule.span ℝ G :=
      Submodule.subset_span ⟨c, hc_int, hc_lp, rfl⟩
    have hinner := (Submodule.mem_orthogonal (Submodule.span ℝ G) w).1
      hw_span _ hcand_mem
    exact (hcand_inner c hc_int hc_lp).symm.trans hinner
  · intro h
    have hw_span : w ∈ (Submodule.span ℝ G)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro z hz
      refine Submodule.span_induction (p := fun z _ => ⟪z, w⟫_ℝ = 0)
        ?_ ?_ ?_ ?_ hz
      · intro z hzG
        rcases hzG with ⟨c, hc_int, hc_lp, rfl⟩
        rw [hcand_inner c hc_int hc_lp]
        exact h c hc_int hc_lp
      · change ⟪(0 : ↥(L2ZeroMean (marObsMeasure Q r))), w⟫_ℝ = 0
        exact inner_zero_left _
      · intro x y hx hy hx0 hy0
        calc
          ⟪x + y, w⟫_ℝ = ⟪x, w⟫_ℝ + ⟪y, w⟫_ℝ := inner_add_left _ _ _
          _ = 0 := by rw [hx0, hy0, add_zero]
      · intro a x hx hx0
        calc
          ⟪a • x, w⟫_ℝ = a * ⟪x, w⟫_ℝ := real_inner_smul_left x w a
          _ = 0 := by rw [hx0, mul_zero]
    rw [Submodule.mem_orthogonal] at hw_span ⊢
    exact (Submodule.orthogonal_closure' (Submodule.span ℝ G) w).1 hw_span

/-! ### Finite consistency witness for the latent bridge -/

/-- The fair probability law on `Bool`. -/
noncomputable def fairBoolMeasure : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

/-- The fair response kernel, constant in the latent datum. -/
noncomputable def fairBoolKernel : Kernel (Unit × ℝ) Bool :=
  Kernel.const (Unit × ℝ) fairBoolMeasure

noncomputable instance : IsMarkovKernel fairBoolKernel := by
  unfold fairBoolKernel fairBoolMeasure
  infer_instance

/-- The fair finite MAR model realizes the propensity `π ≡ 1/2`. -/
theorem fairBoolKernel_isMAR :
    MARResponseKernel (fun _ : Unit ↦ (1 / 2 : ℝ)) fairBoolKernel := by
  intro y
  simp [fairBoolKernel, fairBoolMeasure, Kernel.const_apply,
    PMF.uniformOfFintype_apply]

/-- Both the observed-response and missing-response atoms have positive mass
under the finite latent witness `Q = dirac ((),0)`. -/
theorem fairMAR_atoms_positive :
    let P := marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel
    0 < P {o : MARObs Unit | o.r = true} ∧
      0 < P {o : MARObs Unit | o.r = false} := by
  let obsCoords : MARObs Unit → Unit × Bool × ℝ := fun o ↦ (o.x, o.r, o.ry)
  have hcoords : Measurable obsCoords := comap_measurable obsCoords
  have hr : Measurable (fun o : MARObs Unit ↦ o.r) :=
    (measurable_fst.comp measurable_snd).comp hcoords
  have hatom (b : Bool) :
      marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel
          {o : MARObs Unit | o.r = b} = (1 / 2 : ℝ≥0∞) := by
    unfold marObsMeasure
    change ((Measure.dirac ((), (0 : ℝ)) ⊗ₘ fairBoolKernel).map marObsMap)
      ((fun o : MARObs Unit ↦ o.r) ⁻¹' {b}) = (1 / 2 : ℝ≥0∞)
    rw [Measure.map_apply (measurable_marObsMap (X := Unit))
      (hr (MeasurableSet.singleton b)),
      Measure.dirac_compProd_apply
        ((hr (MeasurableSet.singleton b)).preimage
          (measurable_marObsMap (X := Unit)))]
    cases b <;>
      simp [fairBoolKernel, fairBoolMeasure, Kernel.const_apply,
        PMF.uniformOfFintype_apply, marObsMap]
  constructor <;> rw [hatom] <;> norm_num

/-- The admissible concrete coarsening score generated by `c ≡ 1` is nonzero
under the fair finite MAR witness. -/
theorem fairMAR_coarseningScore_nonzero :
    let P := marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel
    ¬ (marMean_coarseningScore (fun _ : Unit ↦ (1 / 2 : ℝ)) (fun _ ↦ 1)
        =ᵐ[P] fun _ ↦ 0) := by
  dsimp only
  let P := marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel
  intro hzero
  have hbad : P {o : MARObs Unit |
      marMean_coarseningScore (fun _ : Unit ↦ (1 / 2 : ℝ)) (fun _ ↦ 1) o ≠ 0} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hzero] with o ho
    simpa using ho
  have hsub : {o : MARObs Unit | o.r = true} ⊆
      {o : MARObs Unit |
        marMean_coarseningScore (fun _ : Unit ↦ (1 / 2 : ℝ)) (fun _ ↦ 1) o ≠ 0} := by
    intro o ho
    change o.r = true at ho
    norm_num [marMean_coarseningScore, ho]
  have hmass : P {o : MARObs Unit | o.r = true} ≤
      P {o : MARObs Unit |
        marMean_coarseningScore (fun _ : Unit ↦ (1 / 2 : ℝ)) (fun _ ↦ 1) o ≠ 0} :=
    measure_mono hsub
  rw [hbad] at hmass
  have hpos : 0 < P {o : MARObs Unit | o.r = true} := by
    simpa only [P] using fairMAR_atoms_positive.1
  exact (not_lt_of_ge hmass) hpos

end AsymptoticStatistics.Examples.MARMean
