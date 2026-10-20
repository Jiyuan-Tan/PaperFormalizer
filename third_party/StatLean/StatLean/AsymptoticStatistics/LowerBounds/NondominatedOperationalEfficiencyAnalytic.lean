module
public import StatLean.AsymptoticStatistics.Core.NondominatedEfficiencyOperational
public import StatLean.AsymptoticStatistics.Core.Pathwise
public import StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianTiltRigidity
public import StatLean.AsymptoticStatistics.ForMathlib.Prohorov

@[expose] public section

/-! # Analytic core of nondominated operational efficiency -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

namespace AsymptoticStatistics.LowerBounds.NondominatedOperationalEfficiencyAnalytic

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.NondominatedTangent
open AsymptoticStatistics.Core.NondominatedPathwise
open AsymptoticStatistics.Core.NondominatedEfficiencyOperational
open AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

-- Port note (Lean v4.33 / Mathlib db584cd): a variance written as an anonymous constructor
-- `⟨x, h⟩ : ℝ≥0` elaborates at the subtype `{r // 0 ≤ r}`, which instance search no longer sees
-- through. This restates Mathlib's `IsProbabilityMeasure (gaussianReal μ v)` for that spelling.
instance isProbabilityMeasure_gaussianReal_anonMk (μ x : ℝ) (h : 0 ≤ x) :
    IsProbabilityMeasure (gaussianReal μ ⟨x, h⟩) :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal μ (NNReal.mk x h)))

/-- Finite carrier-span projections exhaust every element of the closed
nondominated tangent space.

Proof idea: unfold `NondominatedTangent.tangentSpace`, approximate from the
algebraic carrier span, enlarge finite supports monotonically, and use
finite-dimensional orthogonal projections. All hypotheses are derived from
the carrier of `C`. -/
theorem proj_seq_to_eif_nd
    (C : NondominatedTangentCone P)
    {IF_eff : ↥(L2ZeroMean P)} (h_mem : IF_eff ∈ tangentSpace C) :
    ∃ V : ℕ → Submodule ℝ ↥(L2ZeroMean P),
    ∃ p : ℕ → ↥(L2ZeroMean P),
      (∀ m, V m ≤ tangentSpace C) ∧
      (∀ m, V m ≤ V (m + 1)) ∧
      (∀ m, FiniteDimensional ℝ (V m)) ∧
      (∀ m, ∃ S : Finset ↥(L2ZeroMean P),
        (↑S : Set ↥(L2ZeroMean P)) ⊆ C.carrier ∧
        V m = Submodule.span ℝ (↑S : Set ↥(L2ZeroMean P))) ∧
      (∀ m, p m ∈ V m ∧ IF_eff - p m ∈ (V m)ᗮ) ∧
      Tendsto (fun m => ‖p m - IF_eff‖) atTop (nhds 0) := by
  classical
  haveI : IsClosed ((L2ZeroMean P : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) :=
    L2ZeroMean_isClosed P
  have h_clos : IF_eff ∈ closure
      ((Submodule.span ℝ C.carrier : Submodule ℝ ↥(L2ZeroMean P)) :
        Set ↥(L2ZeroMean P)) := by
    simpa [tangentSpace, Submodule.topologicalClosure_coe] using! h_mem
  have h_approx : ∀ m : ℕ, ∃ a : ↥(L2ZeroMean P),
      a ∈ (Submodule.span ℝ C.carrier : Submodule ℝ ↥(L2ZeroMean P)) ∧
        ‖IF_eff - a‖ < 1 / (m + 1 : ℝ) := by
    intro m
    rcases Metric.mem_closure_iff.mp h_clos (1 / (m + 1 : ℝ)) (by positivity) with
      ⟨a, ha_mem, hdist⟩
    exact ⟨a, ha_mem, by rwa [← dist_eq_norm]⟩
  choose a ha_mem ha_dist using h_approx
  have h_finset : ∀ m : ℕ, ∃ Tm : Finset ↥(L2ZeroMean P),
      (↑Tm : Set ↥(L2ZeroMean P)) ⊆ C.carrier ∧
        a m ∈ Submodule.span ℝ (↑Tm : Set ↥(L2ZeroMean P)) := fun m =>
    Submodule.mem_span_finite_of_mem_span (ha_mem m)
  choose T hT_sub hT_mem using h_finset
  let S : ℕ → Finset ↥(L2ZeroMean P) := fun m =>
    (Finset.range (m + 1)).biUnion T
  let V : ℕ → Submodule ℝ ↥(L2ZeroMean P) := fun m =>
    Submodule.span ℝ (↑(S m) : Set ↥(L2ZeroMean P))
  have hS_sub : ∀ m, (↑(S m) : Set ↥(L2ZeroMean P)) ⊆ C.carrier := by
    intro m x hx
    simp only [S, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion,
      Set.mem_Iio] at hx
    rcases hx with ⟨k, _, hkx⟩
    exact hT_sub k hkx
  have hS_mono : ∀ m, (↑(S m) : Set ↥(L2ZeroMean P)) ⊆
      (↑(S (m + 1)) : Set _) := by
    intro m x hx
    simp only [S, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion,
      Set.mem_Iio] at hx ⊢
    rcases hx with ⟨k, hk, hkx⟩
    exact ⟨k, by omega, hkx⟩
  have hT_in_S : ∀ m, (↑(T m) : Set ↥(L2ZeroMean P)) ⊆ (↑(S m) : Set _) := by
    intro m x hx
    simp only [S, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion,
      Set.mem_Iio]
    exact ⟨m, by omega, hx⟩
  have hV_findim : ∀ m, FiniteDimensional ℝ (V m) := fun m =>
    @FiniteDimensional.span_finset ℝ ↥(L2ZeroMean P) _ _ _ (S m)
  haveI hUG_L2 : IsUniformAddGroup ↥(L2ZeroMean P) :=
    (L2ZeroMean P).toAddSubgroup.isUniformAddGroup
  have hV_complete : ∀ m, CompleteSpace (V m) := fun m =>
    haveI := hV_findim m
    haveI : IsUniformAddGroup ↥(V m) := (V m).toAddSubgroup.isUniformAddGroup
    @FiniteDimensional.complete ℝ ↥(V m) _ _ _ _ _ _ _ _ _
  have hV_proj : ∀ m, (V m).HasOrthogonalProjection := fun m =>
    @Submodule.HasOrthogonalProjection.ofCompleteSpace _ _ _ _ _ (V m)
      (hV_complete m)
  have hV_le : ∀ m, V m ≤ tangentSpace C := by
    intro m
    exact (Submodule.span_mono (hS_sub m)).trans
      (Submodule.span ℝ C.carrier).le_topologicalClosure
  have hV_inc : ∀ m, V m ≤ V (m + 1) := fun m =>
    Submodule.span_mono (hS_mono m)
  have ha_in_V : ∀ m, a m ∈ V m := fun m =>
    Submodule.span_mono (hT_in_S m) (hT_mem m)
  let p : ℕ → ↥(L2ZeroMean P) := fun m =>
    haveI := hV_proj m
    (V m).starProjection IF_eff
  have h_proj_bound : ∀ m, ‖IF_eff - p m‖ ≤ ‖IF_eff - a m‖ := by
    intro m
    haveI := hV_proj m
    rw [show p m = (V m).starProjection IF_eff from rfl,
      Submodule.starProjection_minimal IF_eff]
    refine ciInf_le ⟨0, ?_⟩ (⟨a m, ha_in_V m⟩ : V m)
    rintro _ ⟨x, rfl⟩
    exact norm_nonneg _
  refine ⟨V, p, hV_le, hV_inc, hV_findim, ?_, ?_, ?_⟩
  · intro m
    exact ⟨S m, hS_sub m, rfl⟩
  · intro m
    haveI := hV_proj m
    exact ⟨(V m).starProjection_apply_mem IF_eff,
      (V m).sub_starProjection_mem_orthogonal IF_eff⟩
  · have h_bound : ∀ m, ‖p m - IF_eff‖ ≤ 1 / (m + 1 : ℝ) := by
      intro m
      rw [norm_sub_rev]
      exact (h_proj_bound m).trans (ha_dist m).le
    exact squeeze_zero (fun _ => norm_nonneg _) h_bound
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Baseline root-`n` centered estimator; at `n=0` it is zero. -/
noncomputable def centeredEstimator
    (T_n : ∀ n, (Fin n → Ω) → ℝ) (ψP : ℝ) (n : ℕ) (X : Fin n → Ω) : ℝ :=
  Real.sqrt n * (T_n n X - ψP)

/-- Exact half-line tilt information extracted from regularity and a fixed
baseline joint subsequential limit.

Constitutive (vdV §25.3.2 p.366): the second marginal is the score Gaussian
and every nonnegative exponential tilt has the shifted regular limit. -/
structure NonnegativeTiltSupply
    (π : Measure (ℝ × ℝ)) (v s : ℝ≥0) (c : ℝ) : Prop where
  /-- Constitutive: the baseline subsequential law is a probability. -/
  isProbability : IsProbabilityMeasure π
  /-- Constitutive: its score marginal is the baseline score Gaussian. -/
  snd_law : π.map Prod.snd = gaussianReal 0 v
  /-- Constitutive: every nonnegative likelihood tilt gives the shifted
  first-coordinate Gaussian law. -/
  tilted_fst_law : ∀ a : ℝ, 0 ≤ a →
    (π.withDensity (fun q => ENNReal.ofReal
      (Real.exp (a * q.2 - (a ^ 2 / 2) * (v : ℝ))))).map Prod.fst =
      gaussianReal (a * c) s

/-- Regularity, pathwise differentiability and nondominated Le Cam theory
construct the half-line tilt supply for one carrier score.

Proof idea: use cone closure under `a≥0` to select the path for `a•g`, then
Le Cam III, right pathwise differentiation, and unit-path regularity. -/
theorem nonnegativeTiltSupply_of_regular
    {T_n : ∀ n, (Fin n → Ω) → ℝ} {ψ : Measure Ω → ℝ}
    (C : NondominatedTangentCone P)
    (hpd : NondominatedPathwiseDifferentiableAt P C ψ)
    {φ : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace C) hpd.derivative φ)
    (hT : ∀ n, Measurable (T_n n))
    (hreg : IsRegularAtND C T_n ψ
      (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩))
    (g : {g : ↥(L2ZeroMean P) // g ∈ C.carrier})
    (χ : ℕ → ℕ) (hχ : StrictMono χ)
    (π : Measure (ℝ × ℝ))
    (hπprob : IsProbabilityMeasure π)
    (hπ : AsymptoticStatistics.WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
          normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X))) π) :
    NonnegativeTiltSupply π
      ⟨‖(g : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩
      ⟨‖φ‖ ^ 2, sq_nonneg _⟩
      ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ := by
  classical
  letI : IsProbabilityMeasure π := hπprob
  have hπsnd : π.map Prod.snd =
      gaussianReal 0 ⟨‖(g : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩ := by
    have hscore := qmd_local_score_clt (C.selectedPath g) 0 le_rfl
      (g : ↥(L2ZeroMean P))
    have hscore' : AsymptoticStatistics.WeakConverges
        (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
          (normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k)))
        (gaussianReal 0
          ⟨‖(g : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩) := by
      simpa only [zero_mul, (C.selectedPath g).curve_at_zero,
        C.selectedPath_score g] using hscore.comp hχ
    have hpairMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
        (centeredEstimator T_n (ψ P) (χ k) X,
          normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X)) := by
      intro k
      apply Measurable.prodMk
      · exact Measurable.const_mul ((hT (χ k)).sub_const _) _
      · unfold normalizedScoreSum
        exact Measurable.const_mul
          (Finset.measurable_sum _ fun i _ =>
            (Lp.stronglyMeasurable ((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P)).measurable.comp
              (measurable_pi_apply i)) _
    have hscoreSnd : AsymptoticStatistics.WeakConverges
        (fun k => ((Measure.pi (fun _ : Fin (χ k) => P)).map
          (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
            normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X))).map Prod.snd)
        (gaussianReal 0
          ⟨‖(g : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩) := by
      simpa only [Measure.map_map measurable_snd (hpairMeas _)] using! hscore'
    exact AsymptoticStatistics.WeakConverges.snd_eq hπ hscoreSnd
  refine ⟨hπprob, hπsnd, ?_⟩
  · intro a ha
    let ga : {u : ↥(L2ZeroMean P) // u ∈ C.carrier} :=
      ⟨a • (g : ↥(L2ZeroMean P)), C.nonneg_smul_mem ha g.property⟩
    let γ := C.selectedPath ga
    let scaleSnd : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, a * q.2)
    have hscaleCont : Continuous scaleSnd := by fun_prop
    have hscaleMeas : Measurable scaleSnd := hscaleCont.measurable
    haveI : IsProbabilityMeasure (π.map scaleSnd) :=
      Measure.isProbabilityMeasure_map hscaleMeas.aemeasurable
    have hγscore : γ.score = a • (g : ↥(L2ZeroMean P)) := by
      simpa only [γ, ga] using C.selectedPath_score ga
    have hY : ∀ n, Measurable (centeredEstimator T_n (ψ P) n) := by
      intro n
      exact Measurable.const_mul ((hT n).sub_const _) _
    have hgscoreMeas : ∀ k, Measurable
        (normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k)) := by
      intro k
      unfold normalizedScoreSum
      exact Measurable.const_mul
        (Finset.measurable_sum _ fun i _ =>
          (Lp.stronglyMeasurable ((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P)).measurable.comp
            (measurable_pi_apply i)) _
    have hpairMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
        (centeredEstimator T_n (ψ P) (χ k) X,
          normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X)) := fun k =>
      (hY (χ k)).prodMk (hgscoreMeas k)
    have hcoe : ((γ.score : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
        fun ω => a * ((((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω) := by
      rw [hγscore]
      exact Lp.coeFn_smul _ _
    have hscoreScaleAE : ∀ k,
        (fun X : Fin (χ k) → Ω => normalizedScoreSum γ.score (χ k) X) =ᵐ[
          Measure.pi (fun _ : Fin (χ k) => P)]
        (fun X => a * normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X) := by
      intro k
      have hcoord : ∀ i : Fin (χ k), (fun _ : Ω => True) ≤ᵐ[P]
          (fun ω => ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω =
            a * ((((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω)) :=
        fun _ => hcoe.mono fun _ h _ => h
      have hall : (fun X : Fin (χ k) → Ω => fun _ : Fin (χ k) => True) ≤ᵐ[
          Measure.pi (fun _ : Fin (χ k) => P)]
          (fun X i => ((γ.score : Lp ℝ 2 P) : Ω → ℝ) (X i) =
            a * ((((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) (X i))) := by
        simpa using Measure.ae_le_pi hcoord
      filter_upwards [hall] with X hX
      simp only [normalizedScoreSum]
      rw [show (∑ i : Fin (χ k), ((γ.score : Lp ℝ 2 P) : Ω → ℝ) (X i)) =
          ∑ i : Fin (χ k), a *
            ((((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) (X i)) by
        apply Finset.sum_congr rfl
        intro i _
        exact hX i trivial, ← Finset.mul_sum]
      ring
    have hbaseγ : AsymptoticStatistics.WeakConverges
        (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
          (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
            normalizedScoreSum γ.score (χ k) X)))
        (π.map scaleSnd) := by
      have hm := hπ.map hscaleCont hscaleMeas
      change AsymptoticStatistics.WeakConverges
        (fun k => ((Measure.pi (fun _ : Fin (χ k) => P)).map
          (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
            normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X))).map scaleSnd)
        (π.map scaleSnd) at hm
      have hmap : ∀ k,
          (Measure.pi (fun _ : Fin (χ k) => P)).map
              (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
                normalizedScoreSum γ.score (χ k) X)) =
            ((Measure.pi (fun _ : Fin (χ k) => P)).map
              (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
                normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X))).map
              scaleSnd := by
        intro k
        rw [Measure.map_map hscaleMeas (hpairMeas k)]
        apply Measure.map_congr
        filter_upwards [hscoreScaleAE k] with X hX
        simp only [Function.comp_apply, scaleSnd, hX]
      simpa only [hmap] using hm
    have hlecam := qmd_lecamThird_along_subseq γ 1 zero_le_one
      (centeredEstimator T_n (ψ P)) hY χ hχ (π.map scaleSnd) hbaseγ
    have htzero : Tendsto (fun k : ℕ => (Real.sqrt (χ k))⁻¹) atTop (nhds 0) := by
      exact (Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop.comp hχ.tendsto_atTop)).inv_tendsto_atTop
    have htpos : ∀ᶠ k : ℕ in atTop, 0 < (Real.sqrt (χ k))⁻¹ := by
      filter_upwards [hχ.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk
      exact inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < χ k by omega)))
    have htright : Tendsto (fun k : ℕ => (Real.sqrt (χ k))⁻¹) atTop
        (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨htzero, htpos⟩
    have hquot := (hpd.derivative_spec ga).comp htright
    have hderiv : hpd.derivative
        ⟨(ga : ↥(L2ZeroMean P)), selected_mem_tangentSpace C ga⟩ =
        a * ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ := by
      rw [← hEIF.1
        ⟨(ga : ↥(L2ZeroMean P)), selected_mem_tangentSpace C ga⟩]
      change ⟪φ, a • (g : ↥(L2ZeroMean P))⟫_ℝ = _
      exact real_inner_smul_right φ (g : ↥(L2ZeroMean P)) a
    have hshift : Tendsto (fun k => Real.sqrt (χ k) *
        (ψ (γ.curve ((Real.sqrt (χ k))⁻¹)) - ψ P)) atTop
        (nhds (a * ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ)) := by
      rw [← hderiv]
      have heq : (fun k => Real.sqrt (χ k) *
          (ψ (γ.curve ((Real.sqrt (χ k))⁻¹)) - ψ P)) =
          fun k => (ψ (γ.curve ((Real.sqrt (χ k))⁻¹)) - ψ P) /
            (Real.sqrt (χ k))⁻¹ := by
        funext k
        by_cases hk : Real.sqrt (χ k) = 0
        · simp [hk]
        · field_simp
      rw [heq]
      simpa only [Function.comp_apply, γ] using! hquot
    let Q : (k : ℕ) → Measure (Fin (χ k) → Ω) := fun k =>
      Measure.pi (fun _ : Fin (χ k) => γ.curve ((Real.sqrt (χ k))⁻¹))
    let Xinner : ∀ k, (Fin (χ k) → Ω) → ℝ := fun k X =>
      Real.sqrt (χ k) *
        (T_n (χ k) X - ψ (γ.curve ((Real.sqrt (χ k))⁻¹)))
    let d : ℝ := a * ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ
    let Xshift : ∀ k, (Fin (χ k) → Ω) → ℝ := fun k X => Xinner k X + d
    let Youter : ∀ k, (Fin (χ k) → Ω) → ℝ := fun k =>
      centeredEstimator T_n (ψ P) (χ k)
    haveI : ∀ k, IsProbabilityMeasure (Q k) := fun k => by
      letI : IsProbabilityMeasure (γ.curve ((Real.sqrt (χ k))⁻¹)) :=
        γ.curve_isProbability _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
      infer_instance
    have hinner : AsymptoticStatistics.WeakConverges
        (fun k => (Q k).map (Xinner k))
        (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) := by
      simpa only [Q, Xinner, γ] using (hreg ga).comp hχ
    have hXinnerMeas : ∀ k, Measurable (Xinner k) := fun k =>
      Measurable.const_mul ((hT (χ k)).sub_const _) _
    have hshifted : AsymptoticStatistics.WeakConverges
        (fun k => (Q k).map (Xshift k))
        ((gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩).map (fun x => x + d)) := by
      have hm := hinner.map (continuous_id.add continuous_const)
        (measurable_id.add_const d)
      intro f
      have hmap : ∀ k, (Q k).map (Xshift k) =
          ((Q k).map (Xinner k)).map (fun x : ℝ => x + d) := by
        intro k
        calc
          (Q k).map (Xshift k) =
              (Q k).map ((fun x : ℝ => x + d) ∘ Xinner k) := by rfl
          _ = ((Q k).map (Xinner k)).map (fun x : ℝ => x + d) :=
            (Measure.map_map (measurable_id.add_const d) (hXinnerMeas k)).symm
      simpa only [hmap] using! hm f
    have houterMeas : ∀ k, Measurable (Youter k) := fun k => hY (χ k)
    have hdist : ∀ ε > 0, Tendsto (fun k => (Q k).real
        {X | ε ≤ dist (Xshift k X) (Youter k X)}) atTop (nhds 0) := by
      intro ε hε
      have hclose : Tendsto (fun k => |d - Real.sqrt (χ k) *
          (ψ (γ.curve ((Real.sqrt (χ k))⁻¹)) - ψ P)|) atTop (nhds 0) := by
        have h0 : Tendsto (fun k => d - Real.sqrt (χ k) *
            (ψ (γ.curve ((Real.sqrt (χ k))⁻¹)) - ψ P)) atTop
            (nhds (d - a * ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ)) :=
          tendsto_const_nhds.sub hshift
        have habs := (continuous_abs.tendsto
          (d - a * ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ)).comp h0
        simpa only [d, sub_self, abs_zero] using! habs
      have hev : ∀ᶠ k in atTop, |d - Real.sqrt (χ k) *
          (ψ (γ.curve ((Real.sqrt (χ k))⁻¹)) - ψ P)| < ε := by
        simpa only [Real.dist_eq, sub_zero, abs_abs] using
          (Metric.tendsto_nhds.mp hclose) ε hε
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      filter_upwards [hev] with k hk
      have hset : {X | ε ≤ dist (Xshift k X) (Youter k X)} =
          (∅ : Set (Fin (χ k) → Ω)) := by
        ext X
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le,
          Real.dist_eq]
        rw [show Xshift k X - Youter k X = d - Real.sqrt (χ k) *
            (ψ (γ.curve ((Real.sqrt (χ k))⁻¹)) - ψ P) by
          simp only [Xshift, Xinner, Youter, centeredEstimator]
          ring]
        exact hk
      rw [hset, measureReal_empty]
    haveI : IsProbabilityMeasure
        ((gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩).map (fun x => x + d)) :=
      Measure.isProbabilityMeasure_map (measurable_id.add_const d).aemeasurable
    have houter0 := AsymptoticStatistics.WeakConverges.slutsky_of_tendstoInMeasure_dist
      (fun k => (hXinnerMeas k).add_const d |>.aemeasurable)
      (fun k => (houterMeas k).aemeasurable) hshifted hdist
    have hgaussShift :
        (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩).map (fun x => x + d) =
          gaussianReal d ⟨‖φ‖ ^ 2, sq_nonneg _⟩ := by
      simpa only [zero_add] using
        ProbabilityTheory.gaussianReal_map_add_const (μ := 0)
          (v := ⟨‖φ‖ ^ 2, sq_nonneg _⟩) d
    have houter : AsymptoticStatistics.WeakConverges
        (fun k => (Measure.pi (fun _ : Fin (χ k) =>
          γ.curve ((Real.sqrt (χ k))⁻¹))).map
          (centeredEstimator T_n (ψ P) (χ k)))
        (gaussianReal d ⟨‖φ‖ ^ 2, sq_nonneg _⟩) := by
      rw [hgaussShift] at houter0
      simpa only [Q, Youter] using houter0
    have hlecam' : AsymptoticStatistics.WeakConverges
        (fun k => (Measure.pi (fun _ : Fin (χ k) =>
          γ.curve ((Real.sqrt (χ k))⁻¹))).map
          (centeredEstimator T_n (ψ P) (χ k)))
        (((π.map scaleSnd).withDensity (fun q => ENNReal.ofReal
          (Real.exp (q.2 - (1 / 2 : ℝ) * ‖γ.score‖ ^ 2)))).map Prod.fst) := by
      simpa only [one_mul, one_pow] using hlecam
    let vg : NNReal := ⟨‖(g : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩
    have hExp : Integrable
        (fun q : ℝ × ℝ => Real.exp (a * q.2)) π := by
      have hG := ProbabilityTheory.integrable_exp_mul_gaussianReal
        (μ := 0)
        (v := vg) a
      rw [← hπsnd] at hG
      exact hG.comp_measurable measurable_snd
    have hTiltInt : Integrable (fun q : ℝ × ℝ => Real.exp
        (a * q.2 - (a ^ 2 / 2) * (vg : ℝ))) π := by
      convert hExp.mul_const (Real.exp (-((a ^ 2 / 2) *
        (vg : ℝ)))) using 1
      funext q
      rw [← Real.exp_add]
      congr 1
    let tiltDensity : (ℝ × ℝ) → ℝ≥0∞ := fun q => ENNReal.ofReal
      (Real.exp (a * q.2 - (a ^ 2 / 2) * (vg : ℝ)))
    haveI hTiltFinite : IsFiniteMeasure (π.withDensity tiltDensity) :=
      isFiniteMeasure_withDensity_ofReal hTiltInt.hasFiniteIntegral
    have htarget :
        (((π.map scaleSnd).withDensity (fun q => ENNReal.ofReal
          (Real.exp (q.2 - (1 / 2 : ℝ) * ‖γ.score‖ ^ 2)))).map Prod.fst) =
        ((π.withDensity (fun q => ENNReal.ofReal
          (Real.exp (a * q.2 - (a ^ 2 / 2) * (vg : ℝ))))).map
          Prod.fst) := by
      have hdens : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal
          (Real.exp (q.2 - (1 / 2 : ℝ) * ‖γ.score‖ ^ 2))) := by fun_prop
      rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
        π scaleSnd hscaleMeas _ hdens]
      rw [Measure.map_map measurable_fst hscaleMeas]
      have hfst : Prod.fst ∘ scaleSnd = Prod.fst := rfl
      rw [hfst]
      have hdensityEq :
          (fun q : ℝ × ℝ => ENNReal.ofReal
            (Real.exp (q.2 - (1 / 2 : ℝ) * ‖γ.score‖ ^ 2))) ∘ scaleSnd =
          fun q => ENNReal.ofReal
            (Real.exp (a * q.2 - (a ^ 2 / 2) * (vg : ℝ))) := by
        funext q
        apply congrArg ENNReal.ofReal
        apply congrArg Real.exp
        rw [hγscore, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
        dsimp only [vg, scaleSnd, Function.comp_apply]
        norm_num
        ring_nf
        rfl
      rw [hdensityEq]
    have hlecamTarget : AsymptoticStatistics.WeakConverges
        (fun k => (Measure.pi (fun _ : Fin (χ k) =>
          γ.curve ((Real.sqrt (χ k))⁻¹))).map
          (centeredEstimator T_n (ψ P) (χ k)))
        ((π.withDensity tiltDensity).map Prod.fst) := by
      rw [← htarget]
      exact hlecam'
    have hunique := AsymptoticStatistics.WeakConverges.unique hlecamTarget houter
    simpa only [tiltDensity, d, div_eq_mul_inv] using hunique

/-- A constructed nonnegative tilt supply identifies the cross integral.

Proof idea: install its probability instance and invoke nonnegative Gaussian
tilt rigidity, including `v=0`. -/
theorem cross_integral_eq_of_tiltSupply
    (π : Measure (ℝ × ℝ)) (v s : ℝ≥0) (c : ℝ)
    (H : NonnegativeTiltSupply π v s c) :
    Integrable (fun q : ℝ × ℝ => q.1 * q.2) π ∧
      ∫ q : ℝ × ℝ, q.1 * q.2 ∂π = c := by
  letI : IsProbabilityMeasure π := H.isProbability
  exact AsymptoticStatistics.ForMathlib.GaussianTiltRigidity.covariance_eq_of_nonneg_gaussian_tilts
    π v s c H.snd_law H.tilted_fst_law

private lemma integral_sq_eq_of_map_eq_gaussianReal
    {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (f : E → ℝ) (hf : Measurable f)
    (v : ℝ≥0) (hmap : μ.map f = gaussianReal 0 v) :
    Integrable (fun x => f x ^ 2) μ ∧ ∫ x, f x ^ 2 ∂μ = (v : ℝ) := by
  have hfLp : MemLp f 2 μ := by
    have hid : MemLp id 2 (μ.map f) := by
      rw [hmap]
      exact ProbabilityTheory.memLp_id_gaussianReal' 2 (by norm_num)
    have hcomp := (memLp_map_measure_iff hid.aestronglyMeasurable hf.aemeasurable).1 hid
    simpa only [id_eq, Function.comp_apply] using! hcomp
  have hgaussSq : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v = (v : ℝ) := by
    simpa only [variance_eq_integral measurable_id'.aemeasurable,
      ProbabilityTheory.integral_id_gaussianReal, sub_zero] using
      (ProbabilityTheory.variance_fun_id_gaussianReal (μ := 0) (v := v))
  refine ⟨hfLp.integrable_sq, ?_⟩
  calc
    ∫ x, f x ^ 2 ∂μ = ∫ x : ℝ, x ^ 2 ∂(μ.map f) := by
      rw [integral_map hf.aemeasurable (by fun_prop)]
    _ = (v : ℝ) := by rw [hmap, hgaussSq]

/-- A finite carrier extension supplies only the quantitative residual bound
`4‖φ-p‖²`, not a Dirac conclusion.

Proof idea: expand `p` in the finite span, apply the cross identity to each
carrier coordinate, and use Chebyshev. -/
theorem residual_secondMoment_bound_of_finset_extension
    {T_n : ∀ n, (Fin n → Ω) → ℝ} {ψ : Measure Ω → ℝ}
    (C : NondominatedTangentCone P)
    (hpd : NondominatedPathwiseDifferentiableAt P C ψ)
    {φ : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace C) hpd.derivative φ)
    (hT : ∀ n, Measurable (T_n n))
    (hreg : IsRegularAtND C T_n ψ
      (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩))
    (S : Finset ↥(L2ZeroMean P)) (hS : (↑S : Set _) ⊆ C.carrier)
    (p : ↥(L2ZeroMean P)) (hp : p ∈ Submodule.span ℝ (↑S : Set _))
    (χ : ℕ → ℕ) (hχ : StrictMono χ)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hπ : AsymptoticStatistics.WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
          normalizedScoreSum φ (χ k) X))) π)
    (ρ : Measure ((ℝ × ℝ) × (↥S → ℝ))) [IsProbabilityMeasure ρ]
    (hρ : AsymptoticStatistics.WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => ((centeredEstimator T_n (ψ P) (χ k) X,
          normalizedScoreSum φ (χ k) X),
          fun g : ↥S => normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X))) ρ) :
    (∫ q : ℝ × ℝ, (q.1 - q.2) ^ 2 ∂π ≤ 4 * ‖φ - p‖ ^ 2) ∧
      ∀ ε > 0, (π {q | ε ≤ |q.1 - q.2|}).toReal ≤
        4 * ‖φ - p‖ ^ 2 / ε ^ 2 := by
  classical
  let z : {g : ↥(L2ZeroMean P) // g ∈ C.carrier} := ⟨0, zero_mem C⟩
  let setSndZero : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, 0)
  have hsetSndZeroCont : Continuous setSndZero := by fun_prop
  have hsetSndZeroMeas : Measurable setSndZero := hsetSndZeroCont.measurable
  have hscoreMeas : ∀ (u : ↥(L2ZeroMean P)) k,
      Measurable (normalizedScoreSum u (χ k)) := by
    intro u k
    unfold normalizedScoreSum
    exact Measurable.const_mul
      (Finset.measurable_sum _ fun i _ =>
        (Lp.stronglyMeasurable (u : Lp ℝ 2 P)).measurable.comp
          (measurable_pi_apply i)) _
  have hpairMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
      (centeredEstimator T_n (ψ P) (χ k) X,
        normalizedScoreSum φ (χ k) X)) := by
    intro k
    exact (Measurable.const_mul ((hT (χ k)).sub_const _) _).prodMk
      (hscoreMeas φ k)
  have hextMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
      ((centeredEstimator T_n (ψ P) (χ k) X,
        normalizedScoreSum φ (χ k) X),
        fun g : ↥S => normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X)) := by
    intro k
    exact (hpairMeas k).prodMk
      (measurable_pi_lambda _ fun g => hscoreMeas (g : ↥(L2ZeroMean P)) k)
  have hρfstWeak : AsymptoticStatistics.WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
          normalizedScoreSum φ (χ k) X)))
      (ρ.map Prod.fst) := by
    have hm := hρ.map continuous_fst measurable_fst
    simpa only [Measure.map_map measurable_fst (hextMeas _), Function.comp_apply]
      using! hm
  have hρfst : ρ.map Prod.fst = π :=
    AsymptoticStatistics.WeakConverges.unique hρfstWeak hπ
  have hπsnd : π.map Prod.snd =
      gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩ := by
    have hscore := qmd_local_score_clt (C.selectedPath z) 0 le_rfl φ
    have hscore' : AsymptoticStatistics.WeakConverges
        (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
          (normalizedScoreSum φ (χ k)))
        (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) := by
      simpa only [zero_mul, (C.selectedPath z).curve_at_zero] using hscore.comp hχ
    have hscoreSnd : AsymptoticStatistics.WeakConverges
        (fun k => ((Measure.pi (fun _ : Fin (χ k) => P)).map
          (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
            normalizedScoreSum φ (χ k) X))).map Prod.snd)
        (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) := by
      simpa only [Measure.map_map measurable_snd (hpairMeas _)] using! hscore'
    exact AsymptoticStatistics.WeakConverges.snd_eq hπ hscoreSnd
  have hzeroCoe : ((((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ)) =ᵐ[P]
      fun _ => 0 := Lp.coeFn_zero _ _ _
  have hzeroScoreAE : ∀ k,
      (fun X : Fin (χ k) → Ω => normalizedScoreSum (0 : ↥(L2ZeroMean P)) (χ k) X)
        =ᵐ[Measure.pi (fun _ : Fin (χ k) => P)] fun _ => 0 := by
    intro k
    have hcoord : ∀ i : Fin (χ k), (fun _ : Ω => True) ≤ᵐ[P]
        (fun ω => ((((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω) = 0) :=
      fun _ => hzeroCoe.mono fun _ h _ => h
    have hall := Measure.ae_le_pi hcoord
    filter_upwards [hall] with X hX
    simp only [normalizedScoreSum]
    have hsum : (∑ i : Fin (χ k),
        ((((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) (X i))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact hX i trivial
    rw [hsum, mul_zero]
  let π0 : Measure (ℝ × ℝ) := π.map setSndZero
  haveI hπ0prob : IsProbabilityMeasure π0 :=
    Measure.isProbabilityMeasure_map hsetSndZeroMeas.aemeasurable
  have hbase0 : AsymptoticStatistics.WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
          normalizedScoreSum (0 : ↥(L2ZeroMean P)) (χ k) X))) π0 := by
    have hm := hπ.map hsetSndZeroCont hsetSndZeroMeas
    have hmap : ∀ k,
        (Measure.pi (fun _ : Fin (χ k) => P)).map
            (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
              normalizedScoreSum (0 : ↥(L2ZeroMean P)) (χ k) X)) =
          ((Measure.pi (fun _ : Fin (χ k) => P)).map
            (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
              normalizedScoreSum φ (χ k) X))).map setSndZero := by
      intro k
      rw [Measure.map_map hsetSndZeroMeas (hpairMeas k)]
      apply Measure.map_congr
      filter_upwards [hzeroScoreAE k] with X hX
      simp only [Function.comp_apply, setSndZero, hX]
    simpa only [hmap] using hm
  have H0 := nonnegativeTiltSupply_of_regular C hpd hEIF hT hreg z χ hχ π0
    hπ0prob hbase0
  have hπ0fst : π0.map Prod.fst = gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩ := by
    have ht := H0.tilted_fst_law 0 le_rfl
    norm_num at ht
    simpa only [withDensity_one] using! ht
  have hπfst : π.map Prod.fst = gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩ := by
    rw [← hπ0fst]
    simp only [π0, Measure.map_map measurable_fst hsetSndZeroMeas]
    rfl
  rcases (Submodule.mem_span_finset').mp hp with ⟨c : ↥S → ℝ, hc⟩
  let pScore : ((ℝ × ℝ) × (↥S → ℝ)) → ℝ := fun r =>
    ∑ g : ↥S, c g * r.2 g
  have hpScoreMeas : Measurable pScore := by
    dsimp only [pScore]
    fun_prop
  have hcrossCoord : ∀ g : ↥S,
      Integrable (fun r : ((ℝ × ℝ) × (↥S → ℝ)) => r.1.1 * r.2 g) ρ ∧
        ∫ r, r.1.1 * r.2 g ∂ρ = ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ := by
    intro g
    let projG : ((ℝ × ℝ) × (↥S → ℝ)) → ℝ × ℝ := fun r =>
      (r.1.1, r.2 g)
    have hprojGCont : Continuous projG := by fun_prop
    have hprojGMeas : Measurable projG := hprojGCont.measurable
    let πg : Measure (ℝ × ℝ) := ρ.map projG
    haveI hπgprob : IsProbabilityMeasure πg :=
      Measure.isProbabilityMeasure_map hprojGMeas.aemeasurable
    have hbaseg : AsymptoticStatistics.WeakConverges
        (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
          (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
            normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X))) πg := by
      have hm := hρ.map hprojGCont hprojGMeas
      have hmap : ∀ k,
          ((Measure.pi (fun _ : Fin (χ k) => P)).map
            (fun X => ((centeredEstimator T_n (ψ P) (χ k) X,
              normalizedScoreSum φ (χ k) X),
              fun u : ↥S => normalizedScoreSum (u : ↥(L2ZeroMean P)) (χ k) X))).map
                projG =
            (Measure.pi (fun _ : Fin (χ k) => P)).map
              (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
                normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X)) := by
        intro k
        rw [Measure.map_map hprojGMeas (hextMeas k)]
        rfl
      simpa only [hmap] using hm
    let gc : {u : ↥(L2ZeroMean P) // u ∈ C.carrier} := ⟨g, hS g.property⟩
    have Hg := nonnegativeTiltSupply_of_regular C hpd hEIF hT hreg gc χ hχ πg
      hπgprob (by simpa only [gc] using hbaseg)
    have hcg := cross_integral_eq_of_tiltSupply πg
      ⟨‖(g : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩
      ⟨‖φ‖ ^ 2, sq_nonneg _⟩ ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ
      (by simpa only [gc] using Hg)
    constructor
    · simpa only [πg, projG, Function.comp_apply] using!
        hcg.1.comp_measurable hprojGMeas
    · calc
        ∫ r, r.1.1 * r.2 g ∂ρ = ∫ q : ℝ × ℝ, q.1 * q.2 ∂πg := by
          change ∫ r, r.1.1 * r.2 g ∂ρ =
            ∫ q : ℝ × ℝ, q.1 * q.2 ∂(ρ.map projG)
          rw [integral_map hprojGMeas.aemeasurable (by fun_prop)]
        _ = ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ := hcg.2
  have hTpInt : Integrable (fun r : ((ℝ × ℝ) × (↥S → ℝ)) =>
      r.1.1 * pScore r) ρ := by
    have hsum : Integrable (fun r : ((ℝ × ℝ) × (↥S → ℝ)) =>
        ∑ g : ↥S, c g * (r.1.1 * r.2 g)) ρ :=
      integrable_finset_sum Finset.univ fun g _ => (hcrossCoord g).1.const_mul (c g)
    convert hsum using 1
    funext r
    simp only [pScore, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    ring
  have hTp : ∫ r : ((ℝ × ℝ) × (↥S → ℝ)), r.1.1 * pScore r ∂ρ =
      ⟪φ, p⟫_ℝ := by
    calc
      ∫ r, r.1.1 * pScore r ∂ρ =
          ∫ r, ∑ g : ↥S, c g * (r.1.1 * r.2 g) ∂ρ := by
            congr 1
            funext r
            simp only [pScore, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro g _
            ring
      _ = ∑ g : ↥S, c g * ∫ r, r.1.1 * r.2 g ∂ρ := by
        rw [integral_finset_sum Finset.univ fun g _ =>
          (hcrossCoord g).1.const_mul (c g)]
        apply Finset.sum_congr rfl
        intro g _
        rw [integral_const_mul]
      _ = ∑ g : ↥S, c g * ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ := by
        apply Finset.sum_congr rfl
        intro g _
        rw [(hcrossCoord g).2]
      _ = ⟪φ, p⟫_ℝ := by
        rw [← hc]
        symm
        calc
          ⟪φ, ∑ g : ↥S, c g • (g : ↥(L2ZeroMean P))⟫_ℝ =
              ∑ g : ↥S, ⟪φ, c g • (g : ↥(L2ZeroMean P))⟫_ℝ := by
            simpa only [Finset.mem_univ, true_and] using
              (inner_sum (Finset.univ : Finset ↥S)
                (fun g => c g • (g : ↥(L2ZeroMean P))) φ)
          _ = ∑ g : ↥S, c g * ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ := by
            apply Finset.sum_congr rfl
            intro g _
            exact real_inner_smul_right φ (g : ↥(L2ZeroMean P)) (c g)
  have hsumCoe : ∀ s : Finset ↥S,
      (((∑ g ∈ s, c g • (g : ↥(L2ZeroMean P)) : ↥(L2ZeroMean P)) :
          Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
        fun ω => ∑ g ∈ s, c g *
          ((((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using! (Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞)) (μ := P))
    | @insert a s ha ih =>
        have hadd := Lp.coeFn_add
          (((c a • (a : ↥(L2ZeroMean P)) : ↥(L2ZeroMean P)) : Lp ℝ 2 P))
          (((∑ g ∈ s, c g • (g : ↥(L2ZeroMean P)) : ↥(L2ZeroMean P)) :
            Lp ℝ 2 P))
        have hsmul := Lp.coeFn_smul (c a)
          (((a : ↥(L2ZeroMean P)) : Lp ℝ 2 P))
        have hadd' :
            (((c a • (a : ↥(L2ZeroMean P)) +
              ∑ g ∈ s, c g • (g : ↥(L2ZeroMean P)) : ↥(L2ZeroMean P)) :
                Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
              fun ω =>
                (((c a • (a : ↥(L2ZeroMean P)) : ↥(L2ZeroMean P)) :
                  Lp ℝ 2 P) : Ω → ℝ) ω +
                (((∑ g ∈ s, c g • (g : ↥(L2ZeroMean P)) : ↥(L2ZeroMean P)) :
                  Lp ℝ 2 P) : Ω → ℝ) ω := by
          simpa only [Pi.add_apply] using! hadd
        have hsmul' :
            (((c a • (a : ↥(L2ZeroMean P)) : ↥(L2ZeroMean P)) :
              Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
              fun ω => c a *
                ((((a : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω) := by
          simpa only [Pi.smul_apply, smul_eq_mul] using! hsmul
        simpa only [Finset.sum_insert ha] using! hadd'.trans (hsmul'.add ih)
  have hpCoe : (((p : Lp ℝ 2 P) : Ω → ℝ)) =ᵐ[P] fun ω =>
      ∑ g : ↥S, c g *
        ((((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω) := by
    rw [← hc]
    simpa only [Finset.mem_univ, true_and] using hsumCoe Finset.univ
  have hpScoreSourceAE : ∀ k,
      (fun X : Fin (χ k) → Ω => normalizedScoreSum p (χ k) X) =ᵐ[
        Measure.pi (fun _ : Fin (χ k) => P)]
      (fun X => ∑ g : ↥S, c g *
        normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X) := by
    intro k
    have hcoord : ∀ i : Fin (χ k), (fun _ : Ω => True) ≤ᵐ[P]
        (fun ω => (((p : Lp ℝ 2 P) : Ω → ℝ) ω) =
          ∑ g : ↥S, c g *
            ((((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω)) :=
      fun _ => hpCoe.mono fun _ h _ => h
    have hall := Measure.ae_le_pi hcoord
    filter_upwards [hall] with X hX
    simp only [normalizedScoreSum]
    rw [show (∑ i : Fin (χ k), ((p : Lp ℝ 2 P) : Ω → ℝ) (X i)) =
        ∑ i : Fin (χ k), ∑ g : ↥S, c g *
          ((((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) (X i)) by
      apply Finset.sum_congr rfl
      intro i _
      exact hX i trivial, Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [← Finset.mul_sum]
    ring
  have hpScoreLaw : ρ.map pScore = gaussianReal 0 ⟨‖p‖ ^ 2, sq_nonneg _⟩ := by
    have hfromρ : AsymptoticStatistics.WeakConverges
        (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
          (normalizedScoreSum p (χ k))) (ρ.map pScore) := by
      have hm := hρ.map (by fun_prop : Continuous pScore) hpScoreMeas
      have hmap : ∀ k,
          ((Measure.pi (fun _ : Fin (χ k) => P)).map
            (fun X => ((centeredEstimator T_n (ψ P) (χ k) X,
              normalizedScoreSum φ (χ k) X),
              fun u : ↥S => normalizedScoreSum (u : ↥(L2ZeroMean P)) (χ k) X))).map
                pScore =
            (Measure.pi (fun _ : Fin (χ k) => P)).map
              (normalizedScoreSum p (χ k)) := by
        intro k
        rw [Measure.map_map hpScoreMeas (hextMeas k)]
        apply Measure.map_congr
        exact (hpScoreSourceAE k).symm
      simpa only [hmap] using hm
    have hscore := qmd_local_score_clt (C.selectedPath z) 0 le_rfl p
    have hgauss : AsymptoticStatistics.WeakConverges
        (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
          (normalizedScoreSum p (χ k)))
        (gaussianReal 0 ⟨‖p‖ ^ 2, sq_nonneg _⟩) := by
      simpa only [zero_mul, (C.selectedPath z).curve_at_zero] using hscore.comp hχ
    exact AsymptoticStatistics.WeakConverges.unique hfromρ hgauss
  let scoreDiff : ((ℝ × ℝ) × (↥S → ℝ)) → ℝ := fun r =>
    pScore r - r.1.2
  have hscoreDiffMeas : Measurable scoreDiff := by
    dsimp only [scoreDiff]
    fun_prop
  have hsubScoreAE : ∀ k,
      (fun X : Fin (χ k) → Ω => normalizedScoreSum (p - φ) (χ k) X) =ᵐ[
        Measure.pi (fun _ : Fin (χ k) => P)]
      (fun X => normalizedScoreSum p (χ k) X - normalizedScoreSum φ (χ k) X) := by
    intro k
    have hcoe := Lp.coeFn_sub (p : Lp ℝ 2 P) (φ : Lp ℝ 2 P)
    have hcoord : ∀ i : Fin (χ k), (fun _ : Ω => True) ≤ᵐ[P]
        (fun ω => ((((p - φ : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω) =
          ((p : Lp ℝ 2 P) : Ω → ℝ) ω -
            ((φ : Lp ℝ 2 P) : Ω → ℝ) ω) :=
      fun _ => hcoe.mono fun _ h _ => h
    have hall := Measure.ae_le_pi hcoord
    filter_upwards [hall] with X hX
    simp only [normalizedScoreSum]
    rw [show (∑ i : Fin (χ k),
        (((p - φ : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) (X i)) =
        ∑ i : Fin (χ k), (((p : Lp ℝ 2 P) : Ω → ℝ) (X i) -
          ((φ : Lp ℝ 2 P) : Ω → ℝ) (X i)) by
      apply Finset.sum_congr rfl
      intro i _
      exact hX i trivial, Finset.sum_sub_distrib]
    ring
  have hscoreDiffLaw : ρ.map scoreDiff =
      gaussianReal 0 ⟨‖p - φ‖ ^ 2, sq_nonneg _⟩ := by
    have hfromρ : AsymptoticStatistics.WeakConverges
        (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
          (normalizedScoreSum (p - φ) (χ k))) (ρ.map scoreDiff) := by
      have hm := hρ.map (by fun_prop : Continuous scoreDiff) hscoreDiffMeas
      have hmap : ∀ k,
          ((Measure.pi (fun _ : Fin (χ k) => P)).map
            (fun X => ((centeredEstimator T_n (ψ P) (χ k) X,
              normalizedScoreSum φ (χ k) X),
              fun u : ↥S => normalizedScoreSum (u : ↥(L2ZeroMean P)) (χ k) X))).map
                scoreDiff =
            (Measure.pi (fun _ : Fin (χ k) => P)).map
              (normalizedScoreSum (p - φ) (χ k)) := by
        intro k
        rw [Measure.map_map hscoreDiffMeas (hextMeas k)]
        apply Measure.map_congr
        filter_upwards [hpScoreSourceAE k, hsubScoreAE k] with X hpX hsubX
        dsimp only [scoreDiff, pScore, Function.comp_apply]
        rw [← hpX, ← hsubX]
      simpa only [hmap] using hm
    have hscore := qmd_local_score_clt (C.selectedPath z) 0 le_rfl (p - φ)
    have hgauss : AsymptoticStatistics.WeakConverges
        (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
          (normalizedScoreSum (p - φ) (χ k)))
        (gaussianReal 0 ⟨‖p - φ‖ ^ 2, sq_nonneg _⟩) := by
      simpa only [zero_mul, (C.selectedPath z).curve_at_zero] using hscore.comp hχ
    exact AsymptoticStatistics.WeakConverges.unique hfromρ hgauss
  let tCoord : ((ℝ × ℝ) × (↥S → ℝ)) → ℝ := fun r => r.1.1
  let phiCoord : ((ℝ × ℝ) × (↥S → ℝ)) → ℝ := fun r => r.1.2
  have htCoordMeas : Measurable tCoord := by fun_prop
  have hphiCoordMeas : Measurable phiCoord := by fun_prop
  have htCoordLaw : ρ.map tCoord = gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩ := by
    calc
      ρ.map tCoord = (ρ.map Prod.fst).map Prod.fst := by
        rw [Measure.map_map measurable_fst measurable_fst]
        rfl
      _ = π.map Prod.fst := by rw [hρfst]
      _ = gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩ := hπfst
  have hphiCoordLaw : ρ.map phiCoord =
      gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩ := by
    calc
      ρ.map phiCoord = (ρ.map Prod.fst).map Prod.snd := by
        rw [Measure.map_map measurable_snd measurable_fst]
        rfl
      _ = π.map Prod.snd := by rw [hρfst]
      _ = gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩ := hπsnd
  have hTsq := integral_sq_eq_of_map_eq_gaussianReal ρ tCoord htCoordMeas
    ⟨‖φ‖ ^ 2, sq_nonneg _⟩ htCoordLaw
  have hphisq := integral_sq_eq_of_map_eq_gaussianReal ρ phiCoord hphiCoordMeas
    ⟨‖φ‖ ^ 2, sq_nonneg _⟩ hphiCoordLaw
  have hpsq := integral_sq_eq_of_map_eq_gaussianReal ρ pScore hpScoreMeas
    ⟨‖p‖ ^ 2, sq_nonneg _⟩ hpScoreLaw
  have hdiffsq := integral_sq_eq_of_map_eq_gaussianReal ρ scoreDiff hscoreDiffMeas
    ⟨‖p - φ‖ ^ 2, sq_nonneg _⟩ hscoreDiffLaw
  have hTminusPInt : Integrable
      (fun r : ((ℝ × ℝ) × (↥S → ℝ)) => (r.1.1 - pScore r) ^ 2) ρ := by
    have hcomb := (hTsq.1.sub (hTpInt.const_mul 2)).add hpsq.1
    exact hcomb.congr (Eventually.of_forall fun r => by
      simp only [Pi.add_apply, Pi.sub_apply, tCoord]
      ring)
  have hTminusP : ∫ r : ((ℝ × ℝ) × (↥S → ℝ)),
      (r.1.1 - pScore r) ^ 2 ∂ρ = ‖φ - p‖ ^ 2 := by
    have hTsqInt : Integrable
        (fun r : ((ℝ × ℝ) × (↥S → ℝ)) => r.1.1 ^ 2) ρ := by
      simpa only [tCoord] using hTsq.1
    have hTsqVal : ∫ r : ((ℝ × ℝ) × (↥S → ℝ)), r.1.1 ^ 2 ∂ρ =
        ‖φ‖ ^ 2 := by simpa only [tCoord] using! hTsq.2
    have hpsqVal : ∫ r : ((ℝ × ℝ) × (↥S → ℝ)), pScore r ^ 2 ∂ρ =
        ‖p‖ ^ 2 := by simpa using! hpsq.2
    calc
      ∫ r, (r.1.1 - pScore r) ^ 2 ∂ρ =
          ∫ r, (r.1.1 ^ 2 - 2 * (r.1.1 * pScore r)) + pScore r ^ 2 ∂ρ := by
            congr 1
            funext r
            ring
      _ = (∫ r, r.1.1 ^ 2 ∂ρ) - 2 * (∫ r, r.1.1 * pScore r ∂ρ) +
          ∫ r, pScore r ^ 2 ∂ρ := by
        calc
          ∫ r, (r.1.1 ^ 2 - 2 * (r.1.1 * pScore r)) + pScore r ^ 2 ∂ρ =
              (∫ r, r.1.1 ^ 2 - 2 * (r.1.1 * pScore r) ∂ρ) +
                ∫ r, pScore r ^ 2 ∂ρ := by
            exact integral_add (hTsqInt.sub (hTpInt.const_mul 2)) hpsq.1
          _ = ((∫ r, r.1.1 ^ 2 ∂ρ) -
              ∫ r, 2 * (r.1.1 * pScore r) ∂ρ) + ∫ r, pScore r ^ 2 ∂ρ := by
            rw [integral_sub hTsqInt (hTpInt.const_mul 2)]
          _ = (∫ r, r.1.1 ^ 2 ∂ρ) - 2 *
              (∫ r, r.1.1 * pScore r ∂ρ) + ∫ r, pScore r ^ 2 ∂ρ := by
            rw [integral_const_mul]
      _ = ‖φ‖ ^ 2 - 2 * ⟪φ, p⟫_ℝ + ‖p‖ ^ 2 := by
        rw [hTsqVal, hTp, hpsqVal]
      _ = ‖φ - p‖ ^ 2 := by rw [norm_sub_sq_real]
  have hRhsInt : Integrable (fun r : ((ℝ × ℝ) × (↥S → ℝ)) =>
      2 * (r.1.1 - pScore r) ^ 2 + 2 * scoreDiff r ^ 2) ρ :=
    (hTminusPInt.const_mul 2).add (hdiffsq.1.const_mul 2)
  have hresLe : ∀ r : ((ℝ × ℝ) × (↥S → ℝ)),
      (r.1.1 - r.1.2) ^ 2 ≤
        2 * (r.1.1 - pScore r) ^ 2 + 2 * scoreDiff r ^ 2 := by
    intro r
    dsimp only [scoreDiff]
    nlinarith [sq_nonneg ((r.1.1 - pScore r) - (pScore r - r.1.2))]
  have hresIntρ : Integrable
      (fun r : ((ℝ × ℝ) × (↥S → ℝ)) => (r.1.1 - r.1.2) ^ 2) ρ := by
    refine hRhsInt.mono' (by fun_prop) ?_
    exact Eventually.of_forall fun r => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (r.1.1 - r.1.2))] using hresLe r
  have hboundρ : ∫ r : ((ℝ × ℝ) × (↥S → ℝ)),
      (r.1.1 - r.1.2) ^ 2 ∂ρ ≤ 4 * ‖φ - p‖ ^ 2 := by
    have hdiffsqVal : ∫ r : ((ℝ × ℝ) × (↥S → ℝ)), scoreDiff r ^ 2 ∂ρ =
        ‖p - φ‖ ^ 2 := hdiffsq.2
    calc
      ∫ r, (r.1.1 - r.1.2) ^ 2 ∂ρ ≤
          ∫ r, 2 * (r.1.1 - pScore r) ^ 2 + 2 * scoreDiff r ^ 2 ∂ρ :=
        integral_mono_ae hresIntρ hRhsInt (Eventually.of_forall hresLe)
      _ = 2 * ‖φ - p‖ ^ 2 + 2 * ‖p - φ‖ ^ 2 := by
        rw [integral_add (hTminusPInt.const_mul 2) (hdiffsq.1.const_mul 2),
          integral_const_mul, integral_const_mul, hTminusP, hdiffsqVal]
      _ = 4 * ‖φ - p‖ ^ 2 := by rw [norm_sub_rev]; ring
  have hsecond : ∫ q : ℝ × ℝ, (q.1 - q.2) ^ 2 ∂π ≤
      4 * ‖φ - p‖ ^ 2 := by
    calc
      ∫ q : ℝ × ℝ, (q.1 - q.2) ^ 2 ∂π =
          ∫ r : ((ℝ × ℝ) × (↥S → ℝ)), (r.1.1 - r.1.2) ^ 2 ∂ρ := by
        rw [← hρfst, integral_map measurable_fst.aemeasurable (by fun_prop)]
      _ ≤ 4 * ‖φ - p‖ ^ 2 := hboundρ
  have hresIntπ : Integrable (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) π := by
    have hm : Integrable (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) (ρ.map Prod.fst) :=
      (integrable_map_measure (by fun_prop) measurable_fst.aemeasurable).2
        (by simpa only [Function.comp_apply] using! hresIntρ)
    rwa [hρfst] at hm
  refine ⟨hsecond, ?_⟩
  intro ε hε
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := π) (f := fun q : ℝ × ℝ => (q.1 - q.2) ^ 2)
    (Eventually.of_forall fun _ => sq_nonneg _) hresIntπ (ε ^ 2)
  have hset : {q : ℝ × ℝ | ε ^ 2 ≤ (q.1 - q.2) ^ 2} =
      {q | ε ≤ |q.1 - q.2|} := by
    ext q
    simp only [Set.mem_setOf_eq]
    simpa [sq_abs] using (sq_le_sq₀ hε.le (abs_nonneg (q.1 - q.2)))
  rw [hset] at hm
  have hd2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  calc
    (π {q | ε ≤ |q.1 - q.2|}).toReal ≤
        (∫ q, (q.1 - q.2) ^ 2 ∂π) / ε ^ 2 :=
      (le_div_iff₀ hd2).2 (by simpa [mul_comm] using! hm)
    _ ≤ 4 * ‖φ - p‖ ^ 2 / ε ^ 2 := by
      exact div_le_div_of_nonneg_right hsecond hd2.le

/-- Outer projection exhaustion forces every baseline residual subsequential
limit to be `dirac 0`.

Proof idea: invoke `proj_seq_to_eif_nd C hEIF.2`, internally extract finite
joint extensions, and send the preceding `4‖φ-p‖²` bound to zero.
-/
theorem residual_subseq_limit_eq_dirac_of_regular
    {T_n : ∀ n, (Fin n → Ω) → ℝ} {ψ : Measure Ω → ℝ}
    (C : NondominatedTangentCone P)
    (hpd : NondominatedPathwiseDifferentiableAt P C ψ)
    {φ : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace C) hpd.derivative φ)
    (hT : ∀ n, Measurable (T_n n))
    (hreg : IsRegularAtND C T_n ψ
      (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩))
    (χ : ℕ → ℕ) (hχ : StrictMono χ)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hπ : AsymptoticStatistics.WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
          normalizedScoreSum φ (χ k) X))) π) :
    π.map (fun q : ℝ × ℝ => q.1 - q.2) = Measure.dirac 0 := by
  classical
  rcases proj_seq_to_eif_nd C hEIF.2 with
    ⟨V, p, hVle, hVmono, hVfin, hVspan, hproj, hpconv⟩
  have htailBound : ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      (π {q | ε ≤ |q.1 - q.2|}).toReal ≤
        4 * ‖φ - p m‖ ^ 2 / ε ^ 2 := by
    intro m ε hε
    rcases hVspan m with ⟨S, hS, hVS⟩
    have hpS : p m ∈ Submodule.span ℝ (↑S : Set ↥(L2ZeroMean P)) := by
      rw [← hVS]
      exact (hproj m).1
    let pairSeq : ℕ → Measure (ℝ × ℝ) := fun k =>
      (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (centeredEstimator T_n (ψ P) (χ k) X,
          normalizedScoreSum φ (χ k) X))
    let vecSeq : ℕ → Measure (↥S → ℝ) := fun k =>
      (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => fun g : ↥S =>
          normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X)
    let joint : ℕ → Measure ((ℝ × ℝ) × (↥S → ℝ)) := fun k =>
      (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => ((centeredEstimator T_n (ψ P) (χ k) X,
          normalizedScoreSum φ (χ k) X),
          fun g : ↥S => normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X))
    have hscoreMeas : ∀ (u : ↥(L2ZeroMean P)) k,
        Measurable (normalizedScoreSum u (χ k)) := by
      intro u k
      unfold normalizedScoreSum
      exact Measurable.const_mul
        (Finset.measurable_sum _ fun i _ =>
          (Lp.stronglyMeasurable (u : Lp ℝ 2 P)).measurable.comp
            (measurable_pi_apply i)) _
    have hpairMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
        (centeredEstimator T_n (ψ P) (χ k) X,
          normalizedScoreSum φ (χ k) X)) := by
      intro k
      exact (Measurable.const_mul ((hT (χ k)).sub_const _) _).prodMk
        (hscoreMeas φ k)
    have hvecMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
        fun g : ↥S => normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X) := by
      intro k
      exact measurable_pi_lambda _ fun g => hscoreMeas (g : ↥(L2ZeroMean P)) k
    have hjointMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
        ((centeredEstimator T_n (ψ P) (χ k) X,
          normalizedScoreSum φ (χ k) X),
          fun g : ↥S => normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k) X)) :=
      fun k => (hpairMeas k).prodMk (hvecMeas k)
    haveI hpairProb : ∀ k, IsProbabilityMeasure (pairSeq k) := fun k =>
      Measure.isProbabilityMeasure_map (hpairMeas k).aemeasurable
    haveI hvecProb : ∀ k, IsProbabilityMeasure (vecSeq k) := fun k =>
      Measure.isProbabilityMeasure_map (hvecMeas k).aemeasurable
    haveI hjointProb : ∀ k, IsProbabilityMeasure (joint k) := fun k =>
      Measure.isProbabilityMeasure_map (hjointMeas k).aemeasurable
    have hpairTight : IsTightMeasureSet (Set.range pairSeq) :=
      Prohorov.weakConverges_range_tight pairSeq π (by simpa only [pairSeq] using hπ)
    let z : {g : ↥(L2ZeroMean P) // g ∈ C.carrier} := ⟨0, zero_mem C⟩
    let coordSeq : ↥S → ℕ → Measure ℝ := fun g k =>
      (Measure.pi (fun _ : Fin (χ k) => P)).map
        (normalizedScoreSum (g : ↥(L2ZeroMean P)) (χ k))
    haveI hcoordProb : ∀ (g : ↥S) k, IsProbabilityMeasure (coordSeq g k) := fun g k =>
      Measure.isProbabilityMeasure_map (hscoreMeas (g : ↥(L2ZeroMean P)) k).aemeasurable
    have hcoordTight : ∀ g : ↥S, IsTightMeasureSet (Set.range (coordSeq g)) := by
      intro g
      have hs := qmd_local_score_clt (C.selectedPath z) 0 le_rfl
        (g : ↥(L2ZeroMean P))
      have hw : AsymptoticStatistics.WeakConverges (coordSeq g)
          (gaussianReal 0 ⟨‖(g : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩) := by
        simpa only [coordSeq, zero_mul, (C.selectedPath z).curve_at_zero] using
          hs.comp hχ
      exact Prohorov.weakConverges_range_tight (coordSeq g)
        (gaussianReal 0 ⟨‖(g : ↥(L2ZeroMean P))‖ ^ 2, sq_nonneg _⟩) hw
    have hcoordMarg : ∀ (g : ↥S) k,
        (vecSeq k).map (fun x => x g) = coordSeq g k := by
      intro g k
      simp only [vecSeq, coordSeq, Measure.map_map (by fun_prop : Measurable fun x : ↥S → ℝ => x g)
        (hvecMeas k)]
      rfl
    have hvecTight : IsTightMeasureSet (Set.range vecSeq) := by
      rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
      intro δ hδ
      let d : ℝ≥0∞ := δ / ((Fintype.card ↥S : ℝ≥0∞) + 1)
      have hd : 0 < d := by
        rw [ENNReal.div_pos_iff]
        exact ⟨hδ.ne', by simp⟩
      have hKexists : ∀ g : ↥S, ∃ K : Set ℝ, IsCompact K ∧
          ∀ μ ∈ Set.range (coordSeq g), μ Kᶜ ≤ d := by
        intro g
        exact (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
          (hcoordTight g)) d hd
      choose K hKcomp hKbound using hKexists
      refine ⟨Set.pi Set.univ K, isCompact_univ_pi hKcomp, ?_⟩
      intro μ hμ
      rcases hμ with ⟨k, rfl⟩
      let bad : ↥S → Set (↥S → ℝ) := fun g =>
        (fun x => x g) ⁻¹' (K g)ᶜ
      have hcompl : (Set.pi Set.univ K)ᶜ ⊆ ⋃ g, bad g := by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, forall_true_left,
          not_forall] at hx
        rcases hx with ⟨g, hg⟩
        exact Set.mem_iUnion.2 ⟨g, hg⟩
      have hbad : ∀ g : ↥S, vecSeq k (bad g) ≤ d := by
        intro g
        calc
          vecSeq k (bad g) = (vecSeq k).map (fun x => x g) (K g)ᶜ := by
            rw [Measure.map_apply (by fun_prop) (hKcomp g).measurableSet.compl]
          _ = coordSeq g k (K g)ᶜ := by rw [hcoordMarg]
          _ ≤ d := hKbound g _ ⟨k, rfl⟩
      calc
        vecSeq k (Set.pi Set.univ K)ᶜ ≤ vecSeq k (⋃ g, bad g) := measure_mono hcompl
        _ ≤ ∑' g : ↥S, vecSeq k (bad g) := MeasureTheory.measure_iUnion_le bad
        _ = ∑ g : ↥S, vecSeq k (bad g) := tsum_fintype _
        _ ≤ ∑ _g : ↥S, d := Finset.sum_le_sum fun g _ => hbad g
        _ = (Fintype.card ↥S : ℝ≥0∞) * d := by simp
        _ ≤ ((Fintype.card ↥S : ℝ≥0∞) + 1) * d := by
          gcongr
          exact le_add_right le_rfl
        _ = δ := by
          dsimp only [d]
          exact ENNReal.mul_div_cancel (by simp) (by simp)
    have hmargFst : ∀ k, (joint k).map Prod.fst = pairSeq k := by
      intro k
      simp only [joint, pairSeq, Measure.map_map measurable_fst (hjointMeas k)]
      rfl
    have hmargSnd : ∀ k, (joint k).map Prod.snd = vecSeq k := by
      intro k
      simp only [joint, vecSeq, Measure.map_map measurable_snd (hjointMeas k)]
      rfl
    have hfstImage :
        (fun μ : Measure ((ℝ × ℝ) × (↥S → ℝ)) => μ.map Prod.fst) ''
            Set.range joint = Set.range pairSeq := by
      ext μ
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, (hmargFst k).symm⟩
      · rintro ⟨k, rfl⟩
        exact ⟨joint k, ⟨k, rfl⟩, hmargFst k⟩
    have hsndImage :
        (fun μ : Measure ((ℝ × ℝ) × (↥S → ℝ)) => μ.map Prod.snd) ''
            Set.range joint = Set.range vecSeq := by
      ext μ
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, (hmargSnd k).symm⟩
      · rintro ⟨k, rfl⟩
        exact ⟨joint k, ⟨k, rfl⟩, hmargSnd k⟩
    have hjointTight : IsTightMeasureSet (Set.range joint) :=
      Prohorov.tight_prod_of_tight_marginals _
        (hfstImage ▸ hpairTight) (hsndImage ▸ hvecTight)
    obtain ⟨σ, hσ, ρ, hρprob, hρweak⟩ :=
      Prohorov.extract_weak_subseq joint hjointTight
    letI : IsProbabilityMeasure ρ := hρprob
    have hbound := residual_secondMoment_bound_of_finset_extension C hpd hEIF hT hreg
      S hS (p m) hpS (χ ∘ σ) (hχ.comp hσ) π (hπ.comp hσ) ρ
      (by simpa only [joint, Function.comp_apply] using hρweak)
    exact hbound.2 ε hε
  have hnorm : Tendsto (fun m => ‖φ - p m‖) atTop (nhds 0) := by
    simpa only [norm_sub_rev] using hpconv
  have htailZero : ∀ ε : ℝ, 0 < ε →
      (π {q | ε ≤ |q.1 - q.2|}).toReal = 0 := by
    intro ε hε
    have hrhs : Tendsto (fun m => 4 * ‖φ - p m‖ ^ 2 / ε ^ 2) atTop (nhds 0) := by
      have h4 : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4) := tendsto_const_nhds
      have h := (h4.mul (hnorm.pow 2)).div_const (ε ^ 2)
      simpa using h
    apply le_antisymm
    · exact ge_of_tendsto' hrhs fun m => htailBound m ε hε
    · exact measureReal_nonneg
  let bad : Set (ℝ × ℝ) := {q | q.1 - q.2 ≠ 0}
  let tail : ℕ → Set (ℝ × ℝ) := fun n =>
    {q | ((n + 1 : ℕ) : ℝ)⁻¹ ≤ |q.1 - q.2|}
  have htailNull : ∀ n, π (tail n) = 0 := by
    intro n
    apply (measureReal_eq_zero_iff (measure_ne_top π _)).mp
    simpa only [tail] using! htailZero (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)
  have hbadSub : bad ⊆ ⋃ n, tail n := by
    intro q hq
    have habs : 0 < |q.1 - q.2| := abs_pos.mpr hq
    obtain ⟨n, hn⟩ := exists_nat_gt |q.1 - q.2|⁻¹
    have hn' : |q.1 - q.2|⁻¹ < ((n + 1 : ℕ) : ℝ) :=
      hn.trans (by exact_mod_cast Nat.lt_succ_self n)
    have hinv : (((n + 1 : ℕ) : ℝ)⁻¹ < |q.1 - q.2|) :=
      (inv_lt_comm₀ habs (by positivity)).mp hn'
    exact Set.mem_iUnion.2 ⟨n, by simpa only [tail, Set.mem_setOf_eq] using hinv.le⟩
  have hbadNull : π bad = 0 := by
    apply le_antisymm
    · exact (measure_mono hbadSub).trans_eq
        (MeasureTheory.measure_iUnion_null htailNull)
    · exact bot_le
  have hresAE : (fun q : ℝ × ℝ => q.1 - q.2) =ᵐ[π] fun _ => 0 := by
    have hgood : ∀ᵐ q ∂π, q ∉ bad := compl_mem_ae_iff.2 hbadNull
    filter_upwards [hgood] with q hq
    simpa only [bad, Set.mem_setOf_eq, not_not] using hq
  calc
    π.map (fun q : ℝ × ℝ => q.1 - q.2) = π.map (fun _ => 0) :=
      Measure.map_congr hresAE
    _ = Measure.dirac 0 := by simp

end AsymptoticStatistics.LowerBounds.NondominatedOperationalEfficiencyAnalytic
