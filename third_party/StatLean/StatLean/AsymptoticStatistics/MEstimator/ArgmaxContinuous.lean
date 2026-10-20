module
public import StatLean.AsymptoticStatistics.MEstimator.Argmax

@[expose] public section

/-!
# Continuous-path argmax corollary

Book-facing Corollary 5.58.  The proof route is the refined shared closed-set
core from `Argmax.lean`, not the joint-pair hypothesis of Theorem 5.56, because
that pair convergence may fail for changing parameter sets.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics.MEstimator

/-- A continuous real-valued function is uniformly bounded on a compact set,
so its restriction defines an element of the local `ℓ∞(K)` carrier.

This packages compact-image boundedness in the `Memℓp ∞` form
required by `ForMathlib.restrictToLinfOn`; it is derived data, not a
book-facing regularity assumption. -/
theorem continuous_memℓp_infty_on_compact
    {D : Type*} [TopologicalSpace D] (f : D → ℝ) (K : Set D)
    (hf : Continuous f) (hK : IsCompact K) :
    Memℓp (fun h : K => f h) ∞ := by
  refine memℓp_infty ?_
  obtain ⟨C, hC⟩ := hK.bddAbove_image hf.norm.continuousOn
  refine ⟨C, ?_⟩
  rintro _ ⟨h, rfl⟩
  exact hC ⟨h, h.2, rfl⟩

/-- A continuous real path with a unique maximum on closed `H` is well
separated on every compact localization set (vdV proof of Corollary 5.58,
p.81). Closedness makes `Gᶜ ∩ K ∩ H` compact and is derived from
`SetConverges.limit_closed` by the corollary assembly. -/
theorem continuous_uniqueMax_wellSeparatedOn_compact
    {D : Type*} [MetricSpace D] (z : D → ℝ) (H K G : Set D) (hhat : D)
    (hz : Continuous z) (hHclosed : IsClosed H) (hK : IsCompact K)
    (hG : IsOpen G) (hhG : hhat ∈ G)
    (hunique : ∀ h ∈ H, h ≠ hhat → z h < z hhat) :
    ForMathlib.setSupEReal z (Gᶜ ∩ K ∩ H) < (z hhat : EReal) := by
  have hAcompact : IsCompact (Gᶜ ∩ K ∩ H) := by
    have hcompact := (hK.inter_right hG.isClosed_compl).inter_right hHclosed
    simpa only [inter_assoc, inter_comm, inter_left_comm] using hcompact
  by_cases hA : (Gᶜ ∩ K ∩ H).Nonempty
  · obtain ⟨x, hx, hxmax⟩ :=
      hAcompact.exists_isMaxOn hA hz.continuousOn
    calc
      ForMathlib.setSupEReal z (Gᶜ ∩ K ∩ H) ≤ (z x : EReal) := by
        unfold ForMathlib.setSupEReal
        exact iSup_le fun y => EReal.coe_le_coe_iff.mpr (hxmax y.2)
      _ < (z hhat : EReal) := EReal.coe_lt_coe_iff.mpr <| by
        apply hunique x hx.2
        intro hxeq
        subst x
        exact hx.1.1 hhG
  · have hempty : Gᶜ ∩ K ∩ H = ∅ := not_nonempty_iff_eq_empty.mp hA
    simp [ForMathlib.setSupEReal, hempty]

/-- Uniform compact containment of the sample estimators and tightness of the
measurable Euclidean limit law admit one common positive-radius closed ball:
the sample estimators lie in the closed ball uniformly, while the limit lies
in its interior.

This is localization infrastructure only.  It contains no process comparison
or argmax-convergence conclusion.  The strict enlargement uses compact
boundedness together with `closedBall_subset_ball` and
`ball_subset_interior_closedBall`; it also covers dimension zero. -/
theorem exists_large_closedBall_localization
    {Ω Ωlim : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωlim]
    {d : ℕ} {μ : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (μ n)]
    {μlim : Measure Ωlim} [IsProbabilityMeasure μlim]
    (hhatn : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hhat : Ωlim → EuclideanSpace ℝ (Fin d)) (hhmeas : Measurable hhat)
    (htight : ∀ ε : ℝ, 0 < ε →
      ∃ C : Set (EuclideanSpace ℝ (Fin d)), IsCompact C ∧
        (⨆ n, (μ n).outerMeasureStar {ω | hhatn n ω ∉ C}) < ENNReal.ofReal ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
      (⨆ n, (μ n).outerMeasureStar
        {ω | hhatn n ω ∉ Metric.closedBall 0 R}) < ENNReal.ofReal ε ∧
      μlim {ω | hhat ω ∉ interior (Metric.closedBall 0 R)} < ENNReal.ofReal ε := by
  obtain ⟨C, hCcompact, hCsample⟩ := htight ε hε
  let ν : Measure (EuclideanSpace ℝ (Fin d)) := μlim.map hhat
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hhmeas.aemeasurable
  have hνtight : IsTightMeasureSet ({ν} : Set (Measure (EuclideanSpace ℝ (Fin d)))) :=
    isTightMeasureSet_singleton
  obtain ⟨L, hLcompact, hLmass⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hνtight)
      (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos hε))
  have hCLbounded : Bornology.IsBounded (C ∪ L) :=
    hCcompact.isBounded.union hLcompact.isBounded
  obtain ⟨R, hRpos, hCLball⟩ := hCLbounded.subset_ball_lt 0 0
  have hCsub : C ⊆ Metric.closedBall 0 R :=
    Set.Subset.trans (fun x hx => hCLball (Or.inl hx)) Metric.ball_subset_closedBall
  have hLsub : L ⊆ interior (Metric.closedBall 0 R) :=
    Set.Subset.trans (fun x hx => hCLball (Or.inr hx))
      Metric.ball_subset_interior_closedBall
  have houter_mono : ∀ (m : Measure Ω) {A B : Set Ω}, A ⊆ B →
      m.outerMeasureStar A ≤ m.outerMeasureStar B := by
    intro m A B hAB
    unfold Measure.outerMeasureStar
    refine outerExpectation_mono fun ω => ?_
    by_cases hω : ω ∈ A
    · simp [hω, hAB hω]
    · simp [hω]
  refine ⟨R, hRpos, ?_, ?_⟩
  · apply lt_of_le_of_lt _ hCsample
    refine iSup_le fun n => le_iSup_of_le n (houter_mono (μ n) ?_)
    intro ω hω hωC
    exact hω (hCsub hωC)
  · calc
      μlim {ω | hhat ω ∉ interior (Metric.closedBall 0 R)} =
          ν ((interior (Metric.closedBall 0 R))ᶜ) := by
            rw [Measure.map_apply hhmeas isOpen_interior.measurableSet.compl]
            rfl
      _ ≤ ν (Lᶜ) := measure_mono (compl_subset_compl.mpr hLsub)
      _ ≤ ENNReal.ofReal (ε / 2) := hLmass ν rfl
      _ < ENNReal.ofReal ε :=
        (ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε)

/-- **van der Vaart Corollary 5.58.**

On `ℝᵈ`, continuous limit paths with a unique maximizer, local outer weak
convergence in `ℓ∞(K)` for every compact `K`, changing-set convergence
`Hₙ → H`, near-maximization, membership, and uniform tightness imply outer weak
convergence of the argmax estimators.

The local process hypothesis is intentionally not replaced by the pair
convergence assumption of Theorem 5.56: vdV p.81 explicitly notes that the
latter may fail when `Hₙ` changes. -/
theorem argmax_continuous_corollary
    {Ω Ωlim : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωlim]
    {d : ℕ}
    {μ : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (μ n)]
    {μlim : Measure Ωlim} [IsProbabilityMeasure μlim]
    (Mn : ℕ → Ω → EuclideanSpace ℝ (Fin d) → ℝ)
    (M : Ωlim → EuclideanSpace ℝ (Fin d) → ℝ)
    (Hn : ℕ → Set (EuclideanSpace ℝ (Fin d)))
    (H : Set (EuclideanSpace ℝ (Fin d)))
    -- USER-INPUT: convergence of the changing index sets, as in vdV Corollary 5.58.
    (hset : ForMathlib.SetConverges Hn H)
    (hhatn : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hhat : Ωlim → EuclideanSpace ℝ (Fin d))
    -- LEAN-ONLY: measurability of the limiting argmax.
    (hhmeas : Measurable hhat)
    -- USER-INPUT: the sample and limiting argmaxes lie in their index sets;
    -- vdV Corollary 5.58.
    (hmemn : ∀ n ω, hhatn n ω ∈ Hn n)
    (hmem : ∀ ω, hhat ω ∈ H)
    (r : ℕ → Ω → ℝ)
    -- LEAN-ONLY: the approximation remainder is represented as nonnegative.
    (hrnonneg : ∀ n ω, 0 ≤ r n ω)
    -- USER-INPUT: near-maximization with an `o_P(1)` remainder;
    -- vdV Corollary 5.58.
    (hr : TendstoInOuterProbabilityZero μ r)
    (hnear : ∀ n ω h, h ∈ Hn n →
      Mn n ω h ≤ Mn n ω (hhatn n ω) + r n ω)
    -- USER-INPUT: continuous limit paths with a unique maximizer;
    -- vdV Corollary 5.58.
    (hcontinuous : ∀ ω, Continuous (M ω))
    (hunique : ∀ ω h, h ∈ H → h ≠ hhat ω → M ω h < M ω (hhat ω))
    -- LEAN-ONLY: boundedness and measurability needed to realize restrictions in `ℓ∞(K)`.
    (hMnBounded : ∀ n ω (K : Set (EuclideanSpace ℝ (Fin d))), IsCompact K →
      Memℓp (fun h : K => Mn n ω h) ∞)
    (hLocalMeas : ∀ (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K),
      Measurable (fun ω => ForMathlib.restrictToLinfOn K (M ω)
        (continuous_memℓp_infty_on_compact (M ω) K (hcontinuous ω) hK)))
    -- USER-INPUT: local outer weak convergence and uniform tightness;
    -- vdV Corollary 5.58.
    (hlocal : ∀ (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K),
      WeakConvergesOuter μ
        (fun n ω => ForMathlib.restrictToLinfOn K (Mn n ω) (hMnBounded n ω K hK))
        (μlim.map (fun ω =>
          ForMathlib.restrictToLinfOn K (M ω)
            (continuous_memℓp_infty_on_compact (M ω) K (hcontinuous ω) hK))))
    (htight : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K ∧
        (⨆ n, (μ n).outerMeasureStar {ω | hhatn n ω ∉ K}) < ENNReal.ofReal ε) :
    WeakConvergesOuter μ hhatn (μlim.map hhat) := by
  have hHclosed : IsClosed H := hset.limit_closed
  let 𝓛 : Set (Set (EuclideanSpace ℝ (Fin d)) ×
      Set (EuclideanSpace ℝ (Fin d))) :=
    {p | ∃ R : ℝ, 0 < R ∧
      p = (Metric.closedBall 0 R, interior (Metric.closedBall 0 R))}
  refine argmax_closed_limsup Mn M Hn H 𝓛 hhatn hhat hhmeas hmemn
    (Eventually.of_forall hmem) r hnear ?_ ?_ ?_
  · intro G hG p hp
    filter_upwards with ω
    intro hhG
    obtain ⟨R, hR, rfl⟩ := hp
    exact continuous_uniqueMax_wellSeparatedOn_compact
      (M ω) H (Metric.closedBall 0 R) G (hhat ω)
      (hcontinuous ω) hHclosed (isCompact_closedBall 0 R)
      hG hhG (hunique ω)
  · intro ε hε
    obtain ⟨R, hR, hsample, hlimit⟩ :=
      exists_large_closedBall_localization (μ := μ) (μlim := μlim)
        hhatn hhat hhmeas htight ε hε
    exact ⟨(Metric.closedBall 0 R, interior (Metric.closedBall 0 R)),
      ⟨R, hR, rfl⟩, hsample, hlimit⟩
  · intro F p hF hp
    obtain ⟨R, hR, rfl⟩ := hp
    let K : Set (EuclideanSpace ℝ (Fin d)) := Metric.closedBall 0 R
    have hK : IsCompact K := isCompact_closedBall 0 R
    have hFK : IsCompact (F ∩ K) := hK.inter_left hF
    let Zn : ℕ → Ω → ForMathlib.LinfOn K := fun n ω =>
      ForMathlib.restrictToLinfOn K (Mn n ω) (hMnBounded n ω K hK)
    let Z : Ωlim → ForMathlib.LinfOn K := fun ω =>
      ForMathlib.restrictToLinfOn K (M ω)
        (continuous_memℓp_infty_on_compact (M ω) K (hcontinuous ω) hK)
    have hZmeas : Measurable Z := by
      simpa only [Z] using hLocalMeas K hK
    have hZ : WeakConvergesOuter μ Zn (μlim.map Z) := by
      simpa only [Zn, Z] using hlocal K hK
    have hZcontinuous : ∀ᵐ ω ∂μlim, Continuous (Z ω) :=
      Eventually.of_forall fun ω => by
        change Continuous (fun h : K => M ω h)
        exact (hcontinuous ω).comp continuous_subtype_val
    have hcomparison := outer_supComparison_limsup_of_local_linf
      (μ := μ) (μlim := μlim) (F := F ∩ K) (K := K)
      hset hFK hK inter_subset_right Zn Z hZmeas hZ hZcontinuous
      r hrnonneg hr
    simpa only [K, Zn, Z, ForMathlib.linfSetSup_restrictToLinfOn,
      inter_assoc, inter_left_comm, inter_comm, inter_self,
      inter_eq_left.mpr interior_subset, inter_eq_right.mpr interior_subset] using hcomparison

end AsymptoticStatistics.MEstimator
