module
public import StatLean.AsymptoticStatistics.LowerBounds.LAMUnboundedRecenter
public import StatLean.AsymptoticStatistics.LowerBounds.NondominatedFiniteExperimentMinimax
public import StatLean.AsymptoticStatistics.Core.PathwiseVec
public import StatLean.AsymptoticStatistics.Core.EIFVec

@[expose] public section

/-! # Full semiparametric LAM theorem for a genuine convex tangent cone -/
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace AsymptoticStatistics.LowerBounds.LAMSemiparametricCone
open AsymptoticStatistics
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.PathwiseVec
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.Core.NondominatedTangent
open AsymptoticStatistics.Core.NondominatedPathwise
open AsymptoticStatistics.LowerBounds
open AsymptoticStatistics.LowerBounds.NondominatedFiniteExperimentMinimax

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {d : ℕ}

/-- Compactly-supported action laws are jointly tight and admit weakly
convergent subsequences. -/
theorem bounded_compact_action_product_tightness
    (K : Set (EuclideanSpace ℝ (Fin d))) (_hK : IsCompact K)
    (μn : ℕ → Measure (EuclideanSpace ℝ (Fin d)))
    (_hprob : ∀ n, IsProbabilityMeasure (μn n))
    (_hsupp : ∀ n, μn n K = 1) :
    IsTightMeasureSet (Set.range μn) ∧
      ∃ μ : Measure (EuclideanSpace ℝ (Fin d)),
        IsProbabilityMeasure μ ∧ ∃ ns : ℕ → ℕ, StrictMono ns ∧
          AsymptoticStatistics.WeakConverges (fun k => μn (ns k)) μ := by
  have htight : IsTightMeasureSet (Set.range μn) := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε _hε
    refine ⟨K, _hK, ?_⟩
    rintro _ ⟨n, rfl⟩
    letI : IsProbabilityMeasure (μn n) := _hprob n
    rw [measure_compl _hK.measurableSet (measure_ne_top (μn n) K),
      measure_univ, _hsupp n]
    simp
  letI (n : ℕ) : IsProbabilityMeasure (μn n) := _hprob n
  obtain ⟨ns, hns, μ, hμ, hweak⟩ :=
    AsymptoticStatistics.Prohorov.extract_weak_subseq μn htight
  exact ⟨htight, μ, hμ, ns, hns, hweak⟩

/-- If the effective action set contains zero, its best shifted loss is no
larger than the unshifted loss.  Compactness and bowl shape are unnecessary. -/
theorem gaussian_boundary_actions_no_improvement
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (_h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K) :
    ∀ x, ℓ x ≥ ⨅ y : K, ℓ (x - y) := by
  intro x
  exact (iInf_le_of_le ⟨0, _h0⟩ (by simp)).trans_eq rfl

/-- Pointwise finite-subset liminf passage used after compactification. -/
theorem finiteSubset_liminf_passage
    (f : ℕ → ↥(L2ZeroMean P) → ℝ≥0∞) (I : Finset ↥(L2ZeroMean P)) :
    (⨆ g ∈ I, Filter.liminf (fun n => f n g) atTop) ≤
      Filter.liminf (fun n => ⨆ g ∈ I, f n g) atTop := by
  refine iSup_le fun g => iSup_le fun hg => ?_
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)
  exact le_iSup_of_le g (le_iSup_of_le hg le_rfl)

private theorem nondominated_minimax_core
    (C : NondominatedTangentCone P)
    (hconv : Convex ℝ C.carrier)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : NondominatedPathwiseDifferentiableAtVec P C ψ)
    {φ : Fin d → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec hpd.derivative φ)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (hT : ∀ n, Measurable (T_n n))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hbowl : BowlShaped ℓ) (hlsc : LowerSemicontinuous ℓ) :
    selectedPathCanonicalLHSVec C T_n ψ ℓ ≥
      ∫⁻ y, ℓ y ∂(multivariateGaussian 0 (Matrix.gram ℝ φ)) := by
  exact (finiteCarrierChart_exhausts_eifGram C hconv hpd hEIF ℓ hbowl hlsc).trans
    (gaussianConeKernelRisk_le_selectedPathCanonicalLHSVec
      C hconv hpd T_n hT ℓ hbowl hlsc)

private noncomputable def commonDominatorCone
    (T_set : TangentSpec P)
    (h0 : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (hcone : ∀ x ∈ T_set.carrier, ∀ t : ℝ, 0 ≤ t →
      t • x ∈ T_set.carrier) :
    NondominatedTangentCone P where
  carrier := T_set.carrier
  carrier_nonempty := ⟨0, h0⟩
  nonneg_smul_mem := fun {a} ha {g} hg => hcone g hg a ha
  selectedPath := fun g =>
    AsymptoticStatistics.Core.NondominatedQMDPath.QMDPath.toNondominatedQMDPath
      (AsymptoticStatistics.LowerBounds.RegularEstimator.canonicalPath
        (g : ↥(L2ZeroMean P)))
  selectedPath_score := fun g =>
    AsymptoticStatistics.LowerBounds.RegularEstimator.canonicalPath_score
      (g : ↥(L2ZeroMean P))

private theorem commonDominatorCone_tangentSpace_eq
    (T_set : TangentSpec P)
    (h0 : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (hcone : ∀ x ∈ T_set.carrier, ∀ t : ℝ, 0 ≤ t →
      t • x ∈ T_set.carrier) :
    AsymptoticStatistics.Core.NondominatedTangent.tangentSpace
        (commonDominatorCone T_set h0 hcone) =
      tangentSpace T_set := by
  rfl

private noncomputable def commonDominatorPathwise
    (T_set : TangentSpec P)
    (h0 : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (hcone : ∀ x ∈ T_set.carrier, ∀ t : ℝ, 0 ≤ t →
      t • x ∈ T_set.carrier)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ) :
    NondominatedPathwiseDifferentiableAtVec P
      (commonDominatorCone T_set h0 hcone) ψ where
  derivative := by
    change tangentSpace T_set →L[ℝ] EuclideanSpace ℝ (Fin d)
    exact hpd.derivative
  derivative_spec := by
    intro g
    have hgcarrier : (g : ↥(L2ZeroMean P)) ∈ T_set.carrier := by
      simpa only [commonDominatorCone] using g.property
    have hg : (g : ↥(L2ZeroMean P)) ∈ tangentSpace T_set :=
      span_carrier_le_tangentSpace T_set (Submodule.subset_span hgcarrier)
    have hgscore :
        (AsymptoticStatistics.LowerBounds.RegularEstimator.canonicalPath
          (g : ↥(L2ZeroMean P))).score ∈ tangentSpace T_set := by
      simpa only [
        AsymptoticStatistics.LowerBounds.RegularEstimator.canonicalPath_score]
        using hg
    have hfilter : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ 𝓝[≠] (0 : ℝ) := by
      apply nhdsWithin_mono
      intro t ht
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht.ne'
    have h := (hpd.derivative_spec
      (AsymptoticStatistics.LowerBounds.RegularEstimator.canonicalPath
        (g : ↥(L2ZeroMean P))) hgscore).mono_left hfilter
    simpa only [commonDominatorCone,
      AsymptoticStatistics.Core.NondominatedQMDPath.QMDPath.toNondominatedQMDPath,
      AsymptoticStatistics.LowerBounds.RegularEstimator.canonicalPath_score] using! h

private theorem selectedPathCanonicalLHSVec_le_commonDominator
    (T_set : TangentSpec P)
    (h0 : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (hcone : ∀ x ∈ T_set.carrier, ∀ t : ℝ, 0 ≤ t →
      t • x ∈ T_set.carrier)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin d))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    selectedPathCanonicalLHSVec (commonDominatorCone T_set h0 hcone) T_n ψ ℓ ≤
      LHS_canonical_vec T_set T_n ψ ℓ := by
  classical
  unfold selectedPathCanonicalLHSVec LHS_canonical_vec
  refine iSup_le fun I => ?_
  let e : {g : ↥(L2ZeroMean P) //
      g ∈ (commonDominatorCone T_set h0 hcone).carrier} ↪
        ↥(L2ZeroMean P) := ⟨Subtype.val, Subtype.val_injective⟩
  let S : Finset ↥(L2ZeroMean P) := I.map e
  have hS : (S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier := by
    intro g hg
    change g ∈ I.map e at hg
    rw [Finset.mem_map] at hg
    obtain ⟨g', _hg', rfl⟩ := hg
    simpa only [commonDominatorCone] using! g'.property
  refine le_iSup_of_le (⟨S, hS⟩ :
    {S : Finset ↥(L2ZeroMean P) // (S : Set _) ⊆ T_set.carrier}) ?_
  apply le_of_eq
  congr 1
  funext n
  rw [show (⟨S, hS⟩ :
    {S : Finset ↥(L2ZeroMean P) // (S : Set _) ⊆ T_set.carrier}).val = S from rfl,
    show S = I.map e from rfl, Finset.sup_map]
  rfl

private theorem semiparametricCone_minimax_compatibility
    (T_set : TangentSpec P)
    (h0 : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (hcone : ∀ x ∈ T_set.carrier, ∀ t : ℝ, 0 ≤ t →
      t • x ∈ T_set.carrier)
    (hconv : Convex ℝ T_set.carrier)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    {φ : Fin d → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec hpd.derivative φ)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (hT : ∀ n, Measurable (T_n n))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hbowl : BowlShaped ℓ) (hlsc : LowerSemicontinuous ℓ) :
    LHS_canonical_vec T_set T_n ψ ℓ ≥
      ∫⁻ y, ℓ y ∂(multivariateGaussian 0 (Matrix.gram ℝ φ)) := by
  let C := commonDominatorCone T_set h0 hcone
  let hpdC := commonDominatorPathwise T_set h0 hcone hpd
  have hconvC : Convex ℝ C.carrier := by
    simpa only [C, commonDominatorCone] using hconv
  have hEIFC : IsEfficientInfluenceFunction_vec hpdC.derivative φ := by
    simpa only [hpdC, commonDominatorPathwise,
      commonDominatorCone_tangentSpace_eq] using! hEIF
  have hnd := nondominated_minimax_core
    C hconvC hpdC hEIFC T_n hT ℓ hbowl hlsc
  exact hnd.trans (selectedPathCanonicalLHSVec_le_commonDominator
    T_set h0 hcone T_n ψ ℓ)

/-- Common-dominator form of the semiparametric local asymptotic minimax bound,
formulated with `TangentSpec`. The nondominated form is
`semiparametric_local_asymptotic_minimax_nondominated`. -/
theorem semiparametricCone_minimax_of_tight
    (T_set : TangentSpec P)
    (_h0 : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (_hcone : ∀ x ∈ T_set.carrier, ∀ t : ℝ, 0 ≤ t → t • x ∈ T_set.carrier)
    (_hconv : Convex ℝ T_set.carrier)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    {φ : Fin d → ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction_vec hpd.derivative φ)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (_hT : ∀ n, Measurable (T_n n))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (_hbowl : BowlShaped ℓ) (_hlsc : LowerSemicontinuous ℓ) :
    LHS_canonical_vec T_set T_n ψ ℓ ≥
      ∫⁻ y, ℓ y ∂(multivariateGaussian 0 (Matrix.gram ℝ φ)) := by
  exact semiparametricCone_minimax_compatibility T_set _h0 _hcone _hconv hpd
    _hEIF T_n _hT ℓ _hbowl _hlsc

/-- Common-dominator cone theorem using `TangentSpec` and `canonicalPath`.
The nondominated theorem instead uses paths independently selected by the cone. -/
theorem semiparametric_local_asymptotic_minimax_cone
    (T_set : TangentSpec P)
    (_h0 : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (_hcone : ∀ x ∈ T_set.carrier, ∀ t : ℝ, 0 ≤ t → t • x ∈ T_set.carrier)
    (_hconv : Convex ℝ T_set.carrier)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    {φ : Fin d → ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction_vec hpd.derivative φ)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (_hT : ∀ n, Measurable (T_n n))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (_hbowl : BowlShaped ℓ) (_hlsc : LowerSemicontinuous ℓ) :
    LHS_canonical_vec T_set T_n ψ ℓ ≥
      ∫⁻ y, ℓ y ∂(multivariateGaussian 0 (Matrix.gram ℝ φ)) := by
  exact semiparametricCone_minimax_compatibility T_set _h0 _hcone _hconv hpd
    _hEIF T_n _hT ℓ _hbowl _hlsc

/-- **vdV Theorem 25.21, full nondominated vector form.**

The tangent object supplies zero and nonnegative scaling structurally; the
only extra cone datum is convexity.  The conclusion uses the selected path of
each carrier-subtype score and the raw Gram covariance.  It includes singular
Gram matrices, `d = 0`, and `φ = 0`, and has no common dominating measure,
negation, tightness, or positive-definiteness hypothesis.

Proof idea: `finiteCarrierChart_exhausts_eifGram` bounds the raw Gram
benchmark by the supremum of finite Gaussian carrier experiments;
`gaussianConeKernelRisk_le_selectedPathCanonicalLHSVec` transfers those risks
to the selected nondominated paths by finite loss-profile compactification. -/
theorem semiparametric_local_asymptotic_minimax_nondominated
    (C : NondominatedTangentCone P)
    -- USER-INPUT: convex tangent cone; vdV Theorem 25.21.
    (hconv : Convex ℝ C.carrier)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    -- USER-INPUT: pathwise differentiability and an efficient influence function;
    -- vdV Theorem 25.21.
    (hpd : NondominatedPathwiseDifferentiableAtVec P C ψ)
    {φ : Fin d → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec hpd.derivative φ)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    -- LEAN-ONLY: measurability of each estimator.
    (hT : ∀ n, Measurable (T_n n))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    -- USER-INPUT: bowl-shaped lower-semicontinuous loss; vdV Theorem 25.21.
    (hbowl : BowlShaped ℓ) (hlsc : LowerSemicontinuous ℓ) :
    selectedPathCanonicalLHSVec C T_n ψ ℓ ≥
      ∫⁻ y, ℓ y ∂(multivariateGaussian 0 (Matrix.gram ℝ φ)) := by
  exact (finiteCarrierChart_exhausts_eifGram C hconv hpd hEIF ℓ hbowl hlsc).trans
    (gaussianConeKernelRisk_le_selectedPathCanonicalLHSVec
      C hconv hpd T_n hT ℓ hbowl hlsc)

end AsymptoticStatistics.LowerBounds.LAMSemiparametricCone
