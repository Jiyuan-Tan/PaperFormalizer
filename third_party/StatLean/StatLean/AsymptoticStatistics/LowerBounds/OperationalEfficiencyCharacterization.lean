module
public import StatLean.AsymptoticStatistics.LowerBounds.OperationalEfficiencyCharacterizationNondominated

@[expose] public section

/-!
# Raw regularity characterizes operational efficiency

Formalization of van der Vaart Lemma 25.23.  The premise/conclusion
never uses `SemiparametricallyEfficientAt`; the theorem identifies the raw
regular-plus-efficient-Gaussian-limit condition directly with asymptotic
linearity by the EIF.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace AsymptoticStatistics.LowerBounds.OperationalEfficiencyCharacterization

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.Core.NondominatedTangent
open AsymptoticStatistics.Core.NondominatedPathwise
open AsymptoticStatistics.Core.NondominatedEfficiencyOperational
open AsymptoticStatistics.LowerBounds.OperationalEfficiencyCharacterizationNondominated

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Real-scalar saturation of path scores

A family of two-sided paths permits every real local parameter, although its
set of scores need not itself be a cone.  Saturating the scores under real
scalar multiplication is realized by reparameterizing each path by
`t ↦ a * t`, and does not change their closed linear span. -/

private noncomputable def scaledQMDPath
    (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P) (a : ℝ) :
    AsymptoticStatistics.Core.QMDPath.QMDPath P where
  curve t := γ.curve (a * t)
  curve_at_zero := by simp [γ.curve_at_zero]
  curve_isProbability t := γ.curve_isProbability (a * t)
  dominating := γ.dominating
  curve_absContinuous t := γ.curve_absContinuous (a * t)
  dominating_sigmaFinite := γ.dominating_sigmaFinite
  score := a • γ.score
  qmd_limit := by
    by_cases ha : a = 0
    · subst a
      simp
    · have hmap : Tendsto (fun t : ℝ => a * t) (𝓝[≠] 0) (𝓝[≠] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · simpa using!
            (((continuous_const : Continuous (fun _ : ℝ => a)).mul continuous_id).tendsto 0
              |>.mono_left inf_le_left)
        · filter_upwards [self_mem_nhdsWithin] with t ht
          exact mul_ne_zero ha ht
      have hcomp := γ.qmd_limit.comp hmap
      have hmul0 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |a|) hcomp
        (Or.inr ENNReal.ofReal_ne_top)
      have hmul :
          Tendsto
            (fun t : ℝ => ENNReal.ofReal |a| *
              (eLpNorm (fun ω : Ω =>
                Real.sqrt ((γ.curve (a * t)).rnDeriv γ.dominating ω).toReal
                  - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
                  - ((a * t) / 2) * (γ.score : Ω → ℝ) ω *
                    Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
                2 γ.dominating / ENNReal.ofReal |a * t|))
            (𝓝[≠] 0) (𝓝 0) := by
        simpa only [Function.comp_apply, mul_zero] using hmul0
      apply hmul.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ha_ofReal : ENNReal.ofReal |a| ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr ha)
      have ha_top : ENNReal.ofReal |a| ≠ ⊤ := ENNReal.ofReal_ne_top
      have hPdom : P ≪ γ.dominating := by
        simpa [γ.curve_at_zero] using γ.curve_absContinuous 0
      have hscoreP :
          (fun ω : Ω => (((a • γ.score : ↥(L2ZeroMean P)) : Ω → ℝ) ω)) =ᵐ[P]
            fun ω => a * (γ.score : Ω → ℝ) ω := by
        simpa only [Pi.smul_apply, smul_eq_mul] using!
          (Lp.coeFn_smul a (γ.score : Lp ℝ 2 P))
      have hscoreDensity : ∀ᵐ ω ∂γ.dominating,
          P.rnDeriv γ.dominating ω ≠ 0 →
            (((a • γ.score : ↥(L2ZeroMean P)) : Ω → ℝ) ω) =
              a * (γ.score : Ω → ℝ) ω := by
        apply (ae_withDensity_iff (Measure.measurable_rnDeriv P γ.dominating)).1
        rw [Measure.withDensity_rnDeriv_eq P γ.dominating hPdom]
        exact hscoreP
      have hres :
          eLpNorm (fun ω : Ω =>
            Real.sqrt ((γ.curve (a * t)).rnDeriv γ.dominating ω).toReal
              - Real.sqrt ((γ.curve (a * 0)).rnDeriv γ.dominating ω).toReal
              - (t / 2) * (((a • γ.score : ↥(L2ZeroMean P)) : Ω → ℝ) ω) *
                Real.sqrt ((γ.curve (a * 0)).rnDeriv γ.dominating ω).toReal)
            2 γ.dominating =
          eLpNorm (fun ω : Ω =>
            Real.sqrt ((γ.curve (a * t)).rnDeriv γ.dominating ω).toReal
              - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
              - ((a * t) / 2) * (γ.score : Ω → ℝ) ω *
                Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
            2 γ.dominating := by
        apply eLpNorm_congr_ae
        filter_upwards [hscoreDensity] with ω hscore
        simp only [mul_zero]
        by_cases hd : P.rnDeriv γ.dominating ω = 0
        · simp [γ.curve_at_zero, hd]
        · rw [hscore hd]
          ring
      rw [hres, abs_mul, ENNReal.ofReal_mul (abs_nonneg a)]
      rw [← mul_div_assoc]
      exact ENNReal.mul_div_mul_left _ _ ha_ofReal ha_top

private def scalarSaturation (T : TangentSpec P) : Set ↥(L2ZeroMean P) :=
  {h | ∃ ag : ℝ × {g : ↥(L2ZeroMean P) // g ∈ T.carrier},
    h = ag.1 • (ag.2 : ↥(L2ZeroMean P))}

private noncomputable def saturationWitness (T : TangentSpec P)
    (h : {h : ↥(L2ZeroMean P) // h ∈ scalarSaturation T}) :
    ℝ × {g : ↥(L2ZeroMean P) // g ∈ T.carrier} :=
  Classical.choose h.property

private theorem saturationWitness_spec (T : TangentSpec P)
    (h : {h : ↥(L2ZeroMean P) // h ∈ scalarSaturation T}) :
    (h : ↥(L2ZeroMean P)) =
      (saturationWitness T h).1 •
        ((saturationWitness T h).2 : ↥(L2ZeroMean P)) :=
  Classical.choose_spec h.property

private noncomputable def saturationChoice
    (T : TangentSpec P) (paths : SelectedQMDPaths P T)
    (h : {h : ↥(L2ZeroMean P) // h ∈ scalarSaturation T}) :
    AsymptoticStatistics.Core.QMDPath.QMDPath P :=
  scaledQMDPath (paths.path (saturationWitness T h).2)
    (saturationWitness T h).1

private theorem saturationChoice_score
    (T : TangentSpec P) (paths : SelectedQMDPaths P T)
    (h : {h : ↥(L2ZeroMean P) // h ∈ scalarSaturation T}) :
    (saturationChoice T paths h).score = (h : ↥(L2ZeroMean P)) := by
  change (saturationWitness T h).1 •
      (paths.path (saturationWitness T h).2).score = h
  rw [paths.score_eq]
  exact (saturationWitness_spec T h).symm

private noncomputable def saturatedConeOfChoice
    (T : TangentSpec P)
    (hzero : (0 : ↥(L2ZeroMean P)) ∈ T.carrier)
    (choice : {h : ↥(L2ZeroMean P) // h ∈ scalarSaturation T} →
      AsymptoticStatistics.Core.QMDPath.QMDPath P)
    (hchoice : ∀ h, (choice h).score = (h : ↥(L2ZeroMean P))) :
    NondominatedTangentCone P where
  carrier := scalarSaturation T
  carrier_nonempty := by
    exact ⟨0, ⟨(0, ⟨0, hzero⟩), by simp⟩⟩
  nonneg_smul_mem := by
    rintro b _ h ⟨⟨a, g⟩, rfl⟩
    exact ⟨(b * a, g), by simp only [smul_smul]⟩
  selectedPath h :=
    AsymptoticStatistics.Core.NondominatedQMDPath.QMDPath.toNondominatedQMDPath
      (choice h)
  selectedPath_score h := hchoice h

private noncomputable def saturatedCone
    (T : TangentSpec P) (paths : SelectedQMDPaths P T) :
    NondominatedTangentCone P :=
  saturatedConeOfChoice T paths.zero_mem (saturationChoice T paths)
    (saturationChoice_score T paths)

private theorem saturatedConeOfChoice_tangentSpace_eq
    (T : TangentSpec P) (hzero : (0 : ↥(L2ZeroMean P)) ∈ T.carrier)
    (choice : {h : ↥(L2ZeroMean P) // h ∈ scalarSaturation T} →
      AsymptoticStatistics.Core.QMDPath.QMDPath P)
    (hchoice : ∀ h, (choice h).score = (h : ↥(L2ZeroMean P))) :
    AsymptoticStatistics.Core.NondominatedTangent.tangentSpace
        (saturatedConeOfChoice T hzero choice hchoice) =
      AsymptoticStatistics.Core.TangentAbstract.tangentSpace T := by
  change (Submodule.span ℝ (scalarSaturation T)).topologicalClosure =
    (Submodule.span ℝ T.carrier).topologicalClosure
  apply congrArg Submodule.topologicalClosure
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro h ⟨⟨a, g⟩, rfl⟩
    exact Submodule.smul_mem _ a (Submodule.subset_span g.property)
  · apply Submodule.span_mono
    intro g hg
    exact ⟨(1, ⟨g, hg⟩), by simp⟩

private noncomputable def saturatedTangentEquivOfChoice
    (T : TangentSpec P) (hzero : (0 : ↥(L2ZeroMean P)) ∈ T.carrier)
    (choice : {h : ↥(L2ZeroMean P) // h ∈ scalarSaturation T} →
      AsymptoticStatistics.Core.QMDPath.QMDPath P)
    (hchoice : ∀ h, (choice h).score = (h : ↥(L2ZeroMean P))) :
    AsymptoticStatistics.Core.NondominatedTangent.tangentSpace
        (saturatedConeOfChoice T hzero choice hchoice) ≃L[ℝ]
      AsymptoticStatistics.Core.TangentAbstract.tangentSpace T :=
  ContinuousLinearEquiv.ofEq _ _
    (saturatedConeOfChoice_tangentSpace_eq T hzero choice hchoice)

private noncomputable def nondominatedPathwiseOfChoice
    (T : TangentSpec P) (hzero : (0 : ↥(L2ZeroMean P)) ∈ T.carrier)
    (choice : {h : ↥(L2ZeroMean P) // h ∈ scalarSaturation T} →
      AsymptoticStatistics.Core.QMDPath.QMDPath P)
    (hchoice : ∀ h, (choice h).score = (h : ↥(L2ZeroMean P)))
    {ψ : Measure Ω → ℝ}
    (hpd : PathwiseDifferentiableAt P
      (AsymptoticStatistics.Core.TangentAbstract.tangentSpace T) ψ) :
    NondominatedPathwiseDifferentiableAt P
      (saturatedConeOfChoice T hzero choice hchoice) ψ where
  derivative := hpd.derivative.comp
    (saturatedTangentEquivOfChoice T hzero choice hchoice).toContinuousLinearMap
  derivative_spec h := by
    have hmem : (choice h).score ∈
        AsymptoticStatistics.Core.TangentAbstract.tangentSpace T := by
      rw [hchoice h, ← saturatedConeOfChoice_tangentSpace_eq T hzero choice hchoice]
      exact selected_mem_tangentSpace
        (saturatedConeOfChoice T hzero choice hchoice) h
    have hlegacy := hpd.derivative_spec (choice h) hmem
    have hfilter : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ 𝓝[≠] (0 : ℝ) := by
      apply nhdsWithin_mono
      intro t ht
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht.ne'
    have hright := hlegacy.mono_left hfilter
    have hequiv :
        saturatedTangentEquivOfChoice T hzero choice hchoice
            ⟨h, selected_mem_tangentSpace
              (saturatedConeOfChoice T hzero choice hchoice) h⟩ =
          ⟨(choice h).score, hmem⟩ := by
      apply Subtype.ext
      exact (hchoice h).symm
    change Tendsto (fun t : ℝ => (ψ ((choice h).curve t) - ψ P) / t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (hpd.derivative
        (saturatedTangentEquivOfChoice T hzero choice hchoice
          ⟨h, selected_mem_tangentSpace
            (saturatedConeOfChoice T hzero choice hchoice) h⟩)))
    rw [hequiv]
    exact hright

private theorem eifOfSaturatedChoice
    (T : TangentSpec P) (hzero : (0 : ↥(L2ZeroMean P)) ∈ T.carrier)
    (choice : {h : ↥(L2ZeroMean P) // h ∈ scalarSaturation T} →
      AsymptoticStatistics.Core.QMDPath.QMDPath P)
    (hchoice : ∀ h, (choice h).score = (h : ↥(L2ZeroMean P)))
    {ψ : Measure Ω → ℝ}
    (hpd : PathwiseDifferentiableAt P
      (AsymptoticStatistics.Core.TangentAbstract.tangentSpace T) ψ)
    {φ : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P
      (AsymptoticStatistics.Core.TangentAbstract.tangentSpace T)
      hpd.derivative φ) :
    IsEfficientInfluenceFunction P
      (AsymptoticStatistics.Core.NondominatedTangent.tangentSpace
        (saturatedConeOfChoice T hzero choice hchoice))
      (nondominatedPathwiseOfChoice T hzero choice hchoice hpd).derivative φ := by
  constructor
  · intro g
    have h := hEIF.1 (saturatedTangentEquivOfChoice T hzero choice hchoice g)
    simpa [nondominatedPathwiseOfChoice, saturatedTangentEquivOfChoice,
      ContinuousLinearEquiv.ofEq] using h
  · rw [saturatedConeOfChoice_tangentSpace_eq T hzero choice hchoice]
    exact hEIF.2

private noncomputable def targetedChoice
    (T : TangentSpec P) (paths : SelectedQMDPaths P T)
    (g₀ : {g : ↥(L2ZeroMean P) // g ∈ T.carrier}) (a₀ : ℝ)
    (h : {h : ↥(L2ZeroMean P) // h ∈ scalarSaturation T}) :
    AsymptoticStatistics.Core.QMDPath.QMDPath P := by
  classical
  exact if (h : ↥(L2ZeroMean P)) = a₀ • (g₀ : ↥(L2ZeroMean P)) then
      scaledQMDPath (paths.path g₀) a₀
    else saturationChoice T paths h

private theorem targetedChoice_score
    (T : TangentSpec P) (paths : SelectedQMDPaths P T)
    (g₀ : {g : ↥(L2ZeroMean P) // g ∈ T.carrier}) (a₀ : ℝ)
    (h : {h : ↥(L2ZeroMean P) // h ∈ scalarSaturation T}) :
    (targetedChoice T paths g₀ a₀ h).score = (h : ↥(L2ZeroMean P)) := by
  unfold targetedChoice
  split_ifs with heq
  · change a₀ • (paths.path g₀).score = h
    rw [paths.score_eq, ← heq]
  · exact saturationChoice_score T paths h

private theorem isRegularAtND_saturated_of_isRegularAt
    {T_n : ∀ n, (Fin n → Ω) → ℝ} {ψ : Measure Ω → ℝ}
    (T : TangentSpec P) (paths : SelectedQMDPaths P T) (L : Measure ℝ)
    (hreg : IsRegularAt paths T_n ψ L) :
    IsRegularAtND (saturatedCone T paths) T_n ψ L := by
  intro h
  have hold := hreg (saturationWitness T h).2 (saturationWitness T h).1
  simpa only [saturatedCone, saturatedConeOfChoice, saturationChoice,
    AsymptoticStatistics.Core.NondominatedQMDPath.QMDPath.toNondominatedQMDPath,
    scaledQMDPath] using hold

/-- Selected-family regularity implies the baseline weak limit by specializing
the selected zero-score path at scalar local parameter zero.

Proof idea: specialize regularity to `g = ⟨0, paths.zero_mem⟩` and `a = 0`,
then rewrite the selected path's curve at zero with `QMDPath.curve_at_zero`. -/
theorem hasLimitDistributionAt_of_isRegularAt
    {T_n : ∀ n, (Fin n → Ω) → ℝ} {ψ : Measure Ω → ℝ}
    {T_set : TangentSpec P}
    (paths : SelectedQMDPaths P T_set) (L : Measure ℝ)
    (hreg : IsRegularAt paths T_n ψ L) :
    HasLimitDistributionAt T_n P (ψ P) L := by
  let z : {g : ↥(L2ZeroMean P) // g ∈ T_set.carrier} :=
    ⟨0, paths.zero_mem⟩
  simpa only [IsRegularAt, zero_mul, (paths.path z).curve_at_zero] using! hreg z 0

/-- The forward implication: an asymptotically linear estimator with EIF is
raw-regular with the efficient Gaussian limit and has that baseline limit.

Proof idea: for every selected path and scalar `a`, use the iid CLT for the
EIF empirical average, LAN/Le Cam shift along the `a / √n` tilt, and Slutsky
for the vanishing residual. -/
theorem regular_and_gaussian_of_asymptoticallyLinear
    {T_n : ∀ n, (Fin n → Ω) → ℝ}
    {ψ : Measure Ω → ℝ}
    {T_set : TangentSpec P}
    (paths : SelectedQMDPaths P T_set)
    (hpd : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {φ : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set) hpd.derivative φ)
    (_hT_meas : ∀ n, Measurable (T_n n))
    (hAL : AsymptoticallyLinearAt T_n P φ (ψ P)) :
    IsRegularAt paths T_n ψ
      (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) := by
  intro g a
  let choice := targetedChoice T_set paths g a
  have hchoice : ∀ h, (choice h).score = (h : ↥(L2ZeroMean P)) :=
    targetedChoice_score T_set paths g a
  let C := saturatedConeOfChoice T_set paths.zero_mem choice hchoice
  let hpdND := nondominatedPathwiseOfChoice T_set paths.zero_mem
    choice hchoice hpd
  have hEIFND : IsEfficientInfluenceFunction P
      (AsymptoticStatistics.Core.NondominatedTangent.tangentSpace C)
      hpdND.derivative φ := by
    exact eifOfSaturatedChoice T_set paths.zero_mem choice hchoice hpd hEIF
  have hregND := regular_and_gaussian_of_asymptoticallyLinearND
    C hpdND hEIFND _hT_meas hAL
  let ag : {h : ↥(L2ZeroMean P) // h ∈ C.carrier} :=
    ⟨a • (g : ↥(L2ZeroMean P)), ⟨(a, g), rfl⟩⟩
  have h := hregND ag
  simpa only [C, saturatedConeOfChoice, ag, choice, targetedChoice, ↓reduceDIte, ↓reduceIte,
    AsymptoticStatistics.Core.NondominatedQMDPath.QMDPath.toNondominatedQMDPath,
    scaledQMDPath] using h

/-- The converse implication: raw regularity together with the baseline
efficient Gaussian law forces the asymptotic-linear EIF expansion.

Proof idea: use regularity simultaneously over every scalar `a` on each
selected path in the convolution/characteristic-function equality case,
applied jointly with the EIF empirical average; zero residual law implies
convergence in probability to zero. -/
theorem asymptoticallyLinear_of_regular_and_gaussian
    {T_n : ∀ n, (Fin n → Ω) → ℝ}
    {ψ : Measure Ω → ℝ}
    {T_set : TangentSpec P}
    (paths : SelectedQMDPaths P T_set)
    (hpd : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {φ : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set) hpd.derivative φ)
    (_hT_meas : ∀ n, Measurable (T_n n))
    (hraw : IsRegularAt paths T_n ψ
      (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩)) :
    AsymptoticallyLinearAt T_n P φ (ψ P) := by
  let choice := saturationChoice T_set paths
  have hchoice : ∀ h, (choice h).score = (h : ↥(L2ZeroMean P)) :=
    saturationChoice_score T_set paths
  let C := saturatedConeOfChoice T_set paths.zero_mem choice hchoice
  let hpdND := nondominatedPathwiseOfChoice T_set paths.zero_mem
    choice hchoice hpd
  have hEIFND : IsEfficientInfluenceFunction P
      (AsymptoticStatistics.Core.NondominatedTangent.tangentSpace C)
      hpdND.derivative φ := by
    exact eifOfSaturatedChoice T_set paths.zero_mem choice hchoice hpd hEIF
  have hregND : IsRegularAtND C T_n ψ
      (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) := by
    simpa only [C, choice, saturatedCone] using
      isRegularAtND_saturated_of_isRegularAt T_set paths
        (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩) hraw
  exact asymptoticallyLinear_of_regular_and_gaussianND
    C hpdND hEIFND _hT_meas hregND

/-- vdV Lemma 25.23, literal operational characterization.

The assumptions are exactly pathwise differentiability, an EIF, and
estimator measurability.  Raw regularity and the baseline efficient Gaussian
law occur on the left of the equivalence, not as hidden fields of any
efficiency predicate.  The statement includes `φ=0` without a positivity
side condition. -/
theorem operational_efficiency_characterization
    {T_n : ∀ n, (Fin n → Ω) → ℝ}
    {ψ : Measure Ω → ℝ}
    {T_set : TangentSpec P}
    (paths : SelectedQMDPaths P T_set)
    (hpd : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {φ : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set) hpd.derivative φ)
    (hT_meas : ∀ n, Measurable (T_n n)) :
    IsRegularAt paths T_n ψ
        (gaussianReal 0 ⟨‖φ‖ ^ 2, sq_nonneg _⟩)
      ↔ AsymptoticallyLinearAt T_n P φ (ψ P) := by
  constructor
  · exact asymptoticallyLinear_of_regular_and_gaussian
      paths hpd hEIF hT_meas
  · exact regular_and_gaussian_of_asymptoticallyLinear
      paths hpd hEIF hT_meas

end AsymptoticStatistics.LowerBounds.OperationalEfficiencyCharacterization
