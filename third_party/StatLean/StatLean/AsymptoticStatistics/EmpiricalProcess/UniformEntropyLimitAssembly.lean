module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformEntropyBracketingTransfer
public import StatLean.AsymptoticStatistics.EmpiricalProcess.GlivenkoCantelli
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformEntropyGaussianBridge
public import StatLean.AsymptoticStatistics.EmpiricalProcess.VCUniformEntropyAssembly

@[expose] public section

/-!
# Uniform entropy limit theorems

Van der Vaart Theorems 19.13 and 19.14 from the finite bracketing transfer and
the full Gaussian-process bridge result.

Reference: van der Vaart, *Asymptotic Statistics*, §19.2, p.274.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open UniformEntropyStructural

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 19.13 (uniform covering Glivenko–Cantelli theorem).**

A suitably measurable class with finite uniform relative `L¹` covering
numbers and finite outer first envelope moment is `P`-Glivenko–Cantelli. -/
theorem uniformCovering_isPGlivenkoCantelli
    {F : Set (Ω → ℝ)} {G : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hF_meas : ∀ f ∈ F, Measurable f) (hPM : IsPointwiseMeasurable F)
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hG1 : outerLpNorm P G 1 < ⊤)
    (hcov : ∀ ε : ℝ, 0 < ε → uniformLpCoveringNumber F G 1 ε < ⊤) :
    IsPGlivenkoCantelli F P := by
  obtain ⟨_, H, _, _, _, _, hHenv, hHint, _⟩ :=
    exists_localizingMajorants F G P hF_meas hPM hEnv hG1
  have hF_int : ∀ f ∈ F, Integrable f P := by
    intro f hf
    refine hHint.mono (hF_meas f hf).aestronglyMeasurable ?_
    filter_upwards [] with x
    change |f x| ≤ |H x|
    exact (hHenv.2 f hf x).trans_eq (abs_of_nonneg (hHenv.1 x)).symm
  have hbracket : ∀ ε > 0, HasFiniteBracketingCover F ε 1 P :=
    uniformCovering_finiteBracketing_L1 F G P hF_meas hPM hEnv hG1 hcov
  intro Ξ _ μ _ X hX_meas hX_indep hX_idem hX_law
  exact isPGlivenkoCantelli_of_finite_bracketing_L1 F P hF_int hbracket
    hX_meas hX_indep hX_idem hX_law

/-- **Theorem 19.14 (uniform entropy Donsker theorem).**

A suitably measurable class with finite uniform `L²` entropy integral and
finite outer second envelope moment carries the complete operational and
literal `P`-Donsker process data. -/
theorem uniformEntropy_pdonskerProcessData
    {F : Set (Ω → ℝ)} {G : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hF_meas : ∀ f ∈ F, Measurable f) (hPM : IsPointwiseMeasurable F)
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hG2 : outerLpNorm P G 2 < ⊤)
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤) :
    PDonskerProcessData F P := by
  exact uniformEntropy_pdonskerProcessData_core F G P hF_meas hPM hEnv hG2 hJ

/-- A pointwise-measurable VC-subgraph class with an integrable envelope is
`P`-Glivenko--Cantelli. -/
theorem vcSubgraph_isPGlivenkoCantelli
    {F : Set (Ω → ℝ)} {G : Ω → ℝ} {P : Measure Ω} {V : ℕ}
    [IsProbabilityMeasure P]
    (hVC : IsVCSubgraphClass F V) (hPM : IsPointwiseMeasurable F)
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hG1 : outerLpNorm P G 1 < ⊤) :
    IsPGlivenkoCantelli F P := by
  refine uniformCovering_isPGlivenkoCantelli hVC.1 hPM hEnv hG1 ?_
  intro ε hε
  obtain ⟨_, _, hcover⟩ := vcSubgraph_uniformLpCoveringNumber_le
  by_cases hε₁ : ε < 1
  · obtain ⟨N, hN, _⟩ :=
      hcover Ω ‹MeasurableSpace Ω› F G V 1 ε hVC hEnv (by norm_num) hε hε₁
    exact lt_of_le_of_lt hN (ENat.coe_lt_top N)
  · obtain ⟨N, hN, _⟩ :=
      hcover Ω ‹MeasurableSpace Ω› F G V 1 (1 / 2) hVC hEnv
        (by norm_num) (by norm_num) (by norm_num)
    refine lt_of_le_of_lt
      ((uniformLpCoveringNumber_antitone_eps (by linarith)).trans hN) ?_
    exact ENat.coe_lt_top N

/-- A pointwise-measurable VC-subgraph class with square-integrable envelope
carries the complete `P`-Donsker process data. -/
theorem vcSubgraph_pdonskerProcessData
    {F : Set (Ω → ℝ)} {G : Ω → ℝ} {P : Measure Ω} {V : ℕ}
    [IsProbabilityMeasure P]
    (hVC : IsVCSubgraphClass F V) (hPM : IsPointwiseMeasurable F)
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hG2 : outerLpNorm P G 2 < ⊤) :
    PDonskerProcessData F P := by
  exact uniformEntropy_pdonskerProcessData hVC.1 hPM hEnv hG2
    (vcSubgraph_uniformEntropyIntegral_lt_top hVC hEnv)

end AsymptoticStatistics.EmpiricalProcess
