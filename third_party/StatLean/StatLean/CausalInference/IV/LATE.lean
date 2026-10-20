module
public import StatLean.CausalInference.IV.ComplianceTypes
public import StatLean.CausalInference.ForMathlib.CondAlgebra

@[expose] public section

/-!
# The LATE / CACE theorem — the Wald ratio identifies the complier average effect

The flagship instrumental-variables result. Under random assignment, monotonicity and the
exclusion restriction, the two intention-to-treat contrasts decompose as

$$\tau_D=\Pr(\text{complier}),\qquad
  \tau_Y=\Pr(\text{complier})\cdot\mathbb E[Y(1)-Y(0)\mid\text{complier}],$$

so that whenever the instrument is relevant (`τ_D ≠ 0`) the **Wald ratio** identifies the
complier average causal effect:

$$\frac{\mathbb E[Y\mid Z=1]-\mathbb E[Y\mid Z=0]}
       {\mathbb E[D\mid Z=1]-\mathbb E[D\mid Z=0]}
 =\mathbb E[Y(1)-Y(0)\mid D(1)>D(0)].$$

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). eq. (21.4) (p. 284: the first stage equals the
complier proportion, under Assumption 21.2); eq. (21.3) (p. 283: the reduced form is the
complier proportion times the complier effect, under Assumptions 21.2–21.3, from the
four-term decomposition eq. (21.1)); **Theorem 21.1** (p. 284: `τ_c = τ_Y/τ_D` when
`τ_D ≠ 0`); **Corollary 21.1** (p. 285: the observable Wald form, under Assumptions
21.1–21.3); Theorem 22.1 (§22.1, p. 302: identification of the type proportions and the
type-specific outcome means). (`Ding eqs. (21.3)–(21.4); Theorem 21.1; Corollary 21.1;
Theorem 22.1`.) The corresponding development is G. W. Imbens and D. B. Rubin, *Causal
Inference for Statistics, Social, and Biomedical Sciences*, Cambridge University Press,
2015, chs. 23–24. (`IR chs. 23–24`.)

**Proof formalization notes.** The decompositions are proved in the order the book uses:
first move from observed arm means to potential-outcome means using random assignment
(`ittContrast_eq_integral_sub`, an application of independence), then split the resulting
expectation over the four compliance-type events, then kill the defier term with
monotonicity and the always/never-taker terms with the exclusion restriction. The ratio
theorem is then division; relevance `τ_D ≠ 0` is a genuine hypothesis and is exactly what
fails for a weak instrument.

**Bibliographic comments.** G. W. Imbens and J. D. Angrist, "Identification and estimation
of local average treatment effects," *Econometrica* **62** (1994), 467–475;
J. D. Angrist, G. W. Imbens and D. B. Rubin, "Identification of causal effects using
instrumental variables," *J. Amer. Statist. Assoc.* **91** (1996), 444–455 (with the
discussion in which the "LATE" and "CACE" names are debated).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z d1 d0 : Ω → Bool}
  {y1 y0 : Ω → ℝ}

/-! ### Auxiliary bookkeeping

The compliance-type events are the intersections of two level sets of the potential
treatments, which is what makes them measurable and what lets every argument below be run
through the two `Bool`-valued coordinates only. -/

/-- The value of `D(1)` on a given compliance type. -/
private def dOneOf : ComplianceType → Bool
  | .alwaysTaker => true
  | .complier => true
  | .defier => false
  | .neverTaker => false

/-- The value of `D(0)` on a given compliance type. -/
private def dZeroOf : ComplianceType → Bool
  | .alwaysTaker => true
  | .complier => false
  | .defier => true
  | .neverTaker => false

omit [MeasurableSpace Ω] in
/-- A compliance-type event is the intersection of the two potential-treatment level sets
prescribed by the type. -/
private lemma typeSet_eq_inter (d1 d0 : Ω → Bool) (t : ComplianceType) :
    typeSet d1 d0 t = {ω | d1 ω = dOneOf t} ∩ {ω | d0 ω = dZeroOf t} := by
  ext ω
  simp only [typeSet, Set.mem_setOf_eq, Set.mem_inter_iff, ComplianceType.of]
  cases h1 : d1 ω <;> cases h0 : d0 ω <;> cases t <;> simp [dOneOf, dZeroOf]

/-- Compliance-type events are measurable. -/
private lemma measurableSet_typeSet (hd1 : Measurable d1) (hd0 : Measurable d0)
    (t : ComplianceType) : MeasurableSet (typeSet d1 d0 t) := by
  rw [typeSet_eq_inter]
  exact (hd1 (measurableSet_singleton _)).inter (hd0 (measurableSet_singleton _))

/-- Any function of the potential-treatment pair is measurable: `Bool × Bool` is discrete. -/
private lemma measurable_boolComp (φ₀ : Bool × Bool → ℝ) (hd1 : Measurable d1)
    (hd0 : Measurable d0) : Measurable fun ω => φ₀ (d1 ω, d0 ω) :=
  (measurable_of_countable φ₀).comp (hd1.prodMk hd0)

/-- A bounded function of the potential-treatment pair is integrable. -/
private lemma integrable_boolComp [IsFiniteMeasure μ] (φ₀ : Bool × Bool → ℝ)
    (hd1 : Measurable d1) (hd0 : Measurable d0) (C : ℝ) (hC : ∀ q, ‖φ₀ q‖ ≤ C) :
    Integrable (fun ω => φ₀ (d1 ω, d0 ω)) μ :=
  Integrable.mono' (integrable_const C)
    (measurable_boolComp φ₀ hd1 hd0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => hC _)

/-- Two integrands agreeing on the conditioning event have the same conditional integral. -/
private lemma integral_cond_congr {s : Set Ω} (hs : MeasurableSet s) {f g : Ω → ℝ}
    (h : Set.EqOn f g s) : ∫ ω, f ω ∂(μ[|s]) = ∫ ω, g ω ∂(μ[|s]) := by
  rw [integral_cond_eq_setIntegral, integral_cond_eq_setIntegral, setIntegral_congr_fun hs h]

/-- Random assignment passes to any function of the potential-treatment pair. -/
private lemma indepFun_boolComp (hrand : IVRandomized μ Z d1 d0 y1 y0) (φ₀ : Bool × Bool → ℝ) :
    IndepFun (fun ω => φ₀ (d1 ω, d0 ω)) Z μ := by
  have := hrand.comp (φ := fun p : (Bool × Bool) × (ℝ × ℝ) => φ₀ p.1) (ψ := id)
    ((measurable_of_countable φ₀).comp measurable_fst) measurable_id
  simpa [Function.comp] using! this

/-- Random assignment passes to `Y(1)`. -/
private lemma indepFun_y1 (hrand : IVRandomized μ Z d1 d0 y1 y0) : IndepFun y1 Z μ := by
  have := hrand.comp (φ := fun p : (Bool × Bool) × (ℝ × ℝ) => p.2.1) (ψ := id)
    (measurable_fst.comp measurable_snd) measurable_id
  simpa [Function.comp] using! this

/-- Random assignment passes to `Y(0)`. -/
private lemma indepFun_y0 (hrand : IVRandomized μ Z d1 d0 y1 y0) : IndepFun y0 Z μ := by
  have := hrand.comp (φ := fun p : (Bool × Bool) × (ℝ × ℝ) => p.2.2) (ψ := id)
    (measurable_snd.comp measurable_snd) measurable_id
  simpa [Function.comp] using! this

/-! ### The decompositions -/

/-- **Random assignment turns an arm contrast into a potential-outcome contrast**
(Ding Assumption 21.1): the intention-to-treat contrast of the observed outcome is the
average difference of the potential outcomes. -/
theorem ittContrast_eq_integral_sub [IsProbabilityMeasure μ]
    -- USER-INPUT: random assignment of the instrument; Ding Assumption 21.1
    (hrand : IVRandomized μ Z d1 d0 y1 y0)
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    -- USER-INPUT: integrable potential outcomes; Ding assumes finite means
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    -- USER-INPUT: both instrument arms have positive probability; Ding §21.2
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    ittContrast μ Z (obs Z y1 y0) = ∫ ω, (y1 ω - y0 ω) ∂μ := by
  have hT : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
  have hF : MeasurableSet {ω | Z ω = false} := hZ (measurableSet_singleton false)
  have h1 : ∫ ω, obs Z y1 y0 ω ∂(μ[|{ω | Z ω = true}]) = ∫ ω, y1 ω ∂μ := by
    rw [integral_cond_congr hT (g := y1) (fun ω hω => by
      simp only [Set.mem_setOf_eq] at hω
      simp [obs, hω])]
    exact integral_cond_arm_eq_of_indepFun (indepFun_y1 hrand) hi1 hy1 hZ hZ1
  have h0 : ∫ ω, obs Z y1 y0 ω ∂(μ[|{ω | Z ω = false}]) = ∫ ω, y0 ω ∂μ := by
    rw [integral_cond_congr hF (g := y0) (fun ω hω => by
      simp only [Set.mem_setOf_eq] at hω
      simp [obs, hω])]
    exact integral_cond_arm_eq_of_indepFun (indepFun_y0 hrand) hi0 hy0 hZ hZ0
  simp only [ittContrast, primaFacie, treatedEvent]
  rw [h1, h0, ← integral_sub hi1 hi0]

/-- The same identity for the observed *treatment*: the first stage is the average
difference of the potential treatments. -/
theorem ittContrast_treat_eq_integral_sub [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 y1 y0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω))
      = ∫ ω, (ind (d1 ω) - ind (d0 ω)) ∂μ := by
  have hT : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
  have hF : MeasurableSet {ω | Z ω = false} := hZ (measurableSet_singleton false)
  have hb : ∀ b : Bool, ‖ind b‖ ≤ 1 := by intro b; cases b <;> simp [ind]
  have hint1 : Integrable (fun ω => ind (d1 ω)) μ :=
    integrable_boolComp (fun q => ind q.1) hd1 hd0 1 (fun q => hb _)
  have hint0 : Integrable (fun ω => ind (d0 ω)) μ :=
    integrable_boolComp (fun q => ind q.2) hd1 hd0 1 (fun q => hb _)
  have hm1 : Measurable fun ω => ind (d1 ω) := measurable_boolComp (fun q => ind q.1) hd1 hd0
  have hm0 : Measurable fun ω => ind (d0 ω) := measurable_boolComp (fun q => ind q.2) hd1 hd0
  have h1 : ∫ ω, ind (obsTreat Z d1 d0 ω) ∂(μ[|{ω | Z ω = true}]) = ∫ ω, ind (d1 ω) ∂μ := by
    rw [integral_cond_congr hT (g := fun ω => ind (d1 ω)) (fun ω hω => by
      simp only [Set.mem_setOf_eq] at hω
      simp [obsTreat, hω])]
    exact integral_cond_arm_eq_of_indepFun (indepFun_boolComp hrand (fun q => ind q.1))
      hint1 hm1 hZ hZ1
  have h0 : ∫ ω, ind (obsTreat Z d1 d0 ω) ∂(μ[|{ω | Z ω = false}]) = ∫ ω, ind (d0 ω) ∂μ := by
    rw [integral_cond_congr hF (g := fun ω => ind (d0 ω)) (fun ω hω => by
      simp only [Set.mem_setOf_eq] at hω
      simp [obsTreat, hω])]
    exact integral_cond_arm_eq_of_indepFun (indepFun_boolComp hrand (fun q => ind q.2))
      hint0 hm0 hZ hZ0
  simp only [ittContrast, primaFacie, treatedEvent]
  rw [h1, h0, ← integral_sub hint1 hint0]

/-- **The first stage is the complier proportion** (Ding eq. (21.4)): under monotonicity,
`E[D | Z = 1] - E[D | Z = 0] = P(complier)`. -/
theorem firstStage_eq_prob_complier [IsProbabilityMeasure μ]
    -- USER-INPUT: random assignment; Ding Assumption 21.1
    (hrand : IVRandomized μ Z d1 d0 y1 y0)
    -- USER-INPUT: monotonicity / no defiers; Ding Assumption 21.2
    (hmono : NoDefiers d1 d0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω))
      = (μ (typeSet d1 d0 ComplianceType.complier)).toReal := by
  rw [ittContrast_treat_eq_integral_sub hrand hZ hd1 hd0 hy1 hy0 hZ1 hZ0]
  have hC : MeasurableSet (typeSet d1 d0 ComplianceType.complier) :=
    measurableSet_typeSet hd1 hd0 _
  have hD : typeSet d1 d0 ComplianceType.defier = ∅ :=
    noDefiers_iff_typeSet_defier_eq_empty.1 hmono
  have hfun : (fun ω => ind (d1 ω) - ind (d0 ω))
      = Set.indicator (typeSet d1 d0 ComplianceType.complier) (fun _ => (1 : ℝ)) := by
    funext ω
    rw [ind_d1_sub_ind_d0 ω, hD]
    simp
  have hone : Set.indicator (typeSet d1 d0 ComplianceType.complier) (fun _ => (1 : ℝ))
      = Set.indicator (typeSet d1 d0 ComplianceType.complier) 1 := rfl
  rw [hfun, hone, integral_indicator_one hC, measureReal_def]

/-- **The reduced form is the complier proportion times the complier effect**
(Ding eq. (21.3)): under monotonicity and the exclusion restriction, the always takers and
never takers contribute nothing to the intention-to-treat effect. -/
theorem reducedForm_eq_prob_complier_mul_cace [IsProbabilityMeasure μ]
    -- USER-INPUT: random assignment; Ding Assumption 21.1
    (hrand : IVRandomized μ Z d1 d0 y1 y0)
    -- USER-INPUT: monotonicity; Ding Assumption 21.2
    (hmono : NoDefiers d1 d0)
    -- USER-INPUT: the exclusion restriction; Ding Assumption 21.3
    (hexcl : ExclusionRestriction d1 d0 y1 y0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    ittContrast μ Z (obs Z y1 y0)
      = (μ (typeSet d1 d0 ComplianceType.complier)).toReal * cace μ d1 d0 y1 y0 := by
  rw [ittContrast_eq_integral_sub hrand hZ hd1 hd0 hy1 hy0 hi1 hi0 hZ1 hZ0]
  have hC : MeasurableSet (typeSet d1 d0 ComplianceType.complier) :=
    measurableSet_typeSet hd1 hd0 _
  have hint : Integrable (fun ω => y1 ω - y0 ω) μ := hi1.sub hi0
  rw [← integral_add_compl hC hint]
  have hzero : ∫ ω in (typeSet d1 d0 ComplianceType.complier)ᶜ, (y1 ω - y0 ω) ∂μ = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun ω hω => ?_
    have hnc : ¬ (d1 ω = true ∧ d0 ω = false) := fun h => hω (mem_typeSet_complier.2 h)
    have key : d1 ω = d0 ω := by
      by_cases h0 : d0 ω = true
      · rw [hmono ω h0, h0]
      · have h0' : d0 ω = false := by simpa using h0
        by_cases h1 : d1 ω = true
        · exact absurd ⟨h1, h0'⟩ hnc
        · have h1' : d1 ω = false := by simpa using h1
          rw [h1', h0']
    rw [hexcl ω key, sub_self]
  rw [hzero, add_zero, cace]
  exact (measureReal_mul_integral_cond (measure_ne_top μ _) _).symm

/-- **The LATE / CACE theorem** (Ding Theorem 21.1, p. 284): when the instrument is
relevant, the ratio of the reduced form to the first stage is the complier average causal
effect. -/
theorem cace_eq_ittContrast_div [IsProbabilityMeasure μ]
    -- USER-INPUT: the three IV assumptions; Ding Assumptions 21.1–21.3
    (hrand : IVRandomized μ Z d1 d0 y1 y0) (hmono : NoDefiers d1 d0)
    (hexcl : ExclusionRestriction d1 d0 y1 y0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0)
    -- USER-INPUT: instrument relevance `τ_D ≠ 0`; Ding Theorem 21.1 (fails for a weak
    -- instrument)
    (hrel : ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω)) ≠ 0) :
    cace μ d1 d0 y1 y0
      = ittContrast μ Z (obs Z y1 y0) / ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω)) := by
  rw [eq_div_iff hrel,
    firstStage_eq_prob_complier hrand hmono hZ hd1 hd0 hy1 hy0 hZ1 hZ0,
    reducedForm_eq_prob_complier_mul_cace hrand hmono hexcl hZ hd1 hd0 hy1 hy0 hi1 hi0 hZ1 hZ0,
    mul_comm]

/-- **The Wald ratio in observable form** (Ding Corollary 21.1, p. 285): written out, the
identification formula uses only the observed outcome and treatment in the two instrument
arms. -/
theorem cace_eq_wald_ratio [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 y1 y0) (hmono : NoDefiers d1 d0)
    (hexcl : ExclusionRestriction d1 d0 y1 y0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0)
    (hrel : ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω)) ≠ 0) :
    cace μ d1 d0 y1 y0
      = (∫ ω, obs Z y1 y0 ω ∂(μ[|{ω | Z ω = true}])
          - ∫ ω, obs Z y1 y0 ω ∂(μ[|{ω | Z ω = false}]))
        / (∫ ω, ind (obsTreat Z d1 d0 ω) ∂(μ[|{ω | Z ω = true}])
          - ∫ ω, ind (obsTreat Z d1 d0 ω) ∂(μ[|{ω | Z ω = false}])) := by
  rw [cace_eq_ittContrast_div hrand hmono hexcl hZ hd1 hd0 hy1 hy0 hi1 hi0 hZ1 hZ0 hrel]
  rfl

/-- **Identification of the never-taker proportion** (Ding Theorem 22.1, p. 302):
`π_n = P(D = 0 | Z = 1)`. -/
theorem prob_neverTaker_eq [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 y1 y0) (hmono : NoDefiers d1 d0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) :
    (μ (typeSet d1 d0 ComplianceType.neverTaker)).toReal
      = ((μ[|{ω | Z ω = true}]) {ω | obsTreat Z d1 d0 ω = false}).toReal := by
  have hT : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
  have hS : MeasurableSet {ω | obsTreat Z d1 d0 ω = false} := by
    have : Measurable (obsTreat Z d1 d0) := by
      unfold obsTreat
      exact Measurable.ite (hZ (measurableSet_singleton true)) hd1 hd0
    exact this (measurableSet_singleton false)
  have hNeq : typeSet d1 d0 ComplianceType.neverTaker = {ω | d1 ω = false} := by
    rw [typeSet_eq_inter]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, dOneOf, dZeroOf]
    refine ⟨fun h => h.1, fun h1 => ⟨h1, ?_⟩⟩
    by_contra h0
    have h0' : d0 ω = true := by simpa using h0
    rw [hmono ω h0'] at h1
    exact Bool.noConfusion h1
  have hmf : Measurable (fun ω => if d1 ω = false then (1 : ℝ) else 0) :=
    measurable_boolComp (fun q : Bool × Bool => if q.1 = false then (1 : ℝ) else 0) hd1 hd0
  have hif : Integrable (fun ω => if d1 ω = false then (1 : ℝ) else 0) μ := by
    refine integrable_boolComp (fun q : Bool × Bool => if q.1 = false then (1 : ℝ) else 0)
      hd1 hd0 1 (fun q => ?_)
    by_cases h : q.1 = false <;> simp [h]
  have hindep : IndepFun (fun ω => if d1 ω = false then (1 : ℝ) else 0) Z μ :=
    indepFun_boolComp hrand (fun q : Bool × Bool => if q.1 = false then (1 : ℝ) else 0)
  have hA : ∫ ω, (if d1 ω = false then (1 : ℝ) else 0) ∂μ
      = (μ (typeSet d1 d0 ComplianceType.neverTaker)).toReal := by
    have hfe : (fun ω => if d1 ω = false then (1 : ℝ) else 0)
        = Set.indicator {ω | d1 ω = false} 1 := by
      funext ω
      by_cases h : d1 ω = false <;> simp [h]
    have hs1 : MeasurableSet {ω | d1 ω = false} := hd1 (measurableSet_singleton false)
    rw [hfe, integral_indicator_one hs1, measureReal_def, hNeq]
  have hB : ∫ ω, (if d1 ω = false then (1 : ℝ) else 0) ∂(μ[|{ω | Z ω = true}])
      = ((μ[|{ω | Z ω = true}]) {ω | obsTreat Z d1 d0 ω = false}).toReal := by
    rw [integral_cond_congr hT (g := Set.indicator {ω | obsTreat Z d1 d0 ω = false} 1)
      (fun ω hω => by
        simp only [Set.mem_setOf_eq] at hω
        by_cases h : d1 ω = false <;>
          simp [h, obsTreat, hω]),
      integral_indicator_one hS, measureReal_def]
  rw [← hA, ← integral_cond_arm_eq_of_indepFun hindep hif hmf hZ hZ1, hB]

/-- **Identification of the always-taker proportion** (Ding Theorem 22.1, p. 302):
`π_a = P(D = 1 | Z = 0)`. -/
theorem prob_alwaysTaker_eq [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 y1 y0) (hmono : NoDefiers d1 d0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    (μ (typeSet d1 d0 ComplianceType.alwaysTaker)).toReal
      = ((μ[|{ω | Z ω = false}]) {ω | obsTreat Z d1 d0 ω = true}).toReal := by
  have hF : MeasurableSet {ω | Z ω = false} := hZ (measurableSet_singleton false)
  have hS : MeasurableSet {ω | obsTreat Z d1 d0 ω = true} := by
    have : Measurable (obsTreat Z d1 d0) := by
      unfold obsTreat
      exact Measurable.ite (hZ (measurableSet_singleton true)) hd1 hd0
    exact this (measurableSet_singleton true)
  have hAeq : typeSet d1 d0 ComplianceType.alwaysTaker = {ω | d0 ω = true} := by
    rw [typeSet_eq_inter]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, dOneOf, dZeroOf]
    exact ⟨fun h => h.2, fun h0 => ⟨hmono ω h0, h0⟩⟩
  have hmf : Measurable (fun ω => if d0 ω = true then (1 : ℝ) else 0) :=
    measurable_boolComp (fun q : Bool × Bool => if q.2 = true then (1 : ℝ) else 0) hd1 hd0
  have hif : Integrable (fun ω => if d0 ω = true then (1 : ℝ) else 0) μ := by
    refine integrable_boolComp (fun q : Bool × Bool => if q.2 = true then (1 : ℝ) else 0)
      hd1 hd0 1 (fun q => ?_)
    by_cases h : q.2 = true <;> simp [h]
  have hindep : IndepFun (fun ω => if d0 ω = true then (1 : ℝ) else 0) Z μ :=
    indepFun_boolComp hrand (fun q : Bool × Bool => if q.2 = true then (1 : ℝ) else 0)
  have hA : ∫ ω, (if d0 ω = true then (1 : ℝ) else 0) ∂μ
      = (μ (typeSet d1 d0 ComplianceType.alwaysTaker)).toReal := by
    have hfe : (fun ω => if d0 ω = true then (1 : ℝ) else 0)
        = Set.indicator {ω | d0 ω = true} 1 := by
      funext ω
      by_cases h : d0 ω = true <;> simp [h]
    have hs0 : MeasurableSet {ω | d0 ω = true} := hd0 (measurableSet_singleton true)
    rw [hfe, integral_indicator_one hs0, measureReal_def, hAeq]
  have hB : ∫ ω, (if d0 ω = true then (1 : ℝ) else 0) ∂(μ[|{ω | Z ω = false}])
      = ((μ[|{ω | Z ω = false}]) {ω | obsTreat Z d1 d0 ω = true}).toReal := by
    rw [integral_cond_congr hF (g := Set.indicator {ω | obsTreat Z d1 d0 ω = true} 1)
      (fun ω hω => by
        simp only [Set.mem_setOf_eq] at hω
        by_cases h : d0 ω = true <;>
          simp [h, obsTreat, hω]),
      integral_indicator_one hS, measureReal_def]
  rw [← hA, ← integral_cond_arm_eq_of_indepFun hindep hif hmf hZ hZ0, hB]

end StatLean.CausalInference
