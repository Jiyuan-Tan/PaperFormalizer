module
public import StatLean.CausalInference.IV.ComplianceTypes
public import StatLean.CausalInference.ForMathlib.CondAlgebra

@[expose] public section

/-!
# Instrumental inequalities — the testable implications of the IV model

The IV assumptions are not vacuous: for a **binary** outcome they imply four inequalities
among quantities that are functions of the observed distribution alone,

$$\mathbb E[Q\mid Z=1]-\mathbb E[Q\mid Z=0]\ \ge\ 0
  \qquad\text{for } Q\in\{DY,\;D(1-Y),\;(D-1)Y,\;D+Y-DY\}.$$

A violation in data refutes the conjunction of random assignment, monotonicity and the
exclusion restriction — so unlike most identification assumptions, this package is
partially falsifiable.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). **Theorem 22.2** (Instrumental Variable
Inequalities, §22.2, p. 304, eq. (22.1)), under Assumptions 21.1–21.3 with a binary
outcome. (`Ding Theorem 22.2`.) Related discussion of testable implications is in
G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
Sciences*, Cambridge University Press, 2015, ch. 25. (`IR ch. 25`.)

**Proof formalization notes.** Each inequality is proved by the same three-step recipe:
random assignment replaces the arm-conditional means by unconditional means of the
corresponding potential quantities; the mixture over compliance types is then split;
monotonicity kills the defier stratum and the exclusion restriction makes the always- and
never-taker strata cancel between the two arms. What remains is the complier stratum with
a sign that is forced by `0 ≤ Y ≤ 1` — which is where binariness of the outcome is used,
and why the inequalities have no unbounded-outcome analogue. The four differences equal
`P(complier)` times, respectively, `E[Y(1)|C]`, `E[1-Y(1)|C]`, `E[Y(0)|C]` (with the sign
flip built into `(D-1)Y`) and `E[1-Y(0)|C]`; those exact identities are stated first and
the inequalities follow.

**Bibliographic comments.** The inequalities are due to A. Balke and J. Pearl, "Bounds on
treatment effects from studies with imperfect compliance," *J. Amer. Statist. Assoc.*
**92** (1997), 1171–1176, and (in a different form) B. Pearl, "On the testability of
causal models with latent and instrumental variables," *UAI* (1995), 435–443.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z d1 d0 b1 b0 : Ω → Bool}

/-- The observed **binary** outcome `Y = Y(Z)` under a binary-outcome IV model. -/
def obsBool (Z b1 b0 : Ω → Bool) : Ω → Bool := fun ω => if Z ω then b1 ω else b0 ω

/-! ### Elementary facts about the real indicator of a `Bool` -/

private lemma ind_true : ind true = 1 := rfl

private lemma ind_false : ind false = 0 := rfl

private lemma ind_nonneg (b : Bool) : 0 ≤ ind b := by cases b <;> simp [ind]

private lemma ind_le_one (b : Bool) : ind b ≤ 1 := by cases b <;> simp [ind]

/-- `ind` separates the two `Bool`s, so an equality of real potential outcomes obtained
from the exclusion restriction is an equality of the underlying binary outcomes. -/
private lemma ind_injective : Function.Injective (ind) := by
  intro a b h
  cases a <;> cases b <;> simp_all [ind]

/-- Any function of two `Bool`s is bounded by the sum of the absolute values it takes. -/
private lemma abs_G_le (G : Bool → Bool → ℝ) (d y : Bool) :
    |G d y| ≤ |G true true| + |G true false| + |G false true| + |G false false| := by
  have h1 := abs_nonneg (G true true)
  have h2 := abs_nonneg (G true false)
  have h3 := abs_nonneg (G false true)
  have h4 := abs_nonneg (G false false)
  cases d <;> cases y <;> linarith

/-! ### Measure-theoretic bookkeeping -/

/-- A bounded measurable function on a probability space is integrable. -/
private lemma integrable_of_abs_le [IsProbabilityMeasure μ] {f : Ω → ℝ} {C : ℝ}
    (hf : Measurable f) (hb : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hb ω)

/-- Two functions agreeing on the conditioning event have the same conditional integral. -/
private lemma integral_cond_congr {s : Set Ω} (hs : MeasurableSet s) {f g : Ω → ℝ}
    (h : Set.EqOn f g s) : ∫ ω, f ω ∂(μ[|s]) = ∫ ω, g ω ∂(μ[|s]) := by
  rw [integral_cond_eq_setIntegral, integral_cond_eq_setIntegral, setIntegral_congr_fun hs h]

/-- The compliance type as a function of the *pair* of potential treatments; used only to
exhibit `typeSet` as a preimage under `ω ↦ (D(1) ω, D(0) ω)`. -/
private def typeOfPair (p : Bool × Bool) : ComplianceType :=
  match p.1, p.2 with
  | true, true => ComplianceType.alwaysTaker
  | true, false => ComplianceType.complier
  | false, true => ComplianceType.defier
  | false, false => ComplianceType.neverTaker

/-- Each compliance-type event is measurable. -/
private lemma measurableSet_typeSet (hd1 : Measurable d1) (hd0 : Measurable d0)
    (t : ComplianceType) : MeasurableSet (typeSet d1 d0 t) := by
  have h : typeSet d1 d0 t
      = (fun ω => (d1 ω, d0 ω)) ⁻¹' {p : Bool × Bool | typeOfPair p = t} := rfl
  rw [h]
  exact (hd1.prodMk hd0) MeasurableSet.of_discrete

private lemma mem_typeSet_alwaysTaker' {ω : Ω} :
    ω ∈ typeSet d1 d0 ComplianceType.alwaysTaker ↔ d1 ω = true ∧ d0 ω = true := by
  unfold typeSet ComplianceType.of
  simp only [Set.mem_setOf_eq]
  cases d1 ω <;> cases d0 ω <;> simp

private lemma mem_typeSet_neverTaker' {ω : Ω} :
    ω ∈ typeSet d1 d0 ComplianceType.neverTaker ↔ d1 ω = false ∧ d0 ω = false := by
  unfold typeSet ComplianceType.of
  simp only [Set.mem_setOf_eq]
  cases d1 ω <;> cases d0 ω <;> simp

/-! ### The master identity

All four inequalities are the same computation for four different functions `G` of the
observed treatment and the observed binary outcome: random assignment turns the arm
contrast of `G(D, Y)` into `E[G(D(1), Y(1)) - G(D(0), Y(0))]`, the compliance-type
partition splits that expectation, monotonicity kills the defier cell and the exclusion
restriction kills the always- and never-taker cells. -/

private lemma ittContrast_obs_eq [IsProbabilityMeasure μ] {G : Bool → Bool → ℝ}
    (hrand : IVRandomized μ Z d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hmono : NoDefiers d1 d0)
    (hexcl : ExclusionRestriction d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hb1 : Measurable b1) (hb0 : Measurable b0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    ittContrast μ Z (fun ω => G (obsTreat Z d1 d0 ω) (obsBool Z b1 b0 ω))
      = ∫ ω in typeSet d1 d0 ComplianceType.complier,
          (G true (b1 ω) - G false (b0 ω)) ∂μ := by
  have hindm : Measurable ind := Measurable.of_discrete
  have hG0 : Measurable (fun b : Bool => G b false) := Measurable.of_discrete
  have hG1 : Measurable (fun b : Bool => G b true) := Measurable.of_discrete
  -- every function of a `Bool` is affine in its indicator
  have hGdec : ∀ d y : Bool, G d y = G d false + (G d true - G d false) * ind y := by
    intro d y; cases y <;> simp [ind]
  -- the two potential versions of the observed statistic
  have hy1 : Measurable fun ω => G (d1 ω) (b1 ω) := by
    have h : (fun ω => G (d1 ω) (b1 ω))
        = fun ω => G (d1 ω) false + (G (d1 ω) true - G (d1 ω) false) * ind (b1 ω) :=
      funext fun ω => hGdec _ _
    rw [h]
    exact (hG0.comp hd1).add (((hG1.comp hd1).sub (hG0.comp hd1)).mul (hindm.comp hb1))
  have hy0 : Measurable fun ω => G (d0 ω) (b0 ω) := by
    have h : (fun ω => G (d0 ω) (b0 ω))
        = fun ω => G (d0 ω) false + (G (d0 ω) true - G (d0 ω) false) * ind (b0 ω) :=
      funext fun ω => hGdec _ _
    rw [h]
    exact (hG0.comp hd0).add (((hG1.comp hd0).sub (hG0.comp hd0)).mul (hindm.comp hb0))
  have hI1 : Integrable (fun ω => G (d1 ω) (b1 ω)) μ :=
    integrable_of_abs_le hy1 fun ω => abs_G_le G _ _
  have hI0 : Integrable (fun ω => G (d0 ω) (b0 ω)) μ :=
    integrable_of_abs_le hy0 fun ω => abs_G_le G _ _
  -- independence of each potential statistic from the instrument
  have hrand' : IndepFun (fun ω => ((d1 ω, d0 ω), (ind (b1 ω), ind (b0 ω)))) Z μ := hrand
  have hA : Measurable (fun p : (Bool × Bool) × (ℝ × ℝ) => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hA' : Measurable (fun p : (Bool × Bool) × (ℝ × ℝ) => p.1.2) :=
    measurable_snd.comp measurable_fst
  have hB : Measurable (fun p : (Bool × Bool) × (ℝ × ℝ) => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hB' : Measurable (fun p : (Bool × Bool) × (ℝ × ℝ) => p.2.2) :=
    measurable_snd.comp measurable_snd
  have hφ : Measurable (fun p : (Bool × Bool) × (ℝ × ℝ) =>
      G p.1.1 false + (G p.1.1 true - G p.1.1 false) * p.2.1) :=
    (hG0.comp hA).add (((hG1.comp hA).sub (hG0.comp hA)).mul hB)
  have hψ : Measurable (fun p : (Bool × Bool) × (ℝ × ℝ) =>
      G p.1.2 false + (G p.1.2 true - G p.1.2 false) * p.2.2) :=
    (hG0.comp hA').add (((hG1.comp hA').sub (hG0.comp hA')).mul hB')
  have hi1 : IndepFun (fun ω => G (d1 ω) (b1 ω)) Z μ := by
    have heq : (fun ω => G (d1 ω) (b1 ω))
        = (fun p : (Bool × Bool) × (ℝ × ℝ) =>
            G p.1.1 false + (G p.1.1 true - G p.1.1 false) * p.2.1)
          ∘ fun ω => ((d1 ω, d0 ω), (ind (b1 ω), ind (b0 ω))) :=
      funext fun ω => hGdec _ _
    rw [heq]
    exact hrand'.comp hφ measurable_id
  have hi0 : IndepFun (fun ω => G (d0 ω) (b0 ω)) Z μ := by
    have heq : (fun ω => G (d0 ω) (b0 ω))
        = (fun p : (Bool × Bool) × (ℝ × ℝ) =>
            G p.1.2 false + (G p.1.2 true - G p.1.2 false) * p.2.2)
          ∘ fun ω => ((d1 ω, d0 ω), (ind (b1 ω), ind (b0 ω))) :=
      funext fun ω => hGdec _ _
    rw [heq]
    exact hrand'.comp hψ measurable_id
  -- Step 1: random assignment removes the conditioning on the arm
  have hT : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
  have hF : MeasurableSet {ω | Z ω = false} := hZ (measurableSet_singleton false)
  have e1 : Set.EqOn (fun ω => G (obsTreat Z d1 d0 ω) (obsBool Z b1 b0 ω))
      (fun ω => G (d1 ω) (b1 ω)) {ω | Z ω = true} := by
    intro ω hω
    have hz : Z ω = true := hω
    simp only [obsTreat, obsBool, hz, if_true]
  have e0 : Set.EqOn (fun ω => G (obsTreat Z d1 d0 ω) (obsBool Z b1 b0 ω))
      (fun ω => G (d0 ω) (b0 ω)) {ω | Z ω = false} := by
    intro ω hω
    have hz : Z ω = false := hω
    simp only [obsTreat, obsBool, hz, if_false, Bool.false_eq_true]
  have hstep1 : ittContrast μ Z (fun ω => G (obsTreat Z d1 d0 ω) (obsBool Z b1 b0 ω))
      = ∫ ω, (G (d1 ω) (b1 ω) - G (d0 ω) (b0 ω)) ∂μ := by
    simp only [ittContrast, primaFacie, treatedEvent]
    rw [integral_cond_congr hT e1, integral_cond_congr hF e0,
      integral_cond_arm_eq_of_indepFun hi1 hI1 hy1 hZ hZ1,
      integral_cond_arm_eq_of_indepFun hi0 hI0 hy0 hZ hZ0]
    exact (integral_sub hI1 hI0).symm
  -- Step 2: split the expectation over the compliance types
  have hf : Integrable (fun ω => G (d1 ω) (b1 ω) - G (d0 ω) (b0 ω)) μ := hI1.sub hI0
  have hmeasT : ∀ t : ComplianceType, MeasurableSet (typeSet d1 d0 t) :=
    fun t => measurableSet_typeSet hd1 hd0 t
  have hdisj : Pairwise (Function.onFun Disjoint fun t : ComplianceType => typeSet d1 d0 t) :=
    fun _ _ hst => typeSet_disjoint hst
  have hsum : ∫ ω, (G (d1 ω) (b1 ω) - G (d0 ω) (b0 ω)) ∂μ
      = ∑ t : ComplianceType,
          ∫ ω in typeSet d1 d0 t, (G (d1 ω) (b1 ω) - G (d0 ω) (b0 ω)) ∂μ := by
    calc ∫ ω, (G (d1 ω) (b1 ω) - G (d0 ω) (b0 ω)) ∂μ
        = ∫ ω in Set.univ, (G (d1 ω) (b1 ω) - G (d0 ω) (b0 ω)) ∂μ := setIntegral_univ.symm
      _ = ∫ ω in ⋃ t : ComplianceType, typeSet d1 d0 t,
            (G (d1 ω) (b1 ω) - G (d0 ω) (b0 ω)) ∂μ := by rw [iUnion_typeSet]
      _ = _ := integral_iUnion_fintype hmeasT hdisj fun _ => hf.integrableOn
  -- Step 3: monotonicity empties the defier cell; exclusion cancels the non-complier cells
  have hzero : ∀ t ∈ Finset.univ, t ≠ ComplianceType.complier →
      ∫ ω in typeSet d1 d0 t, (G (d1 ω) (b1 ω) - G (d0 ω) (b0 ω)) ∂μ = 0 := by
    intro t _ ht
    cases t with
    | complier => exact absurd rfl ht
    | defier =>
        rw [noDefiers_iff_typeSet_defier_eq_empty.1 hmono]
        exact setIntegral_empty
    | alwaysTaker =>
        refine setIntegral_eq_zero_of_forall_eq_zero fun ω hω => ?_
        obtain ⟨h1, h0⟩ := mem_typeSet_alwaysTaker'.1 hω
        have hb : b1 ω = b0 ω := ind_injective (hexcl ω (by rw [h1, h0]))
        rw [h1, h0, hb, sub_self]
    | neverTaker =>
        refine setIntegral_eq_zero_of_forall_eq_zero fun ω hω => ?_
        obtain ⟨h1, h0⟩ := mem_typeSet_neverTaker'.1 hω
        have hb : b1 ω = b0 ω := ind_injective (hexcl ω (by rw [h1, h0]))
        rw [h1, h0, hb, sub_self]
  rw [hstep1, hsum, Finset.sum_eq_single_of_mem ComplianceType.complier (Finset.mem_univ _) hzero]
  refine setIntegral_congr_fun (hmeasT _) fun ω hω => ?_
  obtain ⟨h1, h0⟩ := mem_typeSet_complier.1 hω
  rw [h1, h0]

/-- **First IV inequality, exact form** (Ding Theorem 22.2, `Q = DY`): the arm contrast
equals the complier proportion times the complier mean of `Y(1)`. -/
theorem ittContrast_treat_mul_outcome [IsProbabilityMeasure μ]
    -- USER-INPUT: random assignment; Ding Assumption 21.1
    (hrand : IVRandomized μ Z d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    -- USER-INPUT: monotonicity; Ding Assumption 21.2
    (hmono : NoDefiers d1 d0)
    -- USER-INPUT: the exclusion restriction; Ding Assumption 21.3
    (hexcl : ExclusionRestriction d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hb1 : Measurable b1) (hb0 : Measurable b0)
    -- USER-INPUT: both instrument arms have positive probability; Ding §21.2
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω) * ind (obsBool Z b1 b0 ω))
      = (μ (typeSet d1 d0 ComplianceType.complier)).toReal
          * ∫ ω, ind (b1 ω) ∂(μ[|typeSet d1 d0 ComplianceType.complier]) := by
  have h : ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω) * ind (obsBool Z b1 b0 ω))
      = ∫ ω in typeSet d1 d0 ComplianceType.complier,
          (ind true * ind (b1 ω) - ind false * ind (b0 ω)) ∂μ :=
    ittContrast_obs_eq (G := fun d y => ind d * ind y) hrand hmono hexcl hZ hd1 hd0 hb1 hb0
      hZ1 hZ0
  rw [h, measureReal_mul_integral_cond (measure_ne_top μ _)]
  refine setIntegral_congr_fun (measurableSet_typeSet hd1 hd0 _) fun ω _ => ?_
  rw [ind_true, ind_false]
  ring

/-- **First instrumental inequality** (Ding Theorem 22.2, eq. (22.1), `Q = DY`). -/
theorem instrumentalInequality_DY [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hmono : NoDefiers d1 d0)
    (hexcl : ExclusionRestriction d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hb1 : Measurable b1) (hb0 : Measurable b0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    0 ≤ ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω) * ind (obsBool Z b1 b0 ω)) := by
  have h : ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω) * ind (obsBool Z b1 b0 ω))
      = ∫ ω in typeSet d1 d0 ComplianceType.complier,
          (ind true * ind (b1 ω) - ind false * ind (b0 ω)) ∂μ :=
    ittContrast_obs_eq (G := fun d y => ind d * ind y) hrand hmono hexcl hZ hd1 hd0 hb1 hb0
      hZ1 hZ0
  rw [h]
  refine setIntegral_nonneg (measurableSet_typeSet hd1 hd0 _) fun ω _ => ?_
  rw [ind_true, ind_false]
  linarith [ind_nonneg (b1 ω)]

/-- **Second instrumental inequality** (Ding Theorem 22.2, `Q = D(1-Y)`). -/
theorem instrumentalInequality_D_one_sub_Y [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hmono : NoDefiers d1 d0)
    (hexcl : ExclusionRestriction d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hb1 : Measurable b1) (hb0 : Measurable b0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    0 ≤ ittContrast μ Z
          (fun ω => ind (obsTreat Z d1 d0 ω) * (1 - ind (obsBool Z b1 b0 ω))) := by
  have h : ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω) * (1 - ind (obsBool Z b1 b0 ω)))
      = ∫ ω in typeSet d1 d0 ComplianceType.complier,
          (ind true * (1 - ind (b1 ω)) - ind false * (1 - ind (b0 ω))) ∂μ :=
    ittContrast_obs_eq (G := fun d y => ind d * (1 - ind y)) hrand hmono hexcl hZ hd1 hd0 hb1 hb0
      hZ1 hZ0
  rw [h]
  refine setIntegral_nonneg (measurableSet_typeSet hd1 hd0 _) fun ω _ => ?_
  rw [ind_true, ind_false]
  linarith [ind_le_one (b1 ω)]

/-- **Third instrumental inequality** (Ding Theorem 22.2, `Q = (D-1)Y`). -/
theorem instrumentalInequality_D_sub_one_Y [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hmono : NoDefiers d1 d0)
    (hexcl : ExclusionRestriction d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hb1 : Measurable b1) (hb0 : Measurable b0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    0 ≤ ittContrast μ Z
          (fun ω => (ind (obsTreat Z d1 d0 ω) - 1) * ind (obsBool Z b1 b0 ω)) := by
  have h : ittContrast μ Z (fun ω => (ind (obsTreat Z d1 d0 ω) - 1) * ind (obsBool Z b1 b0 ω))
      = ∫ ω in typeSet d1 d0 ComplianceType.complier,
          ((ind true - 1) * ind (b1 ω) - (ind false - 1) * ind (b0 ω)) ∂μ :=
    ittContrast_obs_eq (G := fun d y => (ind d - 1) * ind y) hrand hmono hexcl hZ hd1 hd0 hb1 hb0
      hZ1 hZ0
  rw [h]
  refine setIntegral_nonneg (measurableSet_typeSet hd1 hd0 _) fun ω _ => ?_
  rw [ind_true, ind_false]
  linarith [ind_nonneg (b0 ω)]

/-- **Fourth instrumental inequality** (Ding Theorem 22.2, `Q = D + Y - DY`). -/
theorem instrumentalInequality_D_add_Y_sub_DY [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hmono : NoDefiers d1 d0)
    (hexcl : ExclusionRestriction d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hb1 : Measurable b1) (hb0 : Measurable b0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    0 ≤ ittContrast μ Z
          (fun ω => ind (obsTreat Z d1 d0 ω) + ind (obsBool Z b1 b0 ω)
                      - ind (obsTreat Z d1 d0 ω) * ind (obsBool Z b1 b0 ω)) := by
  have h : ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω) + ind (obsBool Z b1 b0 ω)
        - ind (obsTreat Z d1 d0 ω) * ind (obsBool Z b1 b0 ω))
      = ∫ ω in typeSet d1 d0 ComplianceType.complier,
          ((ind true + ind (b1 ω) - ind true * ind (b1 ω))
            - (ind false + ind (b0 ω) - ind false * ind (b0 ω))) ∂μ :=
    ittContrast_obs_eq (G := fun d y => ind d + ind y - ind d * ind y) hrand hmono hexcl hZ hd1 hd0
      hb1 hb0 hZ1 hZ0
  rw [h]
  refine setIntegral_nonneg (measurableSet_typeSet hd1 hd0 _) fun ω _ => ?_
  rw [ind_true, ind_false]
  linarith [ind_le_one (b0 ω)]

/-- **Falsifiability** (Ding §22.2): if any of the four observable contrasts is negative,
no IV model satisfying Assumptions 21.1–21.3 can have generated the data. Stated as the
contrapositive of the first inequality; the other three are analogous. -/
theorem not_ivModel_of_neg [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hb1 : Measurable b1) (hb0 : Measurable b0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0)
    -- USER-INPUT: an observed violation of the first inequality
    (hviol : ittContrast μ Z
        (fun ω => ind (obsTreat Z d1 d0 ω) * ind (obsBool Z b1 b0 ω)) < 0) :
    ¬ (IVRandomized μ Z d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω))
        ∧ NoDefiers d1 d0
        ∧ ExclusionRestriction d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω))) := by
  rintro ⟨hrand, hmono, hexcl⟩
  have := instrumentalInequality_DY hrand hmono hexcl hZ hd1 hd0 hb1 hb0 hZ1 hZ0
  linarith

end StatLean.CausalInference
