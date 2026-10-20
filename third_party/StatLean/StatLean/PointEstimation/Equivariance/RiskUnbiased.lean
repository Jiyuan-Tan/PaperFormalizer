module
public import StatLean.PointEstimation.Equivariance.General
public import StatLean.PointEstimation.Equivariance.LocationStructure
public import StatLean.PointEstimation.ForMathlib.ConvexMinimizers
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Risk-unbiasedness of minimum risk equivariant estimators

An estimator is **risk-unbiased** when, on the average, it is at least as close to the
true parameter value as to any false one: `E_θ L(θ, δ(X)) ≤ E_θ L(θ', δ(X))` for every
`θ' ≠ θ`. This is the decision-theoretic extension of unbiasedness — under squared error
it reduces to ordinary unbiasedness, under absolute error to median-unbiasedness.

This file proves that minimum risk equivariant estimators are risk-unbiased, in the
general group setting and in the concrete location setting.

* `isRiskUnbiased_of_equivariant_min` — general form: a transitive induced action on the
  parameter space together with a **commutative** action on the decision space forces a
  risk-minimizing equivariant estimator to be risk-unbiased.
* `isLocRiskUnbiased_of_isLocMRE` / `isRiskUnbiased_of_isLocMRE` — the location
  specialization, where both hypotheses hold automatically (translations act transitively
  on `ℝ` and commutatively on the decisions).
* `locEquivariant_sub_bias` / `integral_eq_zero_of_isLocMRE_sq` — the squared-error
  refinement: recentring an equivariant estimator at its (constant) bias keeps it
  equivariant, makes it unbiased, and strictly improves the risk, whence a
  finite-risk MRE estimator is unbiased.

Both hypotheses of the general theorem are genuinely needed: dropping transitivity or
commutativity produces counterexamples, both of which are exhibited classically by the
normal location-scale problem with a standardized squared-error loss.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.1 (First
Examples), Lemma 1.23, Definition 1.24 (risk-unbiasedness) and Theorem 1.27 (an MRE estimator
for a convex even loss is risk-unbiased). (`TPE2 §3.1 Lem 1.23, Def 1.24, Thm 1.27`.)

**Proof formalization notes.**
* The general proof is three lines and does **not** use model invariance: transitivity
  supplies `g` with `g • θ' = θ`; loss invariance rewrites `L θ' d` as `L θ (g • d)`;
  commutativity of the decision action makes `x ↦ g • δ x` equivariant, so the
  minimality hypothesis applies to it. We therefore state the sharper form, **omitting**
  the invariant-model hypothesis that the classical statement carries. Model invariance
  is what makes the minimality hypothesis `hmin` the natural notion of MRE in the first
  place, but it is not used in the implication.
* `hmin` is stated as an explicit hypothesis rather than through a bundled `IsMRE`
  predicate: the general setting has no canonical constant risk to minimize until
  transitivity has been used, and quantifying over measurable equivariant competitors is
  what the proof consumes.
* In the location case the proof is even shorter and needs no convexity or symmetry of
  the loss: `δ − a` is equivariant whenever `δ` is, so minimality applied to `δ − a`
  *is* risk-unbiasedness. We state that honest form; convexity and evenness of the loss
  enter only the *unbiasedness* (rather than risk-unbiasedness) statements.
* The classical squared-error statement deduces unbiasedness of the MRE estimator from
  its *uniqueness*; the argument in fact needs only finiteness of its risk, which is what
  `integral_eq_zero_of_isLocMRE_sq` assumes. This is a (weakening) deviation.
* The classical third part of the squared-error lemma — an equivariant UMVU estimator is
  MRE — is deliberately omitted here: it belongs to a file that may import the UMVU
  layer, which this area's layering forbids at the equivariance level.

**Bibliographic comments.** Risk-unbiasedness as the decision-theoretic generalization of
unbiasedness is due to E. L. Lehmann, "A general concept of unbiasedness," *Ann. Math.
Statist.* **22** (1951), 587–592. The equivariance framework in which it is proved here
originates with G. A. Hunt and C. Stein (unpublished manuscript, 1946), first reported by
M. A. Girshick and L. J. Savage, "Bayes and minimax estimates for quadratic loss
functions," *Proc. Second Berkeley Symp. Math. Statist. Probab.*, Univ. California Press,
1951, 53–73; the location case goes back to E. J. G. Pitman, "The estimation of the
location and scale parameters of a continuous population of any given form," *Biometrika*
**30** (1939), 391–421.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

/-! ## The general group setting -/

section General

variable {G Θ 𝓧 D : Type*} [Group G] [MeasurableSpace 𝓧] [MeasurableSpace D]
  [MulAction G 𝓧] [MulAction G Θ] [MulAction G D] [MeasurableConstSMul G D]

/-- Transporting an equivariant estimator by a group element keeps it equivariant, when
the action on the decision space is commutative. This is the step of
`isRiskUnbiased_of_equivariant_min` where commutativity is genuinely used. -/
theorem IsEquivariant.smul {δ : 𝓧 → D}
    -- USER-INPUT: the estimator is equivariant
    (hδeq : IsEquivariant (G := G) δ)
    -- USER-INPUT: the induced action on the decision space is commutative
    (hcomm : ∀ (g g' : G) (d : D), g • g' • d = g' • g • d)
    (g : G) :
    IsEquivariant (G := G) fun x => g • δ x := by
  intro h x
  show g • δ (h • x) = h • g • δ x
  rw [hδeq h x]
  exact hcomm g h (δ x)

/-- **A risk-minimizing equivariant estimator is risk-unbiased**, provided the induced
action on the parameter space is transitive and the action on the decision space is
commutative.

Transitivity lets us move the false parameter value `θ'` onto the true one by some `g`;
loss invariance then converts the cross risk against `θ'` into the risk of the transported
estimator `g • δ`, which commutativity of the decision action keeps equivariant. -/
theorem isRiskUnbiased_of_equivariant_min [MulAction.IsPretransitive G Θ]
    {P : Θ → Measure 𝓧} {L : Θ → D → ℝ≥0∞} {δ : 𝓧 → D}
    -- USER-INPUT: the loss is unchanged by the simultaneous parameter/decision action
    (hL : IsInvariantLoss (G := G) L)
    -- LEAN-ONLY: measurability of the estimator; only needed so that the transported
    -- estimator qualifies as a competitor in `hmin`
    (hδ : Measurable δ)
    -- USER-INPUT: the estimator is equivariant
    (hδeq : IsEquivariant (G := G) δ)
    -- USER-INPUT: the induced action on the decision space is commutative
    (hcomm : ∀ (g g' : G) (d : D), g • g' • d = g' • g • d)
    -- USER-INPUT: `δ` minimizes the risk among measurable equivariant estimators (MRE);
    -- under transitivity the risk is constant, so this is minimality of one number
    (hmin : ∀ δ', Measurable δ' → IsEquivariant (G := G) δ' →
      ∀ θ, risk P L δ θ ≤ risk P L δ' θ) :
    IsRiskUnbiased P L δ := by
  intro θ θ'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G θ' θ
  have hδ'meas : Measurable (fun x => g • δ x) := hδ.const_smul g
  have hδ'eq : IsEquivariant (G := G) (fun x => g • δ x) := hδeq.smul hcomm g
  have hkey := hmin (fun x => g • δ x) hδ'meas hδ'eq θ
  have hoff : crossRisk P L δ θ θ' = risk P L (fun x => g • δ x) θ := by
    unfold crossRisk risk crossRisk
    refine lintegral_congr fun x => ?_
    rw [← hg]
    exact (hL g θ' (δ x)).symm
  show crossRisk P L δ θ θ ≤ crossRisk P L δ θ θ'
  rw [hoff]
  exact hkey

end General

/-! ## The location specialization -/

section Location

variable {n : ℕ}

/-- The conditional mean minimizes mean squared error at the `ℝ≥0∞` level with no
second-moment hypothesis: outside `L²` both sides are `∞`. (Local copy of the same fact
used in `LocationMRE`; kept private to respect the file's frozen surface.) -/
private lemma lintegral_ofReal_sq_min {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {φ : Ω → ℝ} (hφ : Measurable φ) (w : ℝ) :
    ∫⁻ x, ENNReal.ofReal ((φ x - ∫ z, φ z ∂μ) ^ 2) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal ((φ x - w) ^ 2) ∂μ := by
  set m := ∫ z, φ z ∂μ with hm
  by_cases hL2 : MemLp φ 2 μ
  · have hf1 : Integrable (fun x => (φ x - m) ^ 2) μ :=
      (hL2.sub (memLp_const m)).integrable_sq
    have hf2 : Integrable (fun x => (φ x - w) ^ 2) μ :=
      (hL2.sub (memLp_const w)).integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal hf1 (ae_of_all _ fun x => sq_nonneg _),
        ← ofReal_integral_eq_lintegral_ofReal hf2 (ae_of_all _ fun x => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (integral_sq_sub_mean_le hL2 w)
  · have hnotMemLp : ∀ c : ℝ, ¬ MemLp (fun x => φ x - c) 2 μ := by
      intro c hc
      have h2 := hc.add (memLp_const c)
      rw [show (fun x => φ x - c) + (fun _ : Ω => c) = φ from by
            funext x; simp only [Pi.add_apply]; ring] at h2
      exact hL2 h2
    have hinf : ∀ c : ℝ, ∫⁻ x, ENNReal.ofReal ((φ x - c) ^ 2) ∂μ = ⊤ := by
      intro c
      by_contra hne
      have hlt : ∫⁻ x, ENNReal.ofReal ((φ x - c) ^ 2) ∂μ < ⊤ := lt_top_iff_ne_top.mpr hne
      have hfin : HasFiniteIntegral (fun x => (φ x - c) ^ 2) μ :=
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).mpr hlt
      have hasm : AEStronglyMeasurable (fun x => (φ x - c) ^ 2) μ :=
        ((hφ.sub_const c).pow_const 2).aestronglyMeasurable
      exact hnotMemLp c
        ((memLp_two_iff_integrable_sq (hφ.sub_const c).aestronglyMeasurable).mpr ⟨hasm, hfin⟩)
    rw [hinf m, hinf w]

/-- **A minimum risk equivariant location estimator is risk-unbiased.** Concretely: no
translate `δ − a` of the estimator has smaller expected loss at the base parameter.

No convexity, symmetry or boundedness of the loss is required — the entire content is
that `δ − a` is again equivariant, so equivariant minimality applies to it directly. -/
theorem isLocRiskUnbiased_of_isLocMRE (f : (Fin n → ℝ) → ℝ) (ρ : ℝ → ℝ)
    {δ : (Fin n → ℝ) → ℝ}
    -- USER-INPUT: `δ` is a minimum risk equivariant estimator for the loss `ρ(d − ξ)`
    (hδ : IsLocMRE f ρ δ)
    (a : ℝ) :
    locRisk f ρ δ ≤ ∫⁻ x, ENNReal.ofReal (ρ (δ x - a)) ∂(locationBase f) := by
  exact hδ.2.2 (fun x => δ x - a) (hδ.1.sub_const a) (hδ.2.1.sub_const a)

/-- The same statement in the general vocabulary: a minimum risk equivariant location
estimator is risk-unbiased for the location model with loss `ρ(d − ξ)`. -/
theorem isRiskUnbiased_of_isLocMRE (f : (Fin n → ℝ) → ℝ) (ρ : ℝ → ℝ)
    -- LEAN-ONLY: measurability of the loss; needed for the change of variables that
    -- transports the cross risk at `ξ` back to the base parameter
    (hρ : Measurable ρ)
    {δ : (Fin n → ℝ) → ℝ}
    -- USER-INPUT: `δ` is a minimum risk equivariant estimator
    (hδ : IsLocMRE f ρ δ) :
    IsRiskUnbiased (locationFamily f) (fun ξ d => ENNReal.ofReal (ρ (d - ξ))) δ := by
  intro ξ ξ'
  have hmeas := hδ.1
  have heq := hδ.2.1
  have hdiag : crossRisk (locationFamily f) (fun ξ d => ENNReal.ofReal (ρ (d - ξ))) δ ξ ξ
      = locRisk f ρ δ := locRisk_const f ρ δ hρ hmeas heq ξ
  have hoff : crossRisk (locationFamily f) (fun ξ d => ENNReal.ofReal (ρ (d - ξ))) δ ξ ξ'
      = ∫⁻ x, ENNReal.ofReal (ρ (δ x - (ξ' - ξ))) ∂(locationBase f) := by
    show ∫⁻ x, ENNReal.ofReal (ρ (δ x - ξ')) ∂(locationFamily f ξ) = _
    unfold locationFamily
    have hg : Measurable (fun x : Fin n → ℝ => ENNReal.ofReal (ρ (δ x - ξ'))) :=
      ENNReal.measurable_ofReal.comp (hρ.comp (hmeas.sub_const ξ'))
    have hmap : Measurable (fun x : Fin n → ℝ => x + ξ • (1 : Fin n → ℝ)) := by fun_prop
    rw [lintegral_map hg hmap]
    refine lintegral_congr fun x => ?_
    rw [heq ξ x, show δ x + ξ - ξ' = δ x - (ξ' - ξ) from by ring]
  show crossRisk (locationFamily f) (fun ξ d => ENNReal.ofReal (ρ (d - ξ))) δ ξ ξ ≤
      crossRisk (locationFamily f) (fun ξ d => ENNReal.ofReal (ρ (d - ξ))) δ ξ ξ'
  rw [hdiag, hoff]
  exact isLocRiskUnbiased_of_isLocMRE f ρ hδ (ξ' - ξ)

/-! ### Squared error: recentring at the bias -/

/-- **Recentring an equivariant estimator at its bias.** Under squared error, if `δ` is
equivariant and integrable at the base parameter, then subtracting its bias
`b = E₀[δ(X)]` leaves it equivariant, makes it unbiased, and does not increase the risk
(the improvement is exactly `b²`). -/
theorem locEquivariant_sub_bias (f : (Fin n → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density, so the base member is a probability law
    [IsProbabilityMeasure (locationBase f)]
    {δ : (Fin n → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the estimator
    (hδ : Measurable δ)
    -- USER-INPUT: the estimator is location equivariant
    (heq : IsLocEquivariant δ)
    -- USER-INPUT: the bias exists (finite first moment at the base parameter)
    (hint : Integrable δ (locationBase f)) :
    IsLocEquivariant (fun x => δ x - ∫ y, δ y ∂(locationBase f)) ∧
      (∫ x, (δ x - ∫ y, δ y ∂(locationBase f)) ∂(locationBase f) = 0) ∧
      locRisk f (fun t : ℝ => t ^ 2) (fun x => δ x - ∫ y, δ y ∂(locationBase f)) ≤
        locRisk f (fun t : ℝ => t ^ 2) δ := by
  set b := ∫ y, δ y ∂(locationBase f) with hb
  refine ⟨heq.sub_const b, ?_, ?_⟩
  · have hreal1 : (locationBase f).real Set.univ = 1 := by
      simp [Measure.real, measure_univ]
    rw [integral_sub hint (integrable_const b), integral_const, hreal1, one_smul, hb, sub_self]
  · have hmin0 := lintegral_ofReal_sq_min (μ := locationBase f) (φ := δ) hδ 0
    simp only [sub_zero] at hmin0
    exact hmin0

/-- **A finite-risk minimum risk equivariant estimator is unbiased under squared error.**

The classical statement derives this from *uniqueness* of the MRE estimator; the argument
in fact only needs its risk to be finite, since recentring improves the risk by exactly
the squared bias. -/
theorem integral_eq_zero_of_isLocMRE_sq (f : (Fin n → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    {δ : (Fin n → ℝ) → ℝ}
    -- USER-INPUT: `δ` is minimum risk equivariant under squared error
    (hMRE : IsLocMRE f (fun t : ℝ => t ^ 2) δ)
    -- USER-INPUT: the bias exists (finite first moment at the base parameter)
    (hint : Integrable δ (locationBase f))
    -- USER-INPUT: the estimator has finite risk; replaces the classical uniqueness
    (hfin : locRisk f (fun t : ℝ => t ^ 2) δ ≠ ∞) :
    ∫ x, δ x ∂(locationBase f) = 0 := by
  have hmeas := hMRE.1
  have heq := hMRE.2.1
  set b := ∫ x, δ x ∂(locationBase f) with hb
  have hL2 : MemLp δ 2 (locationBase f) := by
    refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr ?_
    refine ⟨(hmeas.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)]
    exact lt_top_iff_ne_top.mpr hfin
  obtain ⟨heq', _, hle⟩ := locEquivariant_sub_bias f hmeas heq hint
  have hge := hMRE.2.2 (fun x => δ x - b) (hmeas.sub_const b) heq'
  have hrisk_eq : locRisk f (fun t : ℝ => t ^ 2) (fun x => δ x - b)
      = locRisk f (fun t : ℝ => t ^ 2) δ := le_antisymm hle hge
  have hInt_d : Integrable (fun x => (δ x) ^ 2) (locationBase f) := hL2.integrable_sq
  have hInt_db : Integrable (fun x => (δ x - b) ^ 2) (locationBase f) :=
    (hL2.sub (memLp_const b)).integrable_sq
  have hr_d : locRisk f (fun t : ℝ => t ^ 2) δ
      = ENNReal.ofReal (∫ x, (δ x) ^ 2 ∂(locationBase f)) :=
    (ofReal_integral_eq_lintegral_ofReal hInt_d (ae_of_all _ fun x => sq_nonneg _)).symm
  have hr_db : locRisk f (fun t : ℝ => t ^ 2) (fun x => δ x - b)
      = ENNReal.ofReal (∫ x, (δ x - b) ^ 2 ∂(locationBase f)) :=
    (ofReal_integral_eq_lintegral_ofReal hInt_db (ae_of_all _ fun x => sq_nonneg _)).symm
  rw [hr_db, hr_d] at hrisk_eq
  have hreal : ∫ x, (δ x - b) ^ 2 ∂(locationBase f) = ∫ x, (δ x) ^ 2 ∂(locationBase f) :=
    (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => sq_nonneg _)
      (integral_nonneg fun x => sq_nonneg _)).mp hrisk_eq
  have hbv := integral_sq_sub_eq_variance_add_sq hL2 0
  simp only [sub_zero] at hbv
  rw [← hb] at hbv
  rw [hreal] at hbv
  have hbsq : b ^ 2 = 0 := by linarith
  exact (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hbsq

end Location

end StatLean.PointEstimation
