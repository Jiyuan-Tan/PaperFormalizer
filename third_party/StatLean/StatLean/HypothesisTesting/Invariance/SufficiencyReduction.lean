module
public import StatLean.HypothesisTesting.Invariance.AlmostInvariance
public import StatLean.PointEstimation.Sufficiency.Defs
public import StatLean.PointEstimation.Completeness.Defs
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section

/-!
# Invariance after sufficiency: almost invariance, power invariance, and legitimacy

Restricting attention to invariant tests is a departure from comparing tests purely by
their power functions, so it is natural to ask what invariance means *at the level of
power functions*. One implication is immediate: an invariant — indeed an almost invariant
— test has a power function invariant under the induced group. The converse fails in
general, but it holds once the problem has first been reduced to a **sufficient statistic
whose family of laws is boundedly complete**. That is the content of the first result
below, and it is what makes almost invariance the right class to work with.

Two consequences follow. First, a test that is UMP among almost invariant tests based on
the sufficient statistic is optimal in a much larger class: among *all* tests of the
original data whose power function depends on the parameter only through a maximal
invariant. Second — and this is the practical point — reducing by sufficiency **before**
applying invariance is legitimate: every invariant test of the raw data is matched, in
power, by an almost invariant (and, under the structural conditions for almost invariance,
by a genuinely invariant) test of the statistic, so nothing is lost by performing the two
reductions in that order.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 6 (Invariance), §6.5
(Almost Invariance), Lemma 6.5.1 (for a boundedly complete sufficient statistic, invariance of
the power function is equivalent to almost invariance), Theorem 6.5.2 and Theorem 6.5.3
(legitimacy of reducing by sufficiency before invariance). (`TSH4 §6.5 Lem 6.5.1, Thm 6.5.2,
Thm 6.5.3`.)

**Main results.**
* `power_invariant_iff_almostInvariant` — for a boundedly complete family of laws of the
  statistic, invariance of the power function ⟺ almost invariance of the test;
* `isUMP_of_isUMPAlmostInvariant_sufficient` — a UMP almost invariant test based on a
  sufficient statistic is UMP among all tests with power depending only on a maximal
  invariant of the parameter;
* `exists_almostInvariant_on_stat_of_invariant`,
  `exists_invariant_on_stat_of_invariant`,
  `isUMPInvariant_comp_of_isUMPInvariant_stat` — the three parts of the legitimacy of the
  sufficiency-then-invariance reduction.

**Proof formalization notes.**
* In the first result the group acts on the **statistic space** `𝓣`, and the relevant
  family is the family of laws `statLaw P T`. Bounded completeness is the point-estimation
  predicate `IsBoundedlyCompleteStat`, applied to that family; the invariance of the
  reduced problem is `IsInvariantModel` for `statLaw P T`. Sufficiency is *not* assumed
  here — the source's lemma needs only bounded completeness of the family of laws.
* Almost invariance of a test of the statistic is taken "a.e. `P^T`", i.e. with respect to
  every member `statLaw P T θ`, matching the source's exceptional-set convention.
* The induced group on the statistic space is supplied as a `MulAction G 𝓣` instance
  together with the intertwining law `T (g·x) = g·(T x)` (`hTcompat`). This is a
  **LEAN-ONLY** packaging of the source's setup, which imposes the compatibility condition
  `T x₁ = T x₂ ⟹ T(g x₁) = T(g x₂)` and *then defines* the induced transformation by
  `g̃ (T x) = T (g x)`; supplying the action as data plus the intertwining identity is the
  same content once the induced group exists, which is exactly what the condition asserts.
* Maximal invariance of the parameter-space map `v` is written inline as the two set-level
  conditions, so no measurable structure is demanded of the parameter space.

**Bibliographic comments.** The interplay of sufficiency and invariance — in particular the
legitimacy of reducing by sufficiency first — was settled in the invariance program of
G. A. Hunt and C. Stein ("Most stringent tests of statistical hypotheses," unpublished
manuscript, 1946) and C. Stein ("Some problems in multivariate analysis, Part I,"
Technical Report 6, Department of Statistics, Stanford University, 1956), and developed in
E. L. Lehmann's lecture tradition of the 1950s. A definitive treatment of when the two
reductions commute is due to W. J. Hall, R. A. Wijsman and J. K. Ghosh ("The relationship
between sufficiency and invariance with applications in sequential analysis," *Ann. Math.
Statist.* **36** (1965), 575–614). Bounded completeness as the hypothesis converting
power-function invariance into almost invariance of the test traces to E. L. Lehmann and
H. Scheffé ("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10**
(1950), 305–340).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation (IsInvariantModel statLaw HasSufficientKernel
  IsBoundedlyCompleteStat)

/-! ## Private measure-theoretic helpers for the sufficiency reduction -/

/-- Measurability of the θ-free conditional expectation `t ↦ ∫ φ dQ_t`. -/
private theorem measurable_condStat {𝓧' 𝓣' : Type*} [MeasurableSpace 𝓧'] [MeasurableSpace 𝓣']
    {φ : 𝓧' → ℝ} (Q : Kernel 𝓣' 𝓧') (hφ : Measurable φ) :
    Measurable (fun t => ∫ x, φ x ∂(Q t)) :=
  (hφ.stronglyMeasurable.integral_kernel (κ := Q)).measurable

/-- The θ-free conditional expectation of a `[0,1]`-valued test is `[0,1]`-valued. -/
private theorem condStat_mem_Icc {𝓧' 𝓣' : Type*} [MeasurableSpace 𝓧'] [MeasurableSpace 𝓣']
    {φ : 𝓧' → ℝ} (Q : Kernel 𝓣' 𝓧') [IsMarkovKernel Q]
    (hφb : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) (t : 𝓣') :
    (∫ x, φ x ∂(Q t)) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg (fun x => (hφb x).1), ?_⟩
  calc ∫ x, φ x ∂(Q t) ≤ ∫ _x, (1 : ℝ) ∂(Q t) :=
        integral_mono_of_nonneg (ae_of_all _ (fun x => (hφb x).1)) (integrable_const 1)
          (ae_of_all _ (fun x => (hφb x).2))
    _ = 1 := by simp

/-- **Pull-out / adjunction identity for the sufficiency kernel.** For a bounded measurable
`w` on the statistic space, integrating `w · (E[φ|T])` against the law of the statistic
equals integrating `(w ∘ T) · φ` against the raw law. Specialized to `w = 1` this is the
power-matching identity. -/
private theorem integral_condStat_smul_eq {Θ' 𝓧' 𝓣' : Type*}
    [MeasurableSpace 𝓧'] [MeasurableSpace 𝓣'] {P : Θ' → Measure 𝓧'} {T : 𝓧' → 𝓣'}
    {φ : 𝓧' → ℝ} {Q : Kernel 𝓣' 𝓧'} [IsMarkovKernel Q] (hTmeas : Measurable T)
    (hφmeas : Measurable φ) (hφb : ∀ x, |φ x| ≤ 1) {θ : Θ'} [IsProbabilityMeasure (P θ)]
    (hker : (P θ).map (fun x => (T x, x)) = statLaw P T θ ⊗ₘ Q)
    {w : 𝓣' → ℝ} (hw : Measurable w) {C : ℝ} (hwb : ∀ t, |w t| ≤ C) :
    ∫ t, w t * (∫ x, φ x ∂(Q t)) ∂(statLaw P T θ) = ∫ x, w (T x) * φ x ∂(P θ) := by
  haveI : IsProbabilityMeasure (statLaw P T θ) := by
    rw [statLaw]; exact Measure.isProbabilityMeasure_map hTmeas.aemeasurable
  have hFmeas : Measurable (fun p : 𝓣' × 𝓧' => w p.1 * φ p.2) :=
    (hw.comp measurable_fst).mul (hφmeas.comp measurable_snd)
  have hFbound : ∀ p : 𝓣' × 𝓧', ‖w p.1 * φ p.2‖ ≤ C := by
    intro p
    have hc : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hwb p.1)
    calc ‖w p.1 * φ p.2‖ = |w p.1| * |φ p.2| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ C * 1 := mul_le_mul (hwb p.1) (hφb p.2) (abs_nonneg _) hc
      _ = C := mul_one C
  have hFint : Integrable (fun p : 𝓣' × 𝓧' => w p.1 * φ p.2) (statLaw P T θ ⊗ₘ Q) :=
    (integrable_const C).mono' hFmeas.aestronglyMeasurable (ae_of_all _ hFbound)
  have hcompProd : ∫ p, w p.1 * φ p.2 ∂(statLaw P T θ ⊗ₘ Q)
      = ∫ t, w t * (∫ x, φ x ∂(Q t)) ∂(statLaw P T θ) := by
    rw [Measure.integral_compProd hFint]
    exact integral_congr_ae (ae_of_all _ (fun t => (integral_const_mul (w t) φ)))
  rw [← hcompProd, ← hker]
  exact integral_map (hTmeas.prodMk measurable_id).aemeasurable hFmeas.aestronglyMeasurable

/-- **Power-matching:** the law-of-statistic power of `E[φ|T]` equals the raw power of `φ`. -/
private theorem power_condStat_eq {Θ' 𝓧' 𝓣' : Type*}
    [MeasurableSpace 𝓧'] [MeasurableSpace 𝓣'] {P : Θ' → Measure 𝓧'} {T : 𝓧' → 𝓣'}
    {φ : 𝓧' → ℝ} {Q : Kernel 𝓣' 𝓧'} [IsMarkovKernel Q] (hTmeas : Measurable T)
    (hφmeas : Measurable φ) (hφb : ∀ x, |φ x| ≤ 1) {θ : Θ'} [IsProbabilityMeasure (P θ)]
    (hker : (P θ).map (fun x => (T x, x)) = statLaw P T θ ⊗ₘ Q) :
    power (statLaw P T) (fun t => ∫ x, φ x ∂(Q t)) θ = power P φ θ := by
  have h := integral_condStat_smul_eq hTmeas hφmeas hφb hker
    (w := fun _ => (1 : ℝ)) measurable_const (C := 1) (fun _ => by norm_num)
  simpa [power, one_mul] using h

/-- A *single* measurable representative of `t ↦ g • t`, valid a.e. under **every** member of
the family — what is needed to feed the bounded, measurable function `ψ ∘ (g • ·) − ψ` to
bounded completeness.

**Signature amendment (documented deviation).** The frozen statement carried only
`[MulAction G' 𝓣']`; from an invariance hypothesis on the reduced model one derives that
`g • ·` is a.e. measurable under each `statLaw P T θ` *separately*, which is not enough to
pick one common measurable representative — and with a genuinely non-measurable action the
existence statement is simply false. The source's exceptional-set convention presumes `G`
acts by *measurable* transformations of the statistic space, so the measurability of each
`t ↦ g • t` (the content of `[MeasurableSMul G' 𝓣']`, stated as a plain hypothesis so that
no `MeasurableSpace G'` structure has to be imposed) is added. Under it the lemma is
immediate: take `m = (g • ·)`. -/
private theorem exists_measurable_aeEq_smul_statLaw {G' Θ' 𝓧' 𝓣' : Type*} [Group G']
    [MeasurableSpace 𝓧'] [MeasurableSpace 𝓣'] [MulAction G' 𝓣']
    (P : Θ' → Measure 𝓧') (T : 𝓧' → 𝓣') (g : G')
    -- USER-INPUT (amendment): `G'` acts on the statistic space by measurable maps
    (hg : Measurable fun t : 𝓣' => g • t) :
    ∃ m : 𝓣' → 𝓣', Measurable m ∧ ∀ θ, (fun t => g • t) =ᵐ[statLaw P T θ] m :=
  ⟨fun t => g • t, hg, fun _ => Filter.EventuallyEq.rfl⟩

/-- From the invariance of the law-of-statistic model, `g • ·` is a.e. measurable whenever the
translated law is nonzero. -/
private theorem aemeasurable_smul_of_invModel {G' Θ' 𝓣' : Type*} [Group G']
    [MeasurableSpace 𝓣'] [MulAction G' 𝓣'] [MulAction G' Θ'] {Q : Θ' → Measure 𝓣'}
    (hQ : IsInvariantModel (G := G') Q) (g : G') (θ : Θ') (h0 : Q (g • θ) ≠ 0) :
    AEMeasurable (fun t => g • t) (Q θ) := by
  by_contra h
  have hmap := hQ g θ
  rw [Measure.map_of_not_aemeasurable h] at hmap
  exact h0 hmap.symm

/-- The law-of-statistic model inherits invariance from an invariant raw model with an
intertwining statistic. -/
private theorem isInvariantModel_statLaw {G' Θ' 𝓧' 𝓣' : Type*} [Group G']
    [MeasurableSpace 𝓧'] [MeasurableSpace 𝓣'] [MulAction G' 𝓧'] [MulAction G' 𝓣']
    [MulAction G' Θ'] {P : Θ' → Measure 𝓧'} {T : 𝓧' → 𝓣'} [∀ θ, IsProbabilityMeasure (P θ)]
    (hTmeas : Measurable T) (hP : IsInvariantModel (G := G') P)
    (hsmul : ∀ g : G', Measurable fun t : 𝓣' => g • t)
    (hTcompat : ∀ (g : G') (x : 𝓧'), T (g • x) = g • T x) :
    IsInvariantModel (G := G') (statLaw P T) := by
  intro g θ
  obtain ⟨mm, hmm_meas, hmm_ae⟩ := exists_measurable_aeEq_smul_statLaw P T g (hsmul g)
  have haeX : AEMeasurable (fun x => g • x) (P θ) :=
    aemeasurable_smul_of_invModel hP g θ (IsProbabilityMeasure.ne_zero _)
  have haeT : AEMeasurable (fun t => g • t) (statLaw P T θ) :=
    hmm_meas.aemeasurable.congr (hmm_ae θ).symm
  have lhs : (statLaw P T θ).map (fun t => g • t) = (P θ).map (fun x => g • T x) := by
    rw [statLaw, AEMeasurable.map_map_of_aemeasurable haeT hTmeas.aemeasurable]; rfl
  have rhs : statLaw P T (g • θ) = (P θ).map (fun x => g • T x) := by
    rw [statLaw, ← hP g θ, AEMeasurable.map_map_of_aemeasurable hTmeas.aemeasurable haeX]
    exact Measure.map_congr (ae_of_all _ (fun x => hTcompat g x))
  rw [lhs, rhs]

/-- **Set-integral pull-out identity for the sufficiency kernel** (`w = 1_B`). -/
private theorem setIntegral_condStat_eq {Θ' 𝓧' 𝓣' : Type*}
    [MeasurableSpace 𝓧'] [MeasurableSpace 𝓣'] {P : Θ' → Measure 𝓧'} {T : 𝓧' → 𝓣'}
    {φ : 𝓧' → ℝ} {Q : Kernel 𝓣' 𝓧'} [IsMarkovKernel Q] (hTmeas : Measurable T)
    (hφmeas : Measurable φ) (hφb : ∀ x, |φ x| ≤ 1) {θ : Θ'} [IsProbabilityMeasure (P θ)]
    (hker : (P θ).map (fun x => (T x, x)) = statLaw P T θ ⊗ₘ Q)
    {B : Set 𝓣'} (hB : MeasurableSet B) :
    ∫ t in B, (∫ x, φ x ∂(Q t)) ∂(statLaw P T θ) = ∫ x in T ⁻¹' B, φ x ∂(P θ) := by
  have hw : Measurable (B.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hB
  have hwb : ∀ t, |B.indicator (fun _ => (1 : ℝ)) t| ≤ 1 := by
    intro t; by_cases h : t ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have h := integral_condStat_smul_eq hTmeas hφmeas hφb hker hw (C := 1) hwb
  have hLid : ∀ t, B.indicator (fun t => ∫ x, φ x ∂(Q t)) t
      = B.indicator (fun _ => (1 : ℝ)) t * (∫ x, φ x ∂(Q t)) := by
    intro t; by_cases h : t ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hRid : ∀ x, (T ⁻¹' B).indicator φ x = B.indicator (fun _ => (1 : ℝ)) (T x) * φ x := by
    intro x; by_cases h : T x ∈ B <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_preimage, h]
  rw [← integral_indicator hB, ← integral_indicator (hB.preimage hTmeas),
    integral_congr_ae (ae_of_all _ hLid), integral_congr_ae (ae_of_all _ hRid)]
  exact h

/-- **Equivariant set-integral pull-out.** For an invariant test `φ` of the raw data and an
intertwining statistic, the set-integral of the *shifted* conditional expectation
`t ↦ E[φ|T](g • t)` over a measurable set equals the raw integral of `φ` over the preimage —
the same value the unshifted conditional expectation gives. This is the analytic core making
`E[φ|T]` almost invariant. -/
private theorem setIntegral_condStat_smul_eq {G' Θ' 𝓧' 𝓣' : Type*} [Group G']
    [MeasurableSpace 𝓧'] [MeasurableSpace 𝓣'] [MulAction G' 𝓧'] [MulAction G' 𝓣']
    [MulAction G' Θ'] {P : Θ' → Measure 𝓧'} {T : 𝓧' → 𝓣'} {φ : 𝓧' → ℝ}
    {Q : Kernel 𝓣' 𝓧'} [IsMarkovKernel Q] [∀ θ, IsProbabilityMeasure (P θ)]
    (hTmeas : Measurable T) (hφmeas : Measurable φ) (hφIcc : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1)
    (hP : IsInvariantModel (G := G') P)
    (hsmul : ∀ g : G', Measurable fun t : 𝓣' => g • t)
    (hTcompat : ∀ (g : G') (x : 𝓧'), T (g • x) = g • T x)
    (hφinv : ∀ (g : G') (x : 𝓧'), φ (g • x) = φ x)
    (hker : ∀ θ, (P θ).map (fun x => (T x, x)) = statLaw P T θ ⊗ₘ Q)
    (g : G') (θ : Θ') {B : Set 𝓣'} (hB : MeasurableSet B) :
    ∫ t in B, (∫ x, φ x ∂(Q (g • t))) ∂(statLaw P T θ) = ∫ x in T ⁻¹' B, φ x ∂(P θ) := by
  classical
  haveI hprob : ∀ θ', IsProbabilityMeasure (statLaw P T θ') := fun θ' =>
    Measure.isProbabilityMeasure_map hTmeas.aemeasurable
  have hφb : ∀ x, |φ x| ≤ 1 := fun x => by
    rw [abs_le]; exact ⟨by linarith [(hφIcc x).1], (hφIcc x).2⟩
  have hstat : IsInvariantModel (G := G') (statLaw P T) :=
    isInvariantModel_statLaw hTmeas hP hsmul hTcompat
  obtain ⟨m, hm_meas, hm_ae⟩ := exists_measurable_aeEq_smul_statLaw P T g (hsmul g)
  obtain ⟨m', hm'_meas, hm'_ae⟩ := exists_measurable_aeEq_smul_statLaw P T g⁻¹ (hsmul g⁻¹)
  set ind : 𝓣' → ℝ := B.indicator (fun _ => 1) with hinddef
  have hind_meas : Measurable ind := measurable_const.indicator hB
  set ψ : 𝓣' → ℝ := fun t => ∫ x, φ x ∂(Q t) with hψdef
  have hψ_meas : Measurable ψ := measurable_condStat Q hφmeas
  have haeT : AEMeasurable (fun t => g • t) (statLaw P T θ) :=
    hm_meas.aemeasurable.congr (hm_ae θ).symm
  have haeTinv : AEMeasurable (fun s => g⁻¹ • s) (statLaw P T (g • θ)) :=
    hm'_meas.aemeasurable.congr (hm'_ae (g • θ)).symm
  have haeX : AEMeasurable (fun x => g • x) (P θ) :=
    aemeasurable_smul_of_invModel hP g θ (IsProbabilityMeasure.ne_zero _)
  set wt : 𝓣' → ℝ := fun s => ind (m' s) with hwtdef
  have hwt_meas : Measurable wt := hind_meas.comp hm'_meas
  have hwt_b : ∀ s, |wt s| ≤ 1 := fun s => by
    rw [hwtdef]; by_cases h : m' s ∈ B <;>
      simp [hinddef, Set.indicator_of_mem, Set.indicator_of_notMem, h]
  change ∫ t in B, ψ (g • t) ∂(statLaw P T θ) = ∫ x in T ⁻¹' B, φ x ∂(P θ)
  have hFaesm : AEStronglyMeasurable (fun s => ind (g⁻¹ • s) * ψ s)
      (statLaw P T (g • θ)) :=
    ((hind_meas.comp_aemeasurable haeTinv).mul hψ_meas.aemeasurable).aestronglyMeasurable
  have hFaesm2 : AEStronglyMeasurable (fun y => ind (g⁻¹ • T y) * φ y) (P (g • θ)) :=
    ((hind_meas.comp_aemeasurable
      (haeTinv.comp_aemeasurable hTmeas.aemeasurable)).mul
        hφmeas.aemeasurable).aestronglyMeasurable
  calc ∫ t in B, ψ (g • t) ∂(statLaw P T θ)
      = ∫ t, ind t * ψ (g • t) ∂(statLaw P T θ) := by
        rw [← integral_indicator hB]
        refine integral_congr_ae (ae_of_all _ (fun t => ?_))
        by_cases h : t ∈ B <;>
          simp [hinddef, Set.indicator_of_mem, Set.indicator_of_notMem, h]
    _ = ∫ s, ind (g⁻¹ • s) * ψ s ∂(statLaw P T (g • θ)) := by
        rw [← hstat g θ] at hFaesm ⊢
        rw [integral_map haeT hFaesm]
        refine integral_congr_ae (ae_of_all _ (fun t => ?_))
        simp only [inv_smul_smul]
    _ = ∫ s, wt s * ψ s ∂(statLaw P T (g • θ)) := by
        refine integral_congr_ae ?_
        filter_upwards [hm'_ae (g • θ)] with s hs
        simp only [hwtdef]; rw [show g⁻¹ • s = m' s from hs]
    _ = ∫ y, wt (T y) * φ y ∂(P (g • θ)) :=
        integral_condStat_smul_eq hTmeas hφmeas hφb (hker (g • θ)) hwt_meas (C := 1) hwt_b
    _ = ∫ y, ind (g⁻¹ • T y) * φ y ∂(P (g • θ)) := by
        refine integral_congr_ae ?_
        have hcomp := ae_eq_comp hTmeas.aemeasurable (hm'_ae (g • θ))
        filter_upwards [hcomp] with y hy
        simp only [hwtdef, Function.comp_apply] at hy ⊢
        rw [hy]
    _ = ∫ x, ind (g⁻¹ • T (g • x)) * φ (g • x) ∂(P θ) := by
        rw [← hP g θ] at hFaesm2 ⊢
        rw [integral_map haeX hFaesm2]
    _ = ∫ x, ind (T x) * φ x ∂(P θ) := by
        refine integral_congr_ae (ae_of_all _ (fun x => ?_))
        simp only [hTcompat, inv_smul_smul, hφinv]
    _ = ∫ x in T ⁻¹' B, φ x ∂(P θ) := by
        rw [← integral_indicator (hB.preimage hTmeas)]
        refine integral_congr_ae (ae_of_all _ (fun x => ?_))
        by_cases h : T x ∈ B <;>
          simp [hinddef, Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_preimage, h]

variable {G Θ 𝓧 𝓣 𝓥 : Type*} [Group G] [MeasurableSpace 𝓧] [MeasurableSpace 𝓣]

/-! ## Power invariance versus almost invariance -/

/-- **Invariant power function ⟺ almost invariant test**, for a boundedly complete family
of laws of the statistic. One direction is unconditional; the converse is exactly where
bounded completeness is used. -/
theorem power_invariant_iff_almostInvariant [MulAction G 𝓣] [MulAction G Θ]
    {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → 𝓣} {ψ : 𝓣 → ℝ}
    -- USER-INPUT: the family of laws of `T` is boundedly complete
    (hbc : IsBoundedlyCompleteStat P T)
    -- USER-INPUT: the reduced problem is invariant under the action on the statistic space
    (hQ : IsInvariantModel (G := G) (statLaw P T))
    -- USER-INPUT (amendment, see `exists_measurable_aeEq_smul_statLaw`): `G` acts on the
    -- statistic space by measurable maps
    (hsmul : ∀ g : G, Measurable fun t : 𝓣 => g • t)
    -- USER-INPUT: `ψ` is a critical function on the statistic space
    (hψ : IsCriticalFn ψ) :
    (∀ (g : G) (θ : Θ), power (statLaw P T) ψ (g • θ) = power (statLaw P T) ψ θ) ↔
      ∀ θ, IsAlmostInvariant G (statLaw P T θ) ψ := by
  refine ⟨fun hpow θ g => ?_, fun hai g θ => ?_⟩
  · -- Forward: power invariance ⟹ almost invariance (bounded completeness).
    obtain ⟨m, hm_meas, hm_ae⟩ := exists_measurable_aeEq_smul_statLaw P T g (hsmul g)
    have hfmeas : Measurable (fun t => ψ (m t) - ψ t) := (hψ.1.comp hm_meas).sub hψ.1
    have hbound : ∀ s, |ψ (m s) - ψ s| ≤ 2 := by
      intro s; have h1 := hψ.2 (m s); have h2 := hψ.2 s
      rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
    have hfint : ∀ θ', ∫ t, (ψ (m t) - ψ t) ∂(statLaw P T θ') = 0 := by
      intro θ'
      haveI : IsFiniteMeasure (statLaw P T θ') := Measure.isFiniteMeasure_map (P θ') T
      have haem : AEMeasurable (fun t => g • t) (statLaw P T θ') :=
        hm_meas.aemeasurable.congr (hm_ae θ').symm
      have hInt1 : Integrable (fun t => ψ (m t)) (statLaw P T θ') :=
        (integrable_const (1 : ℝ)).mono' (hψ.1.comp hm_meas).aestronglyMeasurable
          (ae_of_all _ (fun s => by
            rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hψ.2 (m s)).1], (hψ.2 (m s)).2⟩))
      have hInt2 : Integrable (fun t => ψ t) (statLaw P T θ') :=
        (integrable_const (1 : ℝ)).mono' hψ.1.aestronglyMeasurable
          (ae_of_all _ (fun s => by
            rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hψ.2 s).1], (hψ.2 s).2⟩))
      rw [integral_sub hInt1 hInt2]
      have ea : (fun t => ψ (m t)) =ᵐ[statLaw P T θ'] (fun t => ψ (g • t)) := by
        filter_upwards [hm_ae θ'] with t ht using by rw [ht]
      have eb : ∫ t, ψ (g • t) ∂(statLaw P T θ') = ∫ t, ψ t ∂(statLaw P T (g • θ')) := by
        rw [← hQ g θ', integral_map haem hψ.1.aestronglyMeasurable]
      have ec : ∫ t, ψ t ∂(statLaw P T (g • θ')) = ∫ t, ψ t ∂(statLaw P T θ') := by
        simpa only [power] using hpow g θ'
      rw [integral_congr_ae ea, eb, ec, sub_self]
    have hzero : (fun t => ψ (m t) - ψ t) =ᵐ[statLaw P T θ] 0 :=
      hbc (fun t => ψ (m t) - ψ t) hfmeas ⟨2, hbound⟩ hfint θ
    filter_upwards [hzero, hm_ae θ] with t ht hmt
    simp only [Pi.zero_apply] at ht
    rw [hmt]; linarith [ht]
  · -- Reverse: almost invariance ⟹ power invariance (change of variables).
    obtain ⟨m, hm_meas, hm_ae⟩ := exists_measurable_aeEq_smul_statLaw P T g (hsmul g)
    have haem : AEMeasurable (fun t => g • t) (statLaw P T θ) :=
      hm_meas.aemeasurable.congr (hm_ae θ).symm
    simp only [power]
    rw [← hQ g θ, integral_map haem hψ.1.aestronglyMeasurable]
    exact integral_congr_ae (hai θ g)

/-- **A UMP almost invariant test based on a sufficient statistic is UMP in the class of
all tests whose power depends only on a maximal invariant of the parameter.** -/
theorem isUMP_of_isUMPAlmostInvariant_sufficient [MulAction G 𝓣] [MulAction G Θ]
    {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → 𝓣} {v : Θ → 𝓥}
    {Θ₀ Θ₁ : Set Θ} {α : ℝ} {ψ₀ : 𝓣 → ℝ}
    -- USER-INPUT: `T` is sufficient for the model
    (hsuf : HasSufficientKernel P T)
    -- LEAN-ONLY: measurability of the statistic, needed to transport tests and laws
    (hTmeas : Measurable T)
    -- USER-INPUT: the family of laws of `T` is boundedly complete
    (hbc : IsBoundedlyCompleteStat P T)
    -- USER-INPUT: the reduced problem is invariant under the action on the statistic space
    (hQ : IsInvariantModel (G := G) (statLaw P T))
    -- USER-INPUT (amendment, see `exists_measurable_aeEq_smul_statLaw`): `G` acts on the
    -- statistic space by measurable maps
    (hsmul : ∀ g : G, Measurable fun t : 𝓣 => g • t)
    -- USER-INPUT: `v` is invariant under the induced parameter action
    (hv_inv : ∀ (g : G) (θ : Θ), v (g • θ) = v θ)
    -- USER-INPUT: `v` separates the induced orbits (maximal invariance of `v`)
    (hv_max : ∀ θ θ' : Θ, v θ = v θ' → ∃ g : G, θ' = g • θ)
    -- USER-INPUT: `ψ₀` is UMP among almost invariant level-`α` tests of the statistic
    (hψ₀ : IsUMPAlmostInvariant G (statLaw P T) Θ₀ Θ₁ α ψ₀) :
    IsCriticalFn (fun x => ψ₀ (T x)) ∧
      ∀ φ : 𝓧 → ℝ, IsCriticalFn φ → IsLevel P Θ₀ φ α →
        (∀ θ θ' : Θ, v θ = v θ' → power P φ θ = power P φ θ') →
        ∀ θ ∈ Θ₁, power P φ θ ≤ power P (fun x => ψ₀ (T x)) θ := by
  obtain ⟨Q, hQmark, hker⟩ := hsuf
  haveI := hQmark
  refine ⟨⟨hψ₀.1.1.comp hTmeas, fun x => hψ₀.1.2 (T x)⟩, ?_⟩
  intro φ hφcrit hφlevel hφv θ hθ
  have hφabs : ∀ x, |φ x| ≤ 1 := fun x => by
    rw [abs_le]; exact ⟨by linarith [(hφcrit.2 x).1], (hφcrit.2 x).2⟩
  have hψφcrit : IsCriticalFn (fun t => ∫ x, φ x ∂(Q t)) :=
    ⟨measurable_condStat Q hφcrit.1, condStat_mem_Icc Q hφcrit.2⟩
  have hmatch : ∀ θ', power (statLaw P T) (fun t => ∫ x, φ x ∂(Q t)) θ' = power P φ θ' :=
    fun θ' => power_condStat_eq hTmeas hφcrit.1 hφabs (hker θ')
  have hpowinv : ∀ (g : G) (θ' : Θ),
      power (statLaw P T) (fun t => ∫ x, φ x ∂(Q t)) (g • θ')
        = power (statLaw P T) (fun t => ∫ x, φ x ∂(Q t)) θ' := by
    intro g θ'
    rw [hmatch (g • θ'), hmatch θ', hφv (g • θ') θ' (hv_inv g θ')]
  have hai : ∀ θ', IsAlmostInvariant G (statLaw P T θ') (fun t => ∫ x, φ x ∂(Q t)) :=
    (power_invariant_iff_almostInvariant hbc hQ hsmul hψφcrit).mp hpowinv
  have hlevel : IsLevel (statLaw P T) Θ₀ (fun t => ∫ x, φ x ∂(Q t)) α := by
    intro θ' hθ'; rw [hmatch θ']; exact hφlevel θ' hθ'
  have hdom := hψ₀.2.2.2 (fun t => ∫ x, φ x ∂(Q t)) hψφcrit hai hlevel θ hθ
  have hmapψ₀ : power (statLaw P T) ψ₀ θ = power P (fun x => ψ₀ (T x)) θ := by
    simp only [power, statLaw]
    rw [integral_map hTmeas.aemeasurable hψ₀.1.1.aestronglyMeasurable]
  rw [← hmatch θ, ← hmapψ₀]
  exact hdom

/-! ## Legitimacy of reducing by sufficiency before invariance -/

section Legitimacy

variable [MulAction G 𝓧] [MulAction G 𝓣] [MulAction G Θ] {P : Θ → Measure 𝓧} {T : 𝓧 → 𝓣}

/-- **(i)** Every invariant test of the raw data is matched in power by an almost
invariant test based on the sufficient statistic. -/
theorem exists_almostInvariant_on_stat_of_invariant [∀ θ, IsProbabilityMeasure (P θ)]
    {φ : 𝓧 → ℝ}
    -- USER-INPUT: `T` is sufficient for the model
    (hsuf : HasSufficientKernel P T)
    -- LEAN-ONLY: measurability of the statistic
    (hTmeas : Measurable T)
    -- USER-INPUT: the model is invariant under the sample-space action
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT (amendment, see `exists_measurable_aeEq_smul_statLaw`): `G` acts on the
    -- statistic space by measurable maps
    (hsmul : ∀ g : G, Measurable fun t : 𝓣 => g • t)
    -- USER-INPUT: the statistic intertwines the two actions, `T (g·x) = g·(T x)`;
    -- this is the source's compatibility condition together with the definition of the
    -- induced group on the statistic space
    (hTcompat : ∀ (g : G) (x : 𝓧), T (g • x) = g • T x)
    -- USER-INPUT: `φ` is an invariant critical function of the raw data
    (hφ : IsCriticalFn φ) (hφinv : IsInvariantTest G φ) :
    ∃ ψ : 𝓣 → ℝ, IsCriticalFn ψ ∧ (∀ θ, IsAlmostInvariant G (statLaw P T θ) ψ) ∧
      ∀ θ, power (statLaw P T) ψ θ = power P φ θ := by
  obtain ⟨Q, hQmark, hker⟩ := hsuf
  haveI := hQmark
  have hφabs : ∀ x, |φ x| ≤ 1 := fun x => by
    rw [abs_le]; exact ⟨by linarith [(hφ.2 x).1], (hφ.2 x).2⟩
  refine ⟨fun t => ∫ x, φ x ∂(Q t),
    ⟨measurable_condStat Q hφ.1, condStat_mem_Icc Q hφ.2⟩, ?_, ?_⟩
  · -- Almost invariance of `E[φ|T]`, via the equivariant set-integral pull-out.
    intro θ g
    haveI : IsProbabilityMeasure (statLaw P T θ) :=
      Measure.isProbabilityMeasure_map hTmeas.aemeasurable
    have hψ_meas := measurable_condStat Q hφ.1
    have haeT : AEMeasurable (fun t => g • t) (statLaw P T θ) := by
      obtain ⟨m, hm_meas, hm_ae⟩ := exists_measurable_aeEq_smul_statLaw P T g (hsmul g)
      exact hm_meas.aemeasurable.congr (hm_ae θ).symm
    have hInt1 : Integrable (fun t => (∫ x, φ x ∂(Q (g • t)))) (statLaw P T θ) :=
      (integrable_const (1 : ℝ)).mono' (hψ_meas.comp_aemeasurable haeT).aestronglyMeasurable
        (ae_of_all _ (fun t => by
          have := condStat_mem_Icc Q hφ.2 (g • t)
          rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [this.1], this.2⟩))
    have hInt2 : Integrable (fun t => (∫ x, φ x ∂(Q t))) (statLaw P T θ) :=
      (integrable_const (1 : ℝ)).mono' hψ_meas.aestronglyMeasurable
        (ae_of_all _ (fun t => by
          have := condStat_mem_Icc Q hφ.2 t
          rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [this.1], this.2⟩))
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s _ _ => hInt1.integrableOn) (fun s _ _ => hInt2.integrableOn) (fun B hB _ => ?_)
    rw [setIntegral_condStat_smul_eq hTmeas hφ.1 hφ.2 hP hsmul hTcompat hφinv hker g θ hB,
      setIntegral_condStat_eq hTmeas hφ.1 hφabs (hker θ) hB]
  · -- Power matching.
    intro θ
    exact power_condStat_eq hTmeas hφ.1 hφabs (hker θ)

/-- **(ii)** Under the structural conditions making almost invariance equivalent to
invariance on the statistic space, the matching test of part (i) can be taken invariant. -/
theorem exists_invariant_on_stat_of_invariant [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSMul₂ G 𝓣] [∀ θ, IsProbabilityMeasure (P θ)] {ν : Measure G} [SigmaFinite ν]
    {μT : Measure 𝓣} [SigmaFinite μT] {φ : 𝓧 → ℝ}
    -- USER-INPUT: `T` is sufficient for the model
    (hsuf : HasSufficientKernel P T)
    -- LEAN-ONLY: measurability of the statistic
    (hTmeas : Measurable T)
    -- USER-INPUT: the model is invariant under the sample-space action
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: the statistic intertwines the two actions
    (hTcompat : ∀ (g : G) (x : 𝓧), T (g • x) = g • T x)
    -- USER-INPUT: the group carries a nonzero σ-finite measure with right-translation
    -- stable null sets
    (hν0 : ν ≠ 0)
    (hν : ∀ (g : G) (B : Set G), MeasurableSet B → ν B = 0 →
      ν ((fun y => y * g⁻¹) ⁻¹' B) = 0)
    -- USER-INPUT: `μT` is a σ-finite measure equivalent to the family of laws of `T`
    (hdom : ∀ θ, statLaw P T θ ≪ μT)
    (hequiv : ∀ B : Set 𝓣, MeasurableSet B → (∀ θ, statLaw P T θ B = 0) → μT B = 0)
    -- USER-INPUT: `φ` is an invariant critical function of the raw data
    (hφ : IsCriticalFn φ) (hφinv : IsInvariantTest G φ) :
    ∃ ψ : 𝓣 → ℝ, IsCriticalFn ψ ∧ IsInvariantTest G ψ ∧
      ∀ θ, power (statLaw P T) ψ θ = power P φ θ := by
  obtain ⟨ψ, hψcrit, hψai, hψpow⟩ :=
    exists_almostInvariant_on_stat_of_invariant hsuf hTmeas hP
      (fun g => measurable_const.smul measurable_id) hTcompat hφ hφinv
  -- Almost invariance w.r.t. the dominating measure `μT`.
  have hμTai : IsAlmostInvariant G μT ψ := by
    intro g
    have hgs : Measurable (fun t : 𝓣 => g • t) := measurable_const.smul measurable_id
    have hNmeas : MeasurableSet {t : 𝓣 | ψ (g • t) = ψ t}ᶜ := by
      have hset : {t : 𝓣 | ψ (g • t) = ψ t} = (fun t => ψ (g • t) - ψ t) ⁻¹' {0} := by
        ext t; simp [sub_eq_zero]
      rw [hset]
      exact (((hψcrit.1.comp hgs).sub hψcrit.1) (measurableSet_singleton 0)).compl
    rw [ae_iff]
    refine hequiv _ hNmeas (fun θ => ?_)
    have h := hψai θ g
    rwa [ae_iff] at h
  -- Upgrade to a genuinely invariant (measurable) version, then clamp to `[0,1]`.
  obtain ⟨ψ', hψ'meas, hψ'inv, hψ'ae⟩ :=
    exists_invariant_ae_eq_of_almostInvariant hν0 hν hψcrit.1 hμTai
  refine ⟨fun t => max 0 (min 1 (ψ' t)),
    ⟨measurable_const.max (measurable_const.min hψ'meas),
      fun t => ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩,
    fun g t => by simp only [hψ'inv g t], ?_⟩
  -- Power matching survives the clamp, since `ψ = clamp ψ'` a.e. `μT` hence a.e. each law.
  have hψeq : ψ =ᵐ[μT] (fun t => max 0 (min 1 (ψ' t))) := by
    filter_upwards [hψ'ae] with t ht
    have hb := hψcrit.2 t
    rw [← ht, min_eq_right hb.2, max_eq_right hb.1]
  intro θ
  have haestat : ψ =ᵐ[statLaw P T θ] (fun t => max 0 (min 1 (ψ' t))) :=
    hψeq.filter_mono (hdom θ).ae_le
  have : power (statLaw P T) (fun t => max 0 (min 1 (ψ' t))) θ = power (statLaw P T) ψ θ := by
    simp only [power]; exact integral_congr_ae haestat.symm
  rw [this]; exact hψpow θ

/-- **(iii)** A test UMP among invariant tests of the sufficient statistic is UMP among
all invariant tests of the raw data — the sufficiency-then-invariance reduction is
legitimate. -/
theorem isUMPInvariant_comp_of_isUMPInvariant_stat [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSMul₂ G 𝓣] [∀ θ, IsProbabilityMeasure (P θ)] {ν : Measure G} [SigmaFinite ν]
    {μT : Measure 𝓣} [SigmaFinite μT] {Θ₀ Θ₁ : Set Θ} {α : ℝ} {ψ₀ : 𝓣 → ℝ}
    -- USER-INPUT: `T` is sufficient for the model
    (hsuf : HasSufficientKernel P T)
    -- LEAN-ONLY: measurability of the statistic
    (hTmeas : Measurable T)
    -- USER-INPUT: the model is invariant under the sample-space action
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: the statistic intertwines the two actions
    (hTcompat : ∀ (g : G) (x : 𝓧), T (g • x) = g • T x)
    -- USER-INPUT: the group carries a nonzero σ-finite measure with right-translation
    -- stable null sets
    (hν0 : ν ≠ 0)
    (hν : ∀ (g : G) (B : Set G), MeasurableSet B → ν B = 0 →
      ν ((fun y => y * g⁻¹) ⁻¹' B) = 0)
    -- USER-INPUT: `μT` is a σ-finite measure equivalent to the family of laws of `T`
    (hdom : ∀ θ, statLaw P T θ ≪ μT)
    (hequiv : ∀ B : Set 𝓣, MeasurableSet B → (∀ θ, statLaw P T θ B = 0) → μT B = 0)
    -- USER-INPUT: `ψ₀` is UMP among invariant level-`α` tests of the statistic
    (hψ₀ : IsUMPInvariant G (statLaw P T) Θ₀ Θ₁ α ψ₀) :
    IsUMPInvariant G P Θ₀ Θ₁ α (fun x => ψ₀ (T x)) := by
  have hmapeq : ∀ (χ : 𝓣 → ℝ), Measurable χ → ∀ θ',
      power P (fun x => χ (T x)) θ' = power (statLaw P T) χ θ' := by
    intro χ hχ θ'
    simp only [power, statLaw]
    rw [integral_map hTmeas.aemeasurable hχ.aestronglyMeasurable]
  refine ⟨⟨hψ₀.1.1.comp hTmeas, fun x => hψ₀.1.2 (T x)⟩,
    fun g x => by change ψ₀ (T (g • x)) = ψ₀ (T x); rw [hTcompat g x]; exact hψ₀.2.1 g (T x),
    ?_, ?_⟩
  · -- Level.
    intro θ hθ; rw [hmapeq ψ₀ hψ₀.1.1 θ]; exact hψ₀.2.2.1 θ hθ
  · -- Domination among all invariant tests of the raw data.
    intro χ hχcrit hχinv hχlevel θ hθ
    obtain ⟨ψχ, hψχcrit, hψχinv, hψχpow⟩ :=
      exists_invariant_on_stat_of_invariant hsuf hTmeas hP hTcompat hν0 hν hdom hequiv
        hχcrit hχinv
    have hψχlevel : IsLevel (statLaw P T) Θ₀ ψχ α := by
      intro θ' hθ'; rw [hψχpow θ']; exact hχlevel θ' hθ'
    have hdomψ := hψ₀.2.2.2 ψχ hψχcrit hψχinv hψχlevel θ hθ
    rw [hmapeq ψ₀ hψ₀.1.1 θ, ← hψχpow θ]
    exact hdomψ

end Legitimacy

end StatLean.HypothesisTesting
