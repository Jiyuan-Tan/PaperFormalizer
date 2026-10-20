module
public import StatLean.HypothesisTesting.Invariance.Defs
public import StatLean.HypothesisTesting.NeymanPearson.Lemma

@[expose] public section

/-!
# UMP invariant tests under a finite group with transitive induced action

When a testing problem is invariant under a **finite** group `G` and the induced group on
the parameter space acts **transitively** on the null class and on the alternative class
separately, the invariance reduction collapses a composite-vs-composite problem to a
simple-vs-simple one. The reason is that an invariant test has the same power at every
parameter of an induced orbit, so maximizing power against one alternative maximizes it
against all of them; the Neyman–Pearson lemma applied to the pair of **orbit-averaged**
densities then produces a uniformly most powerful invariant test.

Concretely, with the model dominated by a σ-finite measure and densities `p θ`, the test
rejects for large values of
$$ \frac{|G|^{-1}\sum_{g \in G} p_{\bar g\theta_1}(x)}
        {|G|^{-1}\sum_{g \in G} p_{\bar g\theta_0}(x)} , $$
where `θ₀` and `θ₁` are *any* members of the null and alternative classes — the ratio does
not depend on which representatives are chosen.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 6 (Invariance), §6.3
(Uniformly Most Powerful Invariant Tests), Theorem 6.3.1 (for a finite group with transitive
induced action the orbit-averaged likelihood ratio gives the UMP invariant test) and Theorem
6.3.2 (the law of an invariant statistic depends only on the maximal invariant). (`TSH4 §6.3
Thm 6.3.1, Thm 6.3.2`.)

**Main results.**
* `isInvariantTest_orbitAverage` — the orbit average of any function is invariant;
* `orbitAverage_eq_avg_translated_density` — the orbit average of a density agrees a.e.
  with the average of the densities at the translated parameters, i.e. with the numerator
  and denominator of the displayed ratio, whenever the dominating measure is invariant;
* `isUMPInvariant_of_orbitAverage_ratio` — a Neyman–Pearson test for the orbit-averaged
  densities is UMP invariant at its size;
* `exists_isUMPInvariant_of_finite_transitive` — the existence statement.

**Proof formalization notes.**
* The book states the rejection region through the *parameter-side* average
  `∑ᵢ p_{ḡᵢθ}(x)/N`. The definitional device available here is `orbitAverage`, the
  *sample-side* average `|G|⁻¹ ∑_g p_θ(g·x)`. The two agree a.e. once the dominating
  measure is `G`-invariant (model invariance then reads `p_{ḡθ}(x) = p_θ(g⁻¹·x)` a.e.);
  `orbitAverage_eq_avg_translated_density` records exactly that bridge, so the headline
  theorem is stated on the sample side without any loss of faithfulness.
* Stability of the null and alternative classes under the induced action (`hΘ₀`, `hΘ₁`) is
  *separate* from transitivity and both are demanded: transitivity relates two points of a
  class, stability says the class is not left.
* Invariance of the candidate test is a hypothesis rather than a conclusion because the
  Neyman–Pearson prescription pins the test only off the boundary `{ratio = k}`, where the
  choice is free. `isInvariantTest_orbitAverage` shows that the ratio itself is always
  invariant, so the hypothesis only constrains that free choice.
* The Neyman–Pearson input is used through the declarations of the fundamental lemma
  planned for the sibling `Tests` layer (work item `ht/test-foundations`); the predicates
  `IsMostPowerful` / `IsLevel` / `power` used here all come from `Tests.Defs`.

**Bibliographic comments.** The reduction of an invariant testing problem with a transitive
induced group to a simple-vs-simple problem, and the resulting orbit-averaged likelihood
ratio, belong to the invariance program of G. A. Hunt and C. Stein ("Most stringent tests
of statistical hypotheses," unpublished manuscript, 1946) and C. Stein ("Some problems in
multivariate analysis, Part I," Technical Report 6, Department of Statistics, Stanford
University, 1956), as developed in E. L. Lehmann's lecture tradition of the 1950s. The
underlying optimality criterion is that of J. Neyman and E. S. Pearson ("On the problem of
the most efficient tests of statistical hypotheses," *Phil. Trans. R. Soc. A* **231**
(1933), 289–337).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation (IsInvariantModel)

variable {G Θ 𝓧 : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace 𝓧]
  [MulAction G 𝓧] [MulAction G Θ]

/-! ### Change-of-variables helpers under an invariant dominating measure -/

/-- Pushing a `withDensity` forward along a `G`-invariant group action re-indexes the
density by `g⁻¹`. This is the density-level reading of `μ.map (g • ·) = μ`. -/
private theorem map_smul_withDensity [MeasurableSMul G 𝓧] {μ : Measure 𝓧} (g : G)
    {f : 𝓧 → ℝ≥0∞} (hf : Measurable f) (hμ : μ.map (fun x => g • x) = μ) :
    (μ.withDensity f).map (fun x => g • x) = μ.withDensity (fun x => f (g⁻¹ • x)) := by
  have hgm : Measurable (fun x : 𝓧 => g • x) := measurable_const_smul g
  have hFm : Measurable (fun x : 𝓧 => f (g⁻¹ • x)) := hf.comp (measurable_const_smul g⁻¹)
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hgm hA, withDensity_apply _ (hgm hA), withDensity_apply _ hA,
    ← lintegral_indicator (hgm hA), ← lintegral_indicator hA]
  conv_rhs => rw [← hμ, lintegral_map (hFm.indicator hA) hgm]
  refine lintegral_congr fun a => ?_
  by_cases h : g • a ∈ A
  · rw [Set.indicator_of_mem (Set.mem_preimage.mpr h) f,
      Set.indicator_of_mem h (fun x => f (g⁻¹ • x)), inv_smul_smul]
  · rw [Set.indicator_of_notMem (by rwa [Set.mem_preimage]) f,
      Set.indicator_of_notMem h (fun x => f (g⁻¹ • x))]

/-- For a nonnegative real `a`, `ofReal` turns multiplication by any real into a product. -/
private theorem ofReal_mul_nonneg {k a : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal k * ENNReal.ofReal a = ENNReal.ofReal (k * a) := by
  rcases le_or_gt 0 k with hk | hk
  · exact (ENNReal.ofReal_mul hk).symm
  · rw [ENNReal.ofReal_eq_zero.mpr hk.le, zero_mul,
      ENNReal.ofReal_eq_zero.mpr (by nlinarith [mul_nonneg (neg_nonneg.mpr hk.le) ha])]

/-- Strictness transfers back across `ofReal`. -/
private theorem ofReal_lt_of_ofReal_lt {a b : ℝ}
    (h : ENNReal.ofReal a < ENNReal.ofReal b) : a < b := by
  by_contra hc
  exact absurd (ENNReal.ofReal_le_ofReal (not_lt.mp hc)) (not_le.mpr h)

/-- Change of variables for a real integral under a `G`-invariant dominating measure. -/
private theorem integral_smul_invariant [MeasurableSMul G 𝓧] {μ : Measure 𝓧} (g : G)
    {F : 𝓧 → ℝ} (hF : Measurable F) (hμ : μ.map (fun x => g • x) = μ) :
    ∫ x, F (g • x) ∂μ = ∫ x, F x ∂μ := by
  conv_rhs => rw [← hμ]
  rw [integral_map (measurable_const_smul g).aemeasurable hF.aestronglyMeasurable]

/-- The integral of a test against a real density equals the integral of the product. -/
private theorem power_withDensity_eq {μ : Measure 𝓧} {q : 𝓧 → ℝ} (hqm : Measurable q)
    (hqnn : ∀ x, 0 ≤ q x) (ψ : 𝓧 → ℝ) :
    ∫ x, ψ x ∂(μ.withDensity fun x => ENNReal.ofReal (q x)) = ∫ x, ψ x * q x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hqm.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hqnn x)]; ring

/-- The orbit average integrates to the same value as the original density. -/
private theorem integral_orbitAverage_eq [Fintype G] [MeasurableSMul G 𝓧] {μ : Measure 𝓧}
    {q : 𝓧 → ℝ} (hqm : Measurable q) (hqi : Integrable q μ)
    (hμ : ∀ g : G, μ.map (fun x => g • x) = μ) :
    ∫ x, orbitAverage G q x ∂μ = ∫ x, q x ∂μ := by
  haveI : Nonempty G := ⟨1⟩
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hint : ∀ g : G, Integrable (fun x => q (g • x)) μ := fun g =>
    (⟨measurable_const_smul g, hμ g⟩ :
      MeasurePreserving _ μ μ).integrable_comp_of_integrable hqi
  have hcov : ∀ g : G, ∫ x, q (g • x) ∂μ = ∫ x, q x ∂μ := fun g =>
    integral_smul_invariant g hqm (hμ g)
  unfold orbitAverage
  rw [integral_const_mul, integral_finset_sum _ (fun g _ => hint g),
    Finset.sum_congr rfl (fun g _ => hcov g), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- **Orbit averages are invariant.** Averaging over a finite group produces a function
constant on orbits, since left translation permutes the group. -/
theorem isInvariantTest_orbitAverage [Fintype G] (f : 𝓧 → ℝ) :
    IsInvariantTest G (orbitAverage G f) := by
  intro g x
  unfold orbitAverage
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight g) (fun b => f (b • x))]
  simp only [Equiv.coe_mulRight, mul_smul]

/-- **Sample-side and parameter-side orbit averages agree.** For a dominated invariant
model whose dominating measure is itself `G`-invariant, the orbit average of the density
at a fixed parameter coincides almost everywhere with the average of the densities at the
translated parameters — the quantity appearing in the classical rejection region. -/
theorem orbitAverage_eq_avg_translated_density [Fintype G] [MeasurableSMul G 𝓧]
    {P : Θ → Measure 𝓧}
    {μ : Measure 𝓧} [SigmaFinite μ] {p : Θ → 𝓧 → ℝ} (θ : Θ)
    -- USER-INPUT: the model intertwines the sample- and parameter-space actions
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: the model is dominated by `μ` with densities `p`
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (p θ x))
    -- USER-INPUT: the densities are measurable and nonnegative
    (hpmeas : ∀ θ, Measurable (p θ)) (hpnonneg : ∀ θ x, 0 ≤ p θ x)
    -- USER-INPUT: the dominating measure is invariant under the group
    (hμ : ∀ g : G, μ.map (g • ·) = μ) :
    orbitAverage G (p θ) =ᵐ[μ] fun x => (Fintype.card G : ℝ)⁻¹ * ∑ g : G, p (g • θ) x := by
  -- Per group element, `p_{gθ}(x) = p_θ(g⁻¹·x)` a.e., from equality of the pushed-forward
  -- densities and `withDensity` uniqueness (σ-finiteness).
  have key : ∀ g : G, (fun x => p (g • θ) x) =ᵐ[μ] fun x => p θ (g⁻¹ • x) := by
    intro g
    have hmeq : (μ.withDensity fun x => ENNReal.ofReal (p (g • θ) x))
        = μ.withDensity fun x => ENNReal.ofReal (p θ (g⁻¹ • x)) := by
      rw [← hdens (g • θ), ← hP g θ, hdens θ]
      exact map_smul_withDensity g (hpmeas θ).ennreal_ofReal (hμ g)
    have hae := (withDensity_eq_iff_of_sigmaFinite
      (hpmeas (g • θ)).ennreal_ofReal.aemeasurable
      ((hpmeas θ).comp (measurable_const_smul g⁻¹)).ennreal_ofReal.aemeasurable).mp hmeq
    filter_upwards [hae] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff (hpnonneg (g • θ) x) (hpnonneg θ (g⁻¹ • x))).mp hx
  have hall : ∀ᵐ x ∂μ, ∀ g : G, p (g • θ) x = p θ (g⁻¹ • x) := ae_all_iff.mpr key
  filter_upwards [hall] with x hx
  show orbitAverage G (p θ) x = (Fintype.card G : ℝ)⁻¹ * ∑ g : G, p (g • θ) x
  unfold orbitAverage
  congr 1
  rw [Finset.sum_congr rfl (fun g _ => hx g)]
  exact (Equiv.sum_comp (Equiv.inv G) (fun g => p θ (g • x))).symm

/-! ### The orbit-averaged model and its optimality bridge -/

/-- The orbit average of a density carries an honest probability density with respect to
`μ`: the associated `withDensity` measure is a probability measure. -/
private theorem hasDensity_orbitAverage [Fintype G] [MeasurableSMul G 𝓧] {P : Θ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {μ : Measure 𝓧} {p : Θ → 𝓧 → ℝ}
    (hμinv : ∀ g : G, μ.map (fun x : 𝓧 => g • x) = μ)
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (p θ x))
    (hpmeas : ∀ θ, Measurable (p θ)) (hpnonneg : ∀ θ x, 0 ≤ p θ x) (θ : Θ) :
    HasDensity μ (orbitAverage G (p θ))
        (μ.withDensity fun x => ENNReal.ofReal (orbitAverage G (p θ) x)) ∧
      IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (orbitAverage G (p θ) x)) := by
  have horbnn : ∀ x, 0 ≤ orbitAverage G (p θ) x := by
    intro x; unfold orbitAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun g _ => hpnonneg θ (g • x))
  have horbmeas : Measurable (orbitAverage G (p θ)) := by
    unfold orbitAverage
    exact (Finset.measurable_sum _
      (fun g _ => (hpmeas θ).comp (measurable_const_smul g))).const_mul _
  have hintp : Integrable (p θ) μ := by
    refine ⟨(hpmeas θ).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (hpnonneg θ))]
    have h1 : (P θ) Set.univ = 1 := measure_univ
    rw [hdens θ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    rw [h1]; exact ENNReal.one_lt_top
  have hp1 : ∫ x, p θ x ∂μ = 1 := by
    have h1 : (P θ) Set.univ = 1 := measure_univ
    rw [hdens θ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    have h := ofReal_integral_eq_lintegral_ofReal hintp (Filter.Eventually.of_forall (hpnonneg θ))
    rw [h1] at h
    have hnn : 0 ≤ ∫ x, p θ x ∂μ := integral_nonneg (hpnonneg θ)
    have := congrArg ENNReal.toReal h
    rwa [ENNReal.toReal_ofReal hnn, ENNReal.toReal_one] at this
  have horbint : Integrable (orbitAverage G (p θ)) μ := by
    unfold orbitAverage
    refine Integrable.const_mul (integrable_finset_sum _ (fun g _ => ?_)) _
    exact (⟨measurable_const_smul g, hμinv g⟩ :
      MeasurePreserving _ μ μ).integrable_comp_of_integrable hintp
  have horb1 : ∫ x, orbitAverage G (p θ) x ∂μ = 1 := by
    rw [integral_orbitAverage_eq (hpmeas θ) hintp hμinv, hp1]
  refine ⟨⟨horbmeas, horbnn, rfl⟩, ⟨?_⟩⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal horbint (Filter.Eventually.of_forall horbnn),
    horb1, ENNReal.ofReal_one]

/-- **The optimality bridge.** For an invariant critical function, its power against the
orbit-averaged probability measure at `θ` equals its true power at `θ`. This is the change
of variables that makes the sample-side orbit-average model faithful. -/
private theorem powerAgainst_orbitAverage_eq [Fintype G] [MeasurableSMul G 𝓧]
    {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)] {μ : Measure 𝓧} {p : Θ → 𝓧 → ℝ}
    (hμinv : ∀ g : G, μ.map (fun x : 𝓧 => g • x) = μ)
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (p θ x))
    (hpmeas : ∀ θ, Measurable (p θ)) (hpnonneg : ∀ θ x, 0 ≤ p θ x)
    {χ : 𝓧 → ℝ} (hχc : IsCriticalFn χ) (hχinv : IsInvariantTest G χ) (θ : Θ) :
    powerAgainst (μ.withDensity fun x => ENNReal.ofReal (orbitAverage G (p θ) x)) χ
        = power P χ θ := by
  haveI : Nonempty G := ⟨1⟩
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have horbnn : ∀ x, 0 ≤ orbitAverage G (p θ) x := by
    intro x; unfold orbitAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun g _ => hpnonneg θ (g • x))
  have horbmeas : Measurable (orbitAverage G (p θ)) := by
    unfold orbitAverage
    exact (Finset.measurable_sum _
      (fun g _ => (hpmeas θ).comp (measurable_const_smul g))).const_mul _
  have hintp : Integrable (p θ) μ := by
    refine ⟨(hpmeas θ).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (hpnonneg θ))]
    have h1 : (P θ) Set.univ = 1 := measure_univ
    rw [hdens θ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    rw [h1]; exact ENNReal.one_lt_top
  have hpw : power P χ θ = ∫ x, χ x * p θ x ∂μ := by
    unfold power; rw [hdens θ, power_withDensity_eq (hpmeas θ) (hpnonneg θ) χ]
  have hint : ∀ g : G, Integrable (fun x => χ x * p θ (g • x)) μ := by
    intro g
    have hpg : Integrable (fun x => p θ (g • x)) μ :=
      (⟨measurable_const_smul g, hμinv g⟩ :
        MeasurePreserving _ μ μ).integrable_comp_of_integrable hintp
    exact hpg.bdd_mul hχc.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hχc.2 x).1]; exact (hχc.2 x).2)
  have key : ∀ g : G, ∫ x, χ x * p θ (g • x) ∂μ = ∫ x, χ x * p θ x ∂μ := by
    intro g
    have hFmeas : Measurable (fun y : 𝓧 => χ (g⁻¹ • y) * p θ y) :=
      (hχc.1.comp (measurable_const_smul g⁻¹)).mul (hpmeas θ)
    have h1 := integral_smul_invariant g hFmeas (hμinv g)
    simp only [inv_smul_smul] at h1
    rw [h1]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun x => congrArg (· * p θ x) (hχinv g⁻¹ x))
  have hpt : ∀ x, χ x * orbitAverage G (p θ) x
      = (Fintype.card G : ℝ)⁻¹ * ∑ g : G, χ x * p θ (g • x) := by
    intro x; unfold orbitAverage; rw [mul_left_comm, Finset.mul_sum]
  unfold powerAgainst
  rw [power_withDensity_eq horbmeas horbnn χ, hpw,
    integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_finset_sum _ (fun g _ => hint g), Finset.sum_congr rfl (fun g _ => key g),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- **From most-powerful for the orbit-averaged model to UMP invariant.** If `φ` is an
invariant critical function that is most powerful for the orbit-averaged simple-vs-simple
problem at the class representatives, then it is UMP among invariant level-`α` tests. -/
private theorem isUMPInvariant_of_mostPowerful [Fintype G] [MeasurableSMul G 𝓧]
    {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)] {μ : Measure 𝓧} {p : Θ → 𝓧 → ℝ}
    {Θ₀ Θ₁ : Set Θ} {θ₀ θ₁ : Θ} {α : ℝ} {φ : 𝓧 → ℝ}
    (hP : IsInvariantModel (G := G) P)
    (hμinv : ∀ g : G, μ.map (fun x : 𝓧 => g • x) = μ)
    (htrans₀ : ∀ θ ∈ Θ₀, ∀ θ' ∈ Θ₀, ∃ g : G, θ' = g • θ)
    (htrans₁ : ∀ θ ∈ Θ₁, ∀ θ' ∈ Θ₁, ∃ g : G, θ' = g • θ)
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (p θ x))
    (hpmeas : ∀ θ, Measurable (p θ)) (hpnonneg : ∀ θ x, 0 ≤ p θ x)
    (hθ₀ : θ₀ ∈ Θ₀) (hθ₁ : θ₁ ∈ Θ₁)
    (hφ : IsCriticalFn φ) (hφinv : IsInvariantTest G φ)
    (hMP : IsMostPowerful (μ.withDensity fun x => ENNReal.ofReal (orbitAverage G (p θ₀) x))
      (μ.withDensity fun x => ENNReal.ofReal (orbitAverage G (p θ₁) x)) α φ) :
    IsUMPInvariant G P Θ₀ Θ₁ α φ := by
  have horbitpow : ∀ (ψ : 𝓧 → ℝ), IsCriticalFn ψ → IsInvariantTest G ψ →
      ∀ (h : G) (θ : Θ), power P ψ (h • θ) = power P ψ θ := by
    intro ψ hψc hψinv h θ
    unfold power
    rw [← hP h θ, integral_map (measurable_const_smul h).aemeasurable hψc.1.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hψinv h x)
  refine ⟨hφ, hφinv, ?_, ?_⟩
  · intro θ hθ
    obtain ⟨g, hg⟩ := htrans₀ θ₀ hθ₀ θ hθ
    rw [hg, horbitpow φ hφ hφinv g θ₀,
      ← powerAgainst_orbitAverage_eq hμinv hdens hpmeas hpnonneg hφ hφinv θ₀]
    exact hMP.2.1
  · intro ψ hψc hψinv hψlvl θ hθ
    obtain ⟨g, hg⟩ := htrans₁ θ₁ hθ₁ θ hθ
    rw [hg, horbitpow ψ hψc hψinv g θ₁, horbitpow φ hφ hφinv g θ₁]
    have hψs :
        powerAgainst (μ.withDensity fun x => ENNReal.ofReal (orbitAverage G (p θ₀) x)) ψ ≤ α := by
      rw [powerAgainst_orbitAverage_eq hμinv hdens hpmeas hpnonneg hψc hψinv θ₀]
      exact hψlvl θ₀ hθ₀
    have hb := hMP.2.2 ψ hψc hψs
    rw [powerAgainst_orbitAverage_eq hμinv hdens hpmeas hpnonneg hψc hψinv θ₁,
      powerAgainst_orbitAverage_eq hμinv hdens hpmeas hpnonneg hφ hφinv θ₁] at hb
    exact hb

/-- **A Neyman–Pearson test for the orbit-averaged densities is UMP invariant.** For a
finite group whose induced action is transitive on the null class and on the alternative
class, an invariant test that rejects where the orbit-averaged likelihood ratio exceeds a
threshold, accepts where it falls short, and has size `α`, is uniformly most powerful
among invariant level-`α` tests. -/
theorem isUMPInvariant_of_orbitAverage_ratio [Fintype G] [MeasurableSMul G 𝓧]
    {P : Θ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {μ : Measure 𝓧} [SigmaFinite μ] {p : Θ → 𝓧 → ℝ}
    {Θ₀ Θ₁ : Set Θ} {θ₀ θ₁ : Θ} {α k : ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: the model intertwines the sample- and parameter-space actions
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: the dominating measure is itself invariant under the group. Without this the
    -- statement is FALSE: with G = Z/2 acting on R by reflection, every P θ symmetric (so
    -- `IsInvariantModel` holds) but μ asymmetric (e.g. N(1,10)), the sample-side orbit-average
    -- ratio is not the likelihood ratio, so the test is invariant but not UMP.
    (hμinv : ∀ g : G, μ.map (fun x : 𝓧 => g • x) = μ)
    -- USER-INPUT: the null and alternative classes are preserved by the induced action
    (hΘ₀ : ∀ (g : G) (θ : Θ), θ ∈ Θ₀ → g • θ ∈ Θ₀)
    (hΘ₁ : ∀ (g : G) (θ : Θ), θ ∈ Θ₁ → g • θ ∈ Θ₁)
    -- USER-INPUT: the induced action is transitive on the null class
    (htrans₀ : ∀ θ ∈ Θ₀, ∀ θ' ∈ Θ₀, ∃ g : G, θ' = g • θ)
    -- USER-INPUT: the induced action is transitive on the alternative class
    (htrans₁ : ∀ θ ∈ Θ₁, ∀ θ' ∈ Θ₁, ∃ g : G, θ' = g • θ)
    -- USER-INPUT: the model is dominated by `μ` with measurable nonnegative densities `p`
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (p θ x))
    (hpmeas : ∀ θ, Measurable (p θ)) (hpnonneg : ∀ θ x, 0 ≤ p θ x)
    -- USER-INPUT: the chosen null and alternative representatives
    (hθ₀ : θ₀ ∈ Θ₀) (hθ₁ : θ₁ ∈ Θ₁)
    -- USER-INPUT: `φ` is a critical function, invariant under the group
    (hφ : IsCriticalFn φ) (hφinv : IsInvariantTest G φ)
    -- USER-INPUT: `φ` rejects above and accepts below the threshold `k` for the
    -- orbit-averaged likelihood ratio
    (hrej : ∀ x, k * orbitAverage G (p θ₀) x < orbitAverage G (p θ₁) x → φ x = 1)
    (hacc : ∀ x, orbitAverage G (p θ₁) x < k * orbitAverage G (p θ₀) x → φ x = 0)
    -- USER-INPUT: `φ` has size exactly `α` at the null representative
    (hsize : power P φ θ₀ = α) :
    IsUMPInvariant G P Θ₀ Θ₁ α φ := by
  obtain ⟨hd0, hQ0⟩ := hasDensity_orbitAverage hμinv hdens hpmeas hpnonneg θ₀
  obtain ⟨hd1, hQ1⟩ := hasDensity_orbitAverage hμinv hdens hpmeas hpnonneg θ₁
  haveI := hQ0; haveI := hQ1
  have hshape : HasNPShape μ (orbitAverage G (p θ₀)) (orbitAverage G (p θ₁))
      (ENNReal.ofReal k) φ := by
    refine ⟨Filter.Eventually.of_forall (fun x hlt => hrej x ?_),
      Filter.Eventually.of_forall (fun x hlt => hacc x ?_)⟩
    · rw [ofReal_mul_nonneg (hd0.2.1 x)] at hlt
      exact ofReal_lt_of_ofReal_lt hlt
    · rw [ofReal_mul_nonneg (hd0.2.1 x)] at hlt
      exact ofReal_lt_of_ofReal_lt hlt
  have hsizeQ0 :
      powerAgainst (μ.withDensity fun x => ENNReal.ofReal (orbitAverage G (p θ₀) x)) φ = α := by
    rw [powerAgainst_orbitAverage_eq hμinv hdens hpmeas hpnonneg hφ hφinv θ₀]; exact hsize
  have hMP : IsMostPowerful (μ.withDensity fun x => ENNReal.ofReal (orbitAverage G (p θ₀) x))
      (μ.withDensity fun x => ENNReal.ofReal (orbitAverage G (p θ₁) x)) α φ :=
    isMostPowerful_of_npShape μ _ _ hd0 hd1 hφ hsizeQ0 hshape
  exact isUMPInvariant_of_mostPowerful hP hμinv htrans₀ htrans₁ hdens hpmeas hpnonneg
    hθ₀ hθ₁ hφ hφinv hMP

/-- **Existence of a UMP invariant test under a finite transitive group.** -/
theorem exists_isUMPInvariant_of_finite_transitive [Fintype G] [MeasurableSMul G 𝓧]
    {P : Θ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {μ : Measure 𝓧} [SigmaFinite μ] {p : Θ → 𝓧 → ℝ}
    {Θ₀ Θ₁ : Set Θ} {α : ℝ}
    -- USER-INPUT: the model intertwines the sample- and parameter-space actions
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: the dominating measure is itself invariant under the group. Without this the
    -- statement is FALSE: with G = Z/2 acting on R by reflection, every P θ symmetric (so
    -- `IsInvariantModel` holds) but μ asymmetric (e.g. N(1,10)), the sample-side orbit-average
    -- ratio is not the likelihood ratio, so the test is invariant but not UMP.
    (hμinv : ∀ g : G, μ.map (fun x : 𝓧 => g • x) = μ)
    -- USER-INPUT: the null and alternative classes are preserved by the induced action
    (hΘ₀ : ∀ (g : G) (θ : Θ), θ ∈ Θ₀ → g • θ ∈ Θ₀)
    (hΘ₁ : ∀ (g : G) (θ : Θ), θ ∈ Θ₁ → g • θ ∈ Θ₁)
    -- USER-INPUT: the induced action is transitive on each of the two classes
    (htrans₀ : ∀ θ ∈ Θ₀, ∀ θ' ∈ Θ₀, ∃ g : G, θ' = g • θ)
    (htrans₁ : ∀ θ ∈ Θ₁, ∀ θ' ∈ Θ₁, ∃ g : G, θ' = g • θ)
    -- USER-INPUT: both classes are nonempty
    (hne₀ : Θ₀.Nonempty) (hne₁ : Θ₁.Nonempty)
    -- USER-INPUT: the model is dominated by `μ` with measurable nonnegative densities `p`
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (p θ x))
    (hpmeas : ∀ θ, Measurable (p θ)) (hpnonneg : ∀ θ x, 0 ≤ p θ x)
    -- USER-INPUT: the prescribed level is a probability
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ φ : 𝓧 → ℝ, IsUMPInvariant G P Θ₀ Θ₁ α φ := by
  obtain ⟨θ₀, hθ₀⟩ := hne₀
  obtain ⟨θ₁, hθ₁⟩ := hne₁
  obtain ⟨hd0, hQ0⟩ := hasDensity_orbitAverage hμinv hdens hpmeas hpnonneg θ₀
  obtain ⟨hd1, hQ1⟩ := hasDensity_orbitAverage hμinv hdens hpmeas hpnonneg θ₁
  haveI := hQ0; haveI := hQ1
  obtain ⟨C, γ, _, _, hMP⟩ := exists_mostPowerful μ
    (μ.withDensity fun x => ENNReal.ofReal (orbitAverage G (p θ₀) x))
    (μ.withDensity fun x => ENNReal.ofReal (orbitAverage G (p θ₁) x))
    hd0 hd1 (Set.mem_Icc.mpr ⟨hα0, hα1⟩)
  refine ⟨npTest (orbitAverage G (p θ₀)) (orbitAverage G (p θ₁)) C γ, ?_⟩
  have hφinv : IsInvariantTest G (npTest (orbitAverage G (p θ₀)) (orbitAverage G (p θ₁)) C γ) := by
    intro g x
    unfold npTest
    rw [isInvariantTest_orbitAverage (p θ₀) g x, isInvariantTest_orbitAverage (p θ₁) g x]
  exact isUMPInvariant_of_mostPowerful hP hμinv htrans₀ htrans₁ hdens hpmeas hpnonneg
    hθ₀ hθ₁ hMP.1 hφinv hMP

end StatLean.HypothesisTesting
