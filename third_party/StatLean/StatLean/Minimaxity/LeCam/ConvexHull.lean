module
public import StatLean.Minimaxity.EstimationToTesting
public import StatLean.Minimaxity.ForMathlib.TotalVariation

@[expose] public section

/-!
# Le Cam's convex-hull lower bound

Le Cam's two-point method generalizes from single pairs to pairs of *classes*: if two subfamilies
$\mathcal{P}_0, \mathcal{P}_1 \subseteq \mathcal{P}$ are $2\delta$-separated in the loss-defining
semimetric $\rho$, then the minimax risk is controlled by the total variation distance measured over
their **convex hulls** (mixtures), which can be far smaller than the pointwise separation. With the
distortion function $\Phi$ increasing, the bound reads

$$\sup_{P\in\mathcal{P}} \mathbb{E}_P\!\big[\Phi\big(\rho(\hat\theta, \theta(P))\big)\big]
  \;\ge\; \tfrac{\Phi(\delta)}{2}\,
  \sup_{Q_0\in\operatorname{conv}(\mathcal{P}_0),\,Q_1\in\operatorname{conv}(\mathcal{P}_1)}
  \big(1 - \lVert Q_1 - Q_0\rVert_{\mathrm{TV}}\big).$$

We state it for given mixtures (the supremum over the convex hulls is recovered by quantifying over
the mixing measures $\pi_0, \pi_1$): for any $2\delta$-separated pair of subfamilies indexed by
$a_0, a_1$ and any priors $\pi_0, \pi_1$, the bound holds with the mixtures
$\bar Q_0 = \int P_{a_0}\,d\pi_0$ and $\bar Q_1 = \int P_{a_1}\,d\pi_1$. Compared with Wainwright's
statement we make the constants and monotonicity explicit: $\Phi$ is assumed *monotone* (rather than
specializing to a fixed power loss), and the conclusion carries the factor $\Phi(\delta)/2$.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.2, Lemma 15.9,
Eq. (15.26).

**Proof formalization notes.** Against the two-class prior with mixing measures $\pi_0, \pi_1$, the
nearest-class test built from any estimator reduces the minimax risk to binary testing error between
the mixtures $\bar Q_0, \bar Q_1$, and `one_sub_tvDist_eq_iInf` rewrites $1 - \lVert\bar Q_1 - \bar
Q_0\rVert_{\mathrm{TV}}$ as the optimal-test value. The crucial $\Omega$-measurability of the
selector is supplied by `Metric.continuous_infEDist`: the distance to the (possibly uncountable)
class of functional values is *continuous*, hence measurable. The per-class core
(`mul_measure_mem_le_avg`) is the mixture analogue of the geometric Markov/triangle bound
$\Phi(\delta)\cdot\mathbf{1}[\text{error}] \le \Phi(\rho)$ integrated against the prior, mirroring
`mul_multiwayTestingError_le` in `EstimationToTesting.lean`. Assembly gives $\Phi(\delta)\cdot(1 -
\mathrm{TV}) \le A_0 + A_1 \le 2\cdot\sup$, then halves.

**Bibliographic comments.** The convex-hull (mixture) refinement of the two-point method originates
with L. Le Cam, "Convergence of estimates under dimensionality restrictions," *The Annals of
Statistics* **1** (1973), no. 1, 38–53, where the lower bound is expressed through the affinity /
total-variation distance between mixtures over the two competing subfamilies. It is now standard as
"Le Cam's method"; the form stated here follows Wainwright's textbook synthesis (Lemma 15.9), with
related expositions in Yu, "Assouad, Fano, and Le Cam," in *Festschrift for Lucien Le Cam* (Springer,
1997), 423–435, and Tsybakov, *Introduction to Nonparametric Estimation* (Springer, 2009), §2.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {Θ Ω 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [mΩ : MeasurableSpace Ω]
  [m𝓧 : MeasurableSpace 𝓧]

/-- **Per-class mixture bound** for Le Cam's convex-hull method. If a measurable region `S ⊆ Ω`
is `δ`-far from every functional value `g (a i)` of the subfamily indexed by `a` (i.e. the test
"decide the *other* class" can only fire when the estimate is at semimetric distance `≥ δ` from the
truth), then `Φ(δ)` times the probability — under the mixture `Q̄ = ∫ P_{a i} dπ` post-composed with
any estimator `κ` — that the estimate lands in `S` is dominated by the averaged distortion risk over
that subfamily. This is the mixture analogue of the geometric core of `mul_multiwayTestingError_le`
(`EstimationToTesting.lean`): the same Markov/triangle bound `Φ(δ)·𝟙[error] ≤ Φ(ρ)` integrated
against the prior `π`. -/
private lemma mul_measure_mem_le_avg [PseudoEMetricSpace Ω]
    {Φ : ℝ≥0∞ → ℝ≥0∞} {g : Θ → Ω} (hΦ : Monotone Φ) {δ : ℝ≥0∞}
    (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    {ι : Type*} [MeasurableSpace ι] (a : ι → Θ) (ha : Measurable a) (π : Measure ι)
    (κ : Kernel 𝓧 Ω) [IsMarkovKernel κ]
    {S : Set Ω} (hS : MeasurableSet S) (hSsep : ∀ i y, y ∈ S → δ ≤ edist (g (a i)) y) :
    Φ δ * ∫⁻ x, (κ x) S ∂(P.comap a ha ∘ₘ π)
      ≤ ∫⁻ i, ∫⁻ y, distortionLoss Φ g (a i) y ∂((κ ∘ₖ P) (a i)) ∂π := by
  -- Rewrite the mixture lintegral over the prior, then identify it with the testing probabilities.
  have hmeas : Measurable (fun x => (κ x) S) := κ.measurable_coe hS
  have hbind : ∫⁻ x, (κ x) S ∂(P.comap a ha ∘ₘ π)
      = ∫⁻ i, (κ ∘ₖ P) (a i) S ∂π := by
    rw [Measure.lintegral_bind (P.comap a ha).measurable.aemeasurable hmeas.aemeasurable]
    refine lintegral_congr fun i => ?_
    rw [Kernel.comap_apply, Kernel.comp_apply' κ P (a i) hS]
  rw [hbind]
  calc Φ δ * ∫⁻ i, (κ ∘ₖ P) (a i) S ∂π
      ≤ ∫⁻ i, Φ δ * ((κ ∘ₖ P) (a i) S) ∂π := lintegral_const_mul_le _ _
    _ ≤ ∫⁻ i, ∫⁻ y, distortionLoss Φ g (a i) y ∂((κ ∘ₖ P) (a i)) ∂π := by
        refine lintegral_mono fun i => ?_
        rw [← lintegral_indicator_one hS]
        calc Φ δ * ∫⁻ y, S.indicator 1 y ∂((κ ∘ₖ P) (a i))
            ≤ ∫⁻ y, Φ δ * S.indicator 1 y ∂((κ ∘ₖ P) (a i)) := lintegral_const_mul_le _ _
          _ ≤ ∫⁻ y, distortionLoss Φ g (a i) y ∂((κ ∘ₖ P) (a i)) := by
              refine lintegral_mono fun y => ?_
              simp only [distortionLoss]
              by_cases hy : y ∈ S
              · rw [Set.indicator_of_mem hy, Pi.one_apply, mul_one]
                exact hΦ (hSsep i y hy)
              · rw [Set.indicator_of_notMem hy, mul_zero]; exact zero_le

/-- **Le Cam's convex-hull lower bound** (Wainwright Lemma 15.9, Eq. (15.26)): for two `2δ`-separated
subfamilies `{P_{a₀ i}}`, `{P_{a₁ i}}` and any mixing priors `π₀, π₁`, the minimax risk dominates
`(δ/2)(1 − ‖Q̄₁ − Q̄₀‖_TV)`, where `Q̄₀, Q̄₁` are the corresponding mixtures over the convex hulls.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.2, Lemma 15.9. -/
theorem minimax_le_cam_convex_hull [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (δ : ℝ≥0∞) {ι₀ ι₁ : Type*} [MeasurableSpace ι₀] [MeasurableSpace ι₁]
    (a₀ : ι₀ → Θ) (a₁ : ι₁ → Θ) (ha₀ : Measurable a₀) (ha₁ : Measurable a₁)
    (π₀ : Measure ι₀) (π₁ : Measure ι₁) [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁]
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.2.2, Lemma 15.9.
    (hΦ : Monotone Φ)
    -- USER-INPUT: the two subfamilies are `2δ`-separated in the semimetric `ρ`; Wainwright §15.2.2.
    (hsep : ∀ i₀ i₁, 2 * δ ≤ edist (g (a₀ i₀)) (g (a₁ i₁))) :
    Φ δ / 2 * (1 - tvDist (P.comap a₀ ha₀ ∘ₘ π₀) (P.comap a₁ ha₁ ∘ₘ π₁))
      ≤ minimaxRiskDist Φ g P := by
  classical
  -- Wainwright's convex-hull method (§15.2.2): against the two-class prior with mixing measures
  -- `π₀, π₁`, the nearest-class test built from any estimator reduces the minimax risk to binary
  -- testing error between the mixtures `Q̄₀ = ∫ P_{a₀} dπ₀`, `Q̄₁ = ∫ P_{a₁} dπ₁`, and
  -- `one_sub_tvDist_eq_iInf` rewrites `1 − ‖Q̄₁ − Q̄₀‖_TV` as the optimal-test value.  The crucial
  -- `Ω`-measurability of the selector is supplied by `Metric.continuous_infEDist`: the distance to
  -- the (possibly uncountable) class of functional values is *continuous*, hence measurable.
  set m₀ : Measure 𝓧 := P.comap a₀ ha₀ ∘ₘ π₀ with hm₀
  set m₁ : Measure 𝓧 := P.comap a₁ ha₁ ∘ₘ π₁ with hm₁
  haveI : IsMarkovKernel (P.comap a₀ ha₀) := Kernel.IsMarkovKernel.comap P ha₀
  haveI : IsMarkovKernel (P.comap a₁ ha₁) := Kernel.IsMarkovKernel.comap P ha₁
  haveI : IsProbabilityMeasure m₀ := by rw [hm₀]; infer_instance
  haveI : IsProbabilityMeasure m₁ := by rw [hm₁]; infer_instance
  -- The two classes of functional values and their (continuous, hence measurable) distance fields.
  set C₀ : Set Ω := Set.range (fun i₀ => g (a₀ i₀)) with hC₀
  set C₁ : Set Ω := Set.range (fun i₁ => g (a₁ i₁)) with hC₁
  set d₀ : Ω → ℝ≥0∞ := fun y => Metric.infEDist y C₀ with hd₀def
  set d₁ : Ω → ℝ≥0∞ := fun y => Metric.infEDist y C₁ with hd₁def
  have hd₀meas : Measurable d₀ := Metric.continuous_infEDist.measurable
  have hd₁meas : Measurable d₁ := Metric.continuous_infEDist.measurable
  -- Distance of `y` to either class as an infimum over the index set.
  have hd₀ : ∀ y, d₀ y = ⨅ i₀, edist y (g (a₀ i₀)) := by
    intro y; rw [hd₀def, hC₀]; exact iInf_range
  have hd₁ : ∀ y, d₁ y = ⨅ i₁, edist y (g (a₁ i₁)) := by
    intro y; rw [hd₁def, hC₁]; exact iInf_range
  -- `2δ`-separation of the classes: `2δ ≤ d₀ y + d₁ y` everywhere (triangle inequality).
  have htotal : ∀ y, 2 * δ ≤ d₀ y + d₁ y := by
    intro y
    rw [hd₀ y, hd₁ y, ENNReal.iInf_add]
    refine le_iInf fun i₀ => ?_
    rw [ENNReal.add_iInf]
    refine le_iInf fun i₁ => ?_
    calc 2 * δ ≤ edist (g (a₀ i₀)) (g (a₁ i₁)) := hsep i₀ i₁
      _ ≤ edist (g (a₀ i₀)) y + edist y (g (a₁ i₁)) := edist_triangle _ _ _
      _ = edist y (g (a₀ i₀)) + edist y (g (a₁ i₁)) := by rw [edist_comm y (g (a₀ i₀))]
  -- Decision regions: `S₀` = "decide class 1" (error if truth is class 0), `S₁` = "decide class 0".
  set S₀ : Set Ω := {y | d₁ y < d₀ y} with hS₀def
  set S₁ : Set Ω := {y | d₀ y ≤ d₁ y} with hS₁def
  have hS₀meas : MeasurableSet S₀ := measurableSet_lt hd₁meas hd₀meas
  have hS₁meas : MeasurableSet S₁ := measurableSet_le hd₀meas hd₁meas
  have hSunion : S₀ ∪ S₁ = Set.univ := by
    ext y; simp only [hS₀def, hS₁def, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact lt_or_ge (d₁ y) (d₀ y)
  have hSdisj : Disjoint S₀ S₁ := by
    rw [Set.disjoint_left]
    intro y hy0 hy1
    rw [hS₀def, Set.mem_setOf_eq] at hy0
    rw [hS₁def, Set.mem_setOf_eq] at hy1
    exact absurd hy1 (not_le.mpr hy0)
  -- Separation of each decision region from the *opposite* class.
  have hsep₀ : ∀ i₀ y, y ∈ S₀ → δ ≤ edist (g (a₀ i₀)) y := by
    intro i₀ y hy
    have hlt : d₁ y < d₀ y := hy
    have h2 : 2 * δ ≤ 2 * d₀ y := by
      calc 2 * δ ≤ d₀ y + d₁ y := htotal y
        _ ≤ d₀ y + d₀ y := add_le_add_right hlt.le _
        _ = 2 * d₀ y := (two_mul _).symm
    have hδ : δ ≤ d₀ y := (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2
    refine hδ.trans ?_
    rw [hd₀ y, edist_comm (g (a₀ i₀)) y]
    exact iInf_le _ i₀
  have hsep₁ : ∀ i₁ y, y ∈ S₁ → δ ≤ edist (g (a₁ i₁)) y := by
    intro i₁ y hy
    have hle : d₀ y ≤ d₁ y := hy
    have h2 : 2 * δ ≤ 2 * d₁ y := by
      calc 2 * δ ≤ d₀ y + d₁ y := htotal y
        _ ≤ d₁ y + d₁ y := add_le_add_left hle _
        _ = 2 * d₁ y := (two_mul _).symm
    have hδ : δ ≤ d₁ y := (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2
    refine hδ.trans ?_
    rw [hd₁ y, edist_comm (g (a₁ i₁)) y]
    exact iInf_le _ i₁
  -- Reduce the minimax risk to a per-estimator bound.
  unfold minimaxRiskDist minimaxRisk
  refine le_iInf₂ fun κ hκ => ?_
  haveI := hκ
  set R : Θ → ℝ≥0∞ := fun θ => ∫⁻ y, distortionLoss Φ g θ y ∂((κ ∘ₖ P) θ) with hR
  -- The averaged risks over each subfamily are each at most the supremum.
  have hsup₀ : ∫⁻ i₀, R (a₀ i₀) ∂π₀ ≤ ⨆ θ, R θ := by
    calc ∫⁻ i₀, R (a₀ i₀) ∂π₀ ≤ ∫⁻ _, (⨆ θ, R θ) ∂π₀ :=
          lintegral_mono fun i₀ => le_iSup R (a₀ i₀)
      _ = ⨆ θ, R θ := by rw [lintegral_const, measure_univ, mul_one]
  have hsup₁ : ∫⁻ i₁, R (a₁ i₁) ∂π₁ ≤ ⨆ θ, R θ := by
    calc ∫⁻ i₁, R (a₁ i₁) ∂π₁ ≤ ∫⁻ _, (⨆ θ, R θ) ∂π₁ :=
          lintegral_mono fun i₁ => le_iSup R (a₁ i₁)
      _ = ⨆ θ, R θ := by rw [lintegral_const, measure_univ, mul_one]
  -- Feasible variational pair `(f₀, f₁)` from the decision regions of the estimator `κ`.
  set f₀ : 𝓧 → ℝ≥0∞ := fun x => (κ x) S₀ with hf₀
  set f₁ : 𝓧 → ℝ≥0∞ := fun x => (κ x) S₁ with hf₁
  have hf₀meas : Measurable f₀ := κ.measurable_coe hS₀meas
  have hf₁meas : Measurable f₁ := κ.measurable_coe hS₁meas
  have hfeas : ∀ x, (1 : ℝ≥0∞) ≤ f₀ x + f₁ x := by
    intro x
    rw [hf₀, hf₁, ← measure_union hSdisj hS₁meas, hSunion, measure_univ]
  -- Variational lower bound on `1 − TV` instantiated at `(f₀, f₁)`.
  have hTV : 1 - tvDist m₀ m₁ ≤ ∫⁻ x, f₀ x ∂m₀ + ∫⁻ x, f₁ x ∂m₁ := by
    rw [one_sub_tvDist_eq_iInf m₀ m₁]
    exact iInf_le_of_le f₀ (iInf_le_of_le f₁ (iInf_le_of_le hf₀meas
      (iInf_le_of_le hf₁meas (iInf_le_of_le hfeas le_rfl))))
  -- Each variational integral against a mixture is dominated by the averaged distortion risk.
  have hbnd₀ : Φ δ * ∫⁻ x, f₀ x ∂m₀ ≤ ∫⁻ i₀, R (a₀ i₀) ∂π₀ :=
    mul_measure_mem_le_avg hΦ P a₀ ha₀ π₀ κ hS₀meas hsep₀
  have hbnd₁ : Φ δ * ∫⁻ x, f₁ x ∂m₁ ≤ ∫⁻ i₁, R (a₁ i₁) ∂π₁ :=
    mul_measure_mem_le_avg hΦ P a₁ ha₁ π₁ κ hS₁meas hsep₁
  -- Assemble: `Φδ·(1 − TV) ≤ A₀ + A₁ ≤ 2·sup`, then halve.
  have hkey : Φ δ * (1 - tvDist m₀ m₁) ≤ 2 * ⨆ θ, R θ := by
    calc Φ δ * (1 - tvDist m₀ m₁)
        ≤ Φ δ * (∫⁻ x, f₀ x ∂m₀ + ∫⁻ x, f₁ x ∂m₁) := by gcongr
      _ = Φ δ * ∫⁻ x, f₀ x ∂m₀ + Φ δ * ∫⁻ x, f₁ x ∂m₁ := by rw [mul_add]
      _ ≤ ∫⁻ i₀, R (a₀ i₀) ∂π₀ + ∫⁻ i₁, R (a₁ i₁) ∂π₁ := add_le_add hbnd₀ hbnd₁
      _ ≤ (⨆ θ, R θ) + (⨆ θ, R θ) := add_le_add hsup₀ hsup₁
      _ = 2 * ⨆ θ, R θ := (two_mul _).symm
  calc Φ δ / 2 * (1 - tvDist m₀ m₁)
      = 2⁻¹ * (Φ δ * (1 - tvDist m₀ m₁)) := by rw [div_eq_mul_inv]; ring
    _ ≤ 2⁻¹ * (2 * ⨆ θ, R θ) := by gcongr
    _ = ⨆ θ, R θ := by rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

end StatLean.Minimaxity
