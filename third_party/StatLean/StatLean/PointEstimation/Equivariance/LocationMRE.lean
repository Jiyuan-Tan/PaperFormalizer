module
public import StatLean.PointEstimation.Equivariance.ConditionalRiskEngine
public import StatLean.PointEstimation.Equivariance.LocationStructure
public import StatLean.PointEstimation.ForMathlib.ConvexMinimizers
public import StatLean.PointEstimation.ForMathlib.MeasurableArgmin
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

@[expose] public section

/-!
# The minimum risk equivariant location estimator

Putting together the two halves of the theory: the equivariant class is exactly
`{δ₀ − v ∘ diffs}` (`LocationStructure`), and minimizing over such a class reduces to a
fibrewise minimization against the conditional distribution of the data given the
differences (`ConditionalRiskEngine`). The result is the construction of the minimum risk
equivariant (MRE) location estimator.

* `isLocMRE_of_conditional_min` — the construction: if `v*(y)` minimizes the conditional
  expected loss `E₀[ρ(δ₀(X) − v) | y]` in almost every fibre of the differences, then
  `δ₀ − v* ∘ diffs` is MRE;
* `exists_isLocMRE_of_convex` — existence for convex, non-monotone losses;
* `isLocMRE_sq_of_condMean` — squared error: the minimizer is the conditional mean,
  giving `δ*(X) = δ₀(X) − E₀[δ₀(X) | Y]`;
* `exists_isLocMRE_of_bounded_loss` — a single observation and a bounded loss vanishing
  at the origin's antipodes: an MRE estimator exists even though the loss is not convex.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.1 (First
Examples), Theorem 1.10 (the MRE estimator via conditional minimization given the differences)
and Corollary 1.11 (existence for a convex non-monotone loss). (`TPE2 §3.1 Thm 1.10, Cor
1.11`.)

**Proof formalization notes.**
* The conditional distribution of the data given the differences is written through the
  shared `orbitCondKernel (locationBase f) diffs`, whose argument order is pinned in
  `ConditionalRiskEngine`; the template is `F w x = δ₀ x − w`.
* The classical hypothesis is "for each `y` there exists a minimizing `v(y)`"; the proof
  only ever uses it on a set of full measure (the same source observes that the
  conditional risk is finite only almost everywhere), so `hmin` is stated with `∀ᵐ`.
  This weakens the hypothesis and hence strengthens the theorem.
* Measurability of `v*` is a Lean-side requirement absent from the classical statement:
  without it `δ₀ − v* ∘ diffs` need not be an estimator at all. For the convex case the
  intended route to a *measurable* selection is the convex-minimizer and measurable-argmin
  bricks in this area's `ForMathlib` layer; this file states existence and does not
  depend on them.
* Non-monotonicity of a convex loss is spelled out as "neither monotone nor antitone",
  which for a convex function is exactly the condition guaranteeing that a minimum is
  attained rather than approached at `±∞`.
* The classical companion to the squared-error corollary characterises the minimizer for
  absolute error as any conditional median; that variant is not formalized here, since
  the median has no canonical measurable selection to state it with.
* The bounded-loss existence result needs no separate finite-risk hypothesis: a loss
  bounded by `M` gives every estimator risk at most `M` under a probability law.
* **The bounded-loss proof does not go through the conditional-risk engine.** For a single
  observation equivariance pins the estimator down completely — `δ(x) = δ(0) + x₀`, read off
  by evaluating `δ(x + a·𝟙) = δ(x) + a` at `x = 0` — so the equivariant class is literally
  `{x ↦ x₀ − c : c ∈ ℝ}` and the problem is the one-dimensional minimization of
  `G c = ∫⁻ ofReal (ρ (x₀ − c))`. `G` is bounded by `ofReal M` and, by dominated convergence
  against the constant `M`, tends to `ofReal M` along `cocompact ℝ`; so either `G` is
  constant (any `c` minimizes) or some `G c₀` is strictly below the bound and
  `Continuous.exists_forall_le'` attains the minimum. The delicate input is continuity of
  `G`, where the a.e. continuity of the density enters: substituting `x ↦ x + c·𝟙` moves the
  shift off the loss and onto the density, and the shifted densities converge pointwise a.e.
  with constant total mass. There is no dominating function for them, so ordinary dominated
  convergence fails; `tendsto_lintegral_mul_of_tendsto_of_mass_eq` supplies the missing
  uniform integrability from the equal masses (Scheffé's argument). A measurable version of
  `f` is needed for that, and is obtained from `hcont`: the continuity set of any function is
  `Gδ`, hence measurable, and `f` is continuous on it.

**Bibliographic comments.** The reduction of best equivariant location estimation to a
conditional minimization given the differences, and the resulting estimator, are due to
E. J. G. Pitman, "The estimation of the location and scale parameters of a continuous
population of any given form," *Biometrika* **30** (1939), 391–421. The admissibility of
that estimator was established by C. Stein, "The admissibility of Pitman's estimator of a
single location parameter," *Ann. Math. Statist.* **30** (1959), 970–979.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.PointEstimation

section LocationMRE

variable {m : ℕ}

/-- The conditional mean minimizes the conditional expected squared error, phrased at the
`ℝ≥0∞` level with no second-moment hypothesis: outside `L²` both sides are `∞`. -/
lemma lintegral_ofReal_sq_min {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
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

/-- A convex function on the line that is not antitone blows up at `+∞`: from a strictly
increasing secant, convexity forces a positive linear minorant.

Not `private`: the scale twin `ScaleMRE` reuses it for the logarithmic reparametrization
`v ↦ γ(eᵛ)` of a scale loss. -/
lemma tendsto_atTop_of_convex_not_antitone {ρ : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ ρ) (hna : ¬ Antitone ρ) :
    Filter.Tendsto ρ Filter.atTop Filter.atTop := by
  obtain ⟨a, b, hab, hlt⟩ : ∃ a b : ℝ, a < b ∧ ρ a < ρ b := by
    rw [Antitone] at hna
    push_neg at hna
    obtain ⟨a, b, hab, hlt⟩ := hna
    exact ⟨a, b, lt_of_le_of_ne hab (by rintro rfl; exact lt_irrefl _ hlt), hlt⟩
  set s₀ : ℝ := (ρ b - ρ a) / (b - a) with hs₀
  have hs₀pos : 0 < s₀ := div_pos (by linarith) (by linarith)
  have hlb : ∀ x, b < x → ρ b + s₀ * (x - b) ≤ ρ x := by
    intro x hbx
    have hslope := hconv.slope_mono_adjacent (Set.mem_univ a) (Set.mem_univ x) hab hbx
    have hxb : 0 < x - b := by linarith
    have hstep : s₀ * (x - b) ≤ ρ x - ρ b := by
      calc s₀ * (x - b) = (ρ b - ρ a) / (b - a) * (x - b) := by rw [hs₀]
        _ ≤ (ρ x - ρ b) / (x - b) * (x - b) := mul_le_mul_of_nonneg_right hslope hxb.le
        _ = ρ x - ρ b := by field_simp
    linarith
  have hlin : Filter.Tendsto (fun x => ρ b + s₀ * (x - b)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_left
    exact Filter.Tendsto.const_mul_atTop hs₀pos
      (Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id)
  refine Filter.tendsto_atTop_mono' _ ?_ hlin
  filter_upwards [Filter.eventually_gt_atTop b] with x hx using hlb x hx

/-- A convex function on the line that is not monotone blows up at `−∞` (the reflection of
`tendsto_atTop_of_convex_not_antitone`).

Not `private`: reused by the scale twin `ScaleMRE`, as its companion above. -/
lemma tendsto_atBot_of_convex_not_monotone {ρ : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ ρ) (hnm : ¬ Monotone ρ) :
    Filter.Tendsto ρ Filter.atBot Filter.atTop := by
  have hconv' : ConvexOn ℝ Set.univ (fun x => ρ (-x)) := by
    have := hconv.comp_affineMap (AffineMap.const ℝ ℝ (0 : ℝ) - AffineMap.id ℝ ℝ)
    simpa [AffineMap.coe_sub, AffineMap.coe_const, Function.const, sub_eq_neg_add] using!
      this.subset (Set.subset_univ _) convex_univ
  have hna' : ¬ Antitone (fun x => ρ (-x)) := by
    intro h
    apply hnm
    intro p q hpq
    have := h (neg_le_neg hpq)
    simpa using this
  have hcomp := (tendsto_atTop_of_convex_not_antitone hconv' hna').comp
    Filter.tendsto_neg_atBot_atTop
  exact hcomp.congr (fun x => by simp)

section LocObj

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The fibrewise conditional-risk objective `w ↦ ∫⁻ ofReal (ρ (δ₀ x − w))` is convex:
convexity of `ρ` through the affine shift, pushed through `ENNReal.ofReal` and `∫⁻`. -/
private lemma locObj_convexOn (μ : Measure 𝓧) {ρ : ℝ → ℝ} (hρm : Measurable ρ)
    (hρ : ConvexOn ℝ Set.univ ρ) {δ₀ : 𝓧 → ℝ} (hδ₀ : Measurable δ₀) :
    ConvexOn ℝ≥0 Set.univ (fun w => ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - w)) ∂μ) := by
  refine ⟨convex_univ, fun a _ b _ u v hu hv huv => ?_⟩
  have huv' : (u : ℝ) + (v : ℝ) = 1 := by exact_mod_cast huv
  have hmeasA : Measurable (fun x => ENNReal.ofReal (ρ (δ₀ x - a))) :=
    ENNReal.measurable_ofReal.comp (hρm.comp (hδ₀.sub_const a))
  have hmeasB : Measurable (fun x => ENNReal.ofReal (ρ (δ₀ x - b))) :=
    ENNReal.measurable_ofReal.comp (hρm.comp (hδ₀.sub_const b))
  have hpoint : ∀ x, ENNReal.ofReal (ρ (δ₀ x - (u • a + v • b)))
      ≤ (u : ℝ≥0∞) * ENNReal.ofReal (ρ (δ₀ x - a)) +
        (v : ℝ≥0∞) * ENNReal.ofReal (ρ (δ₀ x - b)) := by
    intro x
    have hsplit : δ₀ x - (u • a + v • b)
        = (u : ℝ) • (δ₀ x - a) + (v : ℝ) • (δ₀ x - b) := by
      rw [NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      linear_combination (-(δ₀ x)) * huv'
    rw [hsplit]
    have hc := hρ.2 (Set.mem_univ (δ₀ x - a)) (Set.mem_univ (δ₀ x - b))
      u.coe_nonneg v.coe_nonneg huv'
    calc ENNReal.ofReal (ρ ((u : ℝ) • (δ₀ x - a) + (v : ℝ) • (δ₀ x - b)))
        ≤ ENNReal.ofReal ((u : ℝ) • ρ (δ₀ x - a) + (v : ℝ) • ρ (δ₀ x - b)) :=
          ENNReal.ofReal_le_ofReal hc
      _ ≤ ENNReal.ofReal ((u : ℝ) • ρ (δ₀ x - a)) + ENNReal.ofReal ((v : ℝ) • ρ (δ₀ x - b)) :=
          ENNReal.ofReal_add_le
      _ = (u : ℝ≥0∞) * ENNReal.ofReal (ρ (δ₀ x - a)) +
            (v : ℝ≥0∞) * ENNReal.ofReal (ρ (δ₀ x - b)) := by
          rw [smul_eq_mul, smul_eq_mul, ENNReal.ofReal_mul u.coe_nonneg,
            ENNReal.ofReal_mul v.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  calc ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - (u • a + v • b))) ∂μ
      ≤ ∫⁻ x, ((u : ℝ≥0∞) * ENNReal.ofReal (ρ (δ₀ x - a)) +
          (v : ℝ≥0∞) * ENNReal.ofReal (ρ (δ₀ x - b))) ∂μ := lintegral_mono hpoint
    _ = (u : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - a)) ∂μ +
          (v : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - b)) ∂μ := by
        rw [lintegral_add_left (hmeasA.const_mul _), lintegral_const_mul _ hmeasA,
          lintegral_const_mul _ hmeasB]
    _ = u • (∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - a)) ∂μ) +
          v • (∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - b)) ∂μ) := by
        rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]

/-- The fibrewise conditional-risk objective is lower semicontinuous in the shift: the
integrand is continuous in `w`, and `∫⁻` is lower semicontinuous under `liminf` (Fatou). -/
private lemma locObj_lowerSemicontinuous (μ : Measure 𝓧) {ρ : ℝ → ℝ} (hρc : Continuous ρ)
    {δ₀ : 𝓧 → ℝ} (hδ₀ : Measurable δ₀) :
    LowerSemicontinuous (fun w => ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - w)) ∂μ) := by
  intro w y hy
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  simp only [not_lt] at hcon
  obtain ⟨wseq, hwtend, hwle⟩ := exists_seq_forall_of_frequently hcon
  set g : ℕ → 𝓧 → ℝ≥0∞ := fun n x => ENNReal.ofReal (ρ (δ₀ x - wseq n)) with hgdef
  have hg_meas : ∀ n, Measurable (g n) := fun n =>
    ENNReal.measurable_ofReal.comp (hρc.measurable.comp (hδ₀.sub_const _))
  have hlim : ∀ x, Filter.Tendsto (fun n => g n x) Filter.atTop
      (𝓝 (ENNReal.ofReal (ρ (δ₀ x - w)))) := by
    intro x
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((hρc.tendsto _).comp (tendsto_const_nhds.sub hwtend))
  have key : ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - w)) ∂μ ≤ y := by
    have heq : (fun x => ENNReal.ofReal (ρ (δ₀ x - w)))
        = fun x => Filter.liminf (fun n => g n x) Filter.atTop := by
      funext x; exact ((hlim x).liminf_eq).symm
    rw [show (∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - w)) ∂μ)
        = ∫⁻ x, Filter.liminf (fun n => g n x) Filter.atTop ∂μ from by rw [heq]]
    refine le_trans (lintegral_liminf_le hg_meas) ?_
    refine Filter.liminf_le_of_le (h := fun b hb => ?_)
    obtain ⟨n, hn⟩ := (hb.and (Filter.Eventually.of_forall hwle)).exists
    exact le_trans hn.1 hn.2
  exact absurd key (not_le.mpr hy)

/-- The fibrewise conditional-risk objective is coercive (blows up at `±∞`): the loss `ρ`
tends to `+∞` at both ends (convex, non-monotone), so the integrand tends to `⊤` pointwise
and Fatou pushes the integral to `⊤`. -/
private lemma locObj_tendsto_top (μ : Measure 𝓧) [IsProbabilityMeasure μ] {ρ : ℝ → ℝ}
    (hρc : Continuous ρ) (hconv : ConvexOn ℝ Set.univ ρ)
    (hnotmono : ¬ Monotone ρ ∧ ¬ Antitone ρ) {δ₀ : 𝓧 → ℝ} (hδ₀ : Measurable δ₀) :
    Tendsto (fun w => ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - w)) ∂μ) (cocompact ℝ) (𝓝 ⊤) := by
  have hρtop : Tendsto ρ (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
    exact ⟨tendsto_atBot_of_convex_not_monotone hconv hnotmono.1,
      tendsto_atTop_of_convex_not_antitone hconv hnotmono.2⟩
  have hsub : ∀ c : ℝ, Tendsto (fun w => c - w) (cocompact ℝ) (cocompact ℝ) := by
    intro c
    rw [cocompact_eq_atBot_atTop]
    refine Filter.tendsto_sup.mpr ⟨?_, ?_⟩
    · refine Filter.Tendsto.mono_right ?_ le_sup_right
      exact (Filter.tendsto_atTop_add_const_left atBot c
        Filter.tendsto_neg_atBot_atTop).congr (fun w => by ring)
    · refine Filter.Tendsto.mono_right ?_ le_sup_left
      exact (Filter.tendsto_atBot_add_const_left atTop c
        Filter.tendsto_neg_atTop_atBot).congr (fun w => by ring)
  haveI : (cocompact ℝ).IsCountablyGenerated := by
    rw [cocompact_eq_atBot_atTop]; infer_instance
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro N
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  simp only [not_lt] at hcon
  obtain ⟨wseq, hwtend, hwle⟩ := exists_seq_forall_of_frequently hcon
  set g : ℕ → 𝓧 → ℝ≥0∞ := fun n x => ENNReal.ofReal (ρ (δ₀ x - wseq n)) with hgdef
  have hg_meas : ∀ n, Measurable (g n) := fun n =>
    ENNReal.measurable_ofReal.comp (hρc.measurable.comp (hδ₀.sub_const _))
  have hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 ⊤) := by
    intro x
    exact ENNReal.tendsto_ofReal_nhds_top.2 (hρtop.comp ((hsub (δ₀ x)).comp hwtend))
  have hkey : (⊤ : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
    calc (⊤ : ℝ≥0∞) = ∫⁻ _x : 𝓧, (⊤ : ℝ≥0∞) ∂μ := by rw [lintegral_const]; simp
      _ = ∫⁻ x, Filter.liminf (fun n => g n x) atTop ∂μ := by
          refine lintegral_congr fun x => ?_
          exact ((hlim x).liminf_eq).symm
      _ ≤ Filter.liminf (fun n => ∫⁻ x, g n x ∂μ) atTop := lintegral_liminf_le hg_meas
      _ ≤ (N : ℝ≥0∞) := by
          refine Filter.liminf_le_of_le (h := fun b hb => ?_)
          obtain ⟨n, hn⟩ := (hb.and (Filter.Eventually.of_forall hwle)).exists
          exact le_trans hn.1 hn.2
  exact absurd hkey (not_le.mpr ENNReal.coe_lt_top)

end LocObj

/-- **The minimum risk equivariant location estimator.** Let `δ₀` be a measurable
equivariant estimator with finite risk and let `v*` be a measurable function of the
differences which, in almost every fibre, minimizes the conditional expected loss
`E₀[ρ(δ₀(X) − v) | y]` over constant `v`. Then `δ₀ − v* ∘ diffs` is a minimum risk
equivariant estimator.

The two ingredients are the representation of the equivariant class as `δ₀ − v ∘ diffs`
and the fact that an integral is minimized by minimizing its integrand fibrewise. -/
theorem isLocMRE_of_conditional_min (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density, so the base member is a probability law
    [IsProbabilityMeasure (locationBase f)]
    (ρ : ℝ → ℝ)
    -- LEAN-ONLY: measurability of the loss; needed for the disintegration
    (hρ : Measurable ρ)
    {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference equivariant estimator, the caller's free choice
    (heq₀ : IsLocEquivariant δ₀)
    -- USER-INPUT: it has finite risk, so the conditional minimization is meaningful
    (hfin : locRisk f ρ δ₀ ≠ ∞)
    {vStar : (Fin m → ℝ) → ℝ}
    -- USER-INPUT: the fibrewise minimizer, supplied measurably by the caller
    (hvStar : Measurable vStar)
    -- USER-INPUT: `v*` minimizes the conditional expected loss in almost every fibre of
    -- the differences (the classical statement asks for every fibre)
    (hmin : ∀ᵐ y ∂((locationBase f).map diffs), ∀ w : ℝ,
      ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - vStar y))
          ∂(orbitCondKernel (locationBase f) diffs y) ≤
        ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - w))
          ∂(orbitCondKernel (locationBase f) diffs y)) :
    IsLocMRE f ρ (fun x => δ₀ x - vStar (diffs x)) := by
  refine ⟨hδ₀.sub (hvStar.comp measurable_diffs), ?_, ?_⟩
  · exact (isLocEquivariant_iff_exists_diffs_rep heq₀ _).mpr ⟨vStar, fun x => rfl⟩
  · intro δ' hδ'meas hδ'eq
    obtain ⟨v, hvmeas, hv⟩ :=
      (isLocEquivariant_iff_exists_diffs_rep_measurable heq₀ hδ₀ δ').mp ⟨hδ'meas, hδ'eq⟩
    have hFmeas : Measurable (fun p : ℝ × (Fin (m + 1) → ℝ) => δ₀ p.2 - p.1) :=
      (hδ₀.comp measurable_snd).sub measurable_fst
    have key := lintegral_le_of_condMinimizer (locationBase f) (Z := diffs)
      measurable_diffs (F := fun w x => δ₀ x - w) hFmeas (ρ := ρ) hρ
      (vStar := vStar) hvStar hmin (v := v) hvmeas
    have hrisk' : locRisk f ρ δ' =
        ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - v (diffs x))) ∂(locationBase f) := by
      unfold locRisk; exact lintegral_congr fun x => by rw [hv x]
    rw [hrisk']; unfold locRisk; exact key

/-- Analytic core: for a convex, non-monotone loss the fibrewise conditional risk
`w ↦ ∫⁻ x, ofReal (ρ (δ₀ x − w)) ∂(orbitCondKernel (locationBase f) diffs z)` is convex,
lower semicontinuous and coercive in `w`, so the measurable-argmin brick
`exists_measurable_argmin_of_convex` produces a measurable `v*` minimizing it in almost every
fibre. The finiteness point `fObj z 0 < ⊤` that the brick's convex form needs comes from the
finite reference risk via disintegration. -/
private lemma exists_measurable_condMinimizer_convex (f : (Fin (m + 1) → ℝ) → ℝ)
    [IsProbabilityMeasure (locationBase f)] {ρ : ℝ → ℝ} (hρ : Measurable ρ)
    (hconv : ConvexOn ℝ Set.univ ρ) (hnotmono : ¬ Monotone ρ ∧ ¬ Antitone ρ)
    {δ₀ : (Fin (m + 1) → ℝ) → ℝ} (hδ₀ : Measurable δ₀) (hfin : locRisk f ρ δ₀ ≠ ∞) :
    ∃ vStar : (Fin m → ℝ) → ℝ, Measurable vStar ∧
      ∀ᵐ y ∂((locationBase f).map diffs), ∀ w : ℝ,
        ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - vStar y))
            ∂(orbitCondKernel (locationBase f) diffs y) ≤
          ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - w))
            ∂(orbitCondKernel (locationBase f) diffs y) := by
  have hρc : Continuous ρ := (hconv.locallyLipschitz).continuous
  set fObj : (Fin m → ℝ) → ℝ → ℝ≥0∞ :=
    fun z w => ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - w))
      ∂(orbitCondKernel (locationBase f) diffs z) with hfObjdef
  -- (1) joint measurability of the objective through the fibre kernel
  have hmeas : Measurable (Function.uncurry fObj) := by
    have hf_meas : Measurable (fun p : ((Fin m → ℝ) × ℝ) × (Fin (m + 1) → ℝ) =>
        ENNReal.ofReal (ρ (δ₀ p.2 - p.1.2))) :=
      ENNReal.measurable_ofReal.comp (hρc.measurable.comp
        ((hδ₀.comp measurable_snd).sub (measurable_snd.comp measurable_fst)))
    set κ' : ProbabilityTheory.Kernel ((Fin m → ℝ) × ℝ) (Fin (m + 1) → ℝ) :=
      (orbitCondKernel (locationBase f) diffs).comap Prod.fst measurable_fst with hκ'
    have heq : Function.uncurry fObj
        = fun p : (Fin m → ℝ) × ℝ => ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - p.2)) ∂(κ' p) := by
      funext p
      rw [hκ', ProbabilityTheory.Kernel.comap_apply]
      simp only [Function.uncurry, hfObjdef]
    rw [heq]
    exact Measurable.lintegral_kernel_prod_right' (κ := κ') hf_meas
  -- (2)–(4) convexity / lower semicontinuity / coercivity of each fibre objective
  have hconvex : ∀ z, ConvexOn ℝ≥0 Set.univ (fObj z) := fun z =>
    locObj_convexOn _ hρ hconv hδ₀
  have hlsc : ∀ z, LowerSemicontinuous (fObj z) := fun z =>
    locObj_lowerSemicontinuous _ hρc hδ₀
  have hcoer : ∀ z, Tendsto (fObj z) (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞)) := fun z =>
    locObj_tendsto_top _ hρc hconv hnotmono hδ₀
  -- (5) finiteness at `0` for a.e. fibre, from the finite reference risk via disintegration
  have hint_meas : Measurable (fun z => ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x))
      ∂(orbitCondKernel (locationBase f) diffs z)) :=
    Measurable.lintegral_kernel_prod_right'
      (κ := orbitCondKernel (locationBase f) diffs)
      (ENNReal.measurable_ofReal.comp (hρc.measurable.comp (hδ₀.comp measurable_snd)))
  have hfin0 : ∀ᵐ z ∂((locationBase f).map diffs), fObj z 0 < ⊤ := by
    have hdis := lintegral_eq_lintegral_condDistrib (locationBase f) measurable_diffs
      (g := fun _z x => ENNReal.ofReal (ρ (δ₀ x)))
      (ENNReal.measurable_ofReal.comp (hρc.measurable.comp (hδ₀.comp measurable_snd)))
    have hne : (∫⁻ z, ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x))
        ∂(orbitCondKernel (locationBase f) diffs z) ∂((locationBase f).map diffs)) ≠ ⊤ := by
      rw [← hdis]; exact hfin
    filter_upwards [ae_lt_top hint_meas hne] with z hz
    have hz0 : fObj z 0 = ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x))
        ∂(orbitCondKernel (locationBase f) diffs z) := by simp only [hfObjdef, sub_zero]
    rw [hz0]; exact hz
  obtain ⟨vStar, hvStar_meas, hvStar_min⟩ :=
    exists_measurable_argmin_of_convex (μ := (locationBase f).map diffs) hmeas hlsc hconvex
      hcoer hfin0
  refine ⟨vStar, hvStar_meas, ?_⟩
  filter_upwards [hvStar_min] with z hz w
  show fObj z (vStar z) ≤ fObj z w
  rw [hz]; exact iInf_le _ w

/-- **Existence of a minimum risk equivariant estimator for a convex, non-monotone
loss.** For such a loss the fibrewise minimization always has a solution, and the
solution can be chosen measurably; uniqueness holds when the loss is strictly convex, a
refinement not formalized here. -/
theorem exists_isLocMRE_of_convex (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    (ρ : ℝ → ℝ)
    -- LEAN-ONLY: measurability of the loss
    (hρ : Measurable ρ)
    -- USER-INPUT: the loss is convex
    (hconv : ConvexOn ℝ Set.univ ρ)
    -- USER-INPUT: the loss is not monotone — for a convex loss this is exactly the
    -- condition making the fibrewise minimum attained rather than approached at `±∞`
    (hnotmono : ¬ Monotone ρ ∧ ¬ Antitone ρ)
    {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference equivariant estimator with finite risk
    (heq₀ : IsLocEquivariant δ₀)
    (hfin : locRisk f ρ δ₀ ≠ ∞) :
    ∃ δ, IsLocMRE f ρ δ := by
  obtain ⟨vStar, hvStar, hmin⟩ :=
    exists_measurable_condMinimizer_convex f hρ hconv hnotmono hδ₀ hfin
  exact ⟨_, isLocMRE_of_conditional_min f ρ hρ hδ₀ heq₀ hfin hvStar hmin⟩

/-- **Squared error: the minimum risk equivariant estimator subtracts the conditional
mean.** With `ρ(t) = t²` the fibrewise minimizer is the conditional expectation of the
reference estimator given the differences, so the minimum risk equivariant estimator is
`δ*(X) = δ₀(X) − E₀[δ₀(X) | Y]`. -/
theorem isLocMRE_sq_of_condMean (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference equivariant estimator with finite risk
    (heq₀ : IsLocEquivariant δ₀)
    (hfin : locRisk f (fun t : ℝ => t ^ 2) δ₀ ≠ ∞)
    -- USER-INPUT: the conditional mean exists in every fibre of the differences
    (hint : ∀ y, Integrable δ₀ (orbitCondKernel (locationBase f) diffs y)) :
    IsLocMRE f (fun t : ℝ => t ^ 2)
      (fun x => δ₀ x -
        ∫ z, δ₀ z ∂(orbitCondKernel (locationBase f) diffs (diffs x))) := by
  have hρmeas : Measurable (fun t : ℝ => t ^ 2) := by fun_prop
  set vStar : (Fin m → ℝ) → ℝ :=
    fun y => ∫ z, δ₀ z ∂(orbitCondKernel (locationBase f) diffs y) with hvStarDef
  have hvStar : Measurable vStar :=
    measurable_integral_orbitCondKernel (locationBase f) measurable_diffs hδ₀ hint
  have hmin : ∀ᵐ y ∂((locationBase f).map diffs), ∀ w : ℝ,
      ∫⁻ x, ENNReal.ofReal ((δ₀ x - vStar y) ^ 2)
          ∂(orbitCondKernel (locationBase f) diffs y) ≤
        ∫⁻ x, ENNReal.ofReal ((δ₀ x - w) ^ 2)
          ∂(orbitCondKernel (locationBase f) diffs y) := by
    refine ae_of_all _ fun y w => ?_
    exact lintegral_ofReal_sq_min hδ₀ w
  exact isLocMRE_of_conditional_min f (fun t => t ^ 2) hρmeas hδ₀ heq₀ hfin hvStar hmin

/-- **Scheffé-type stability of bounded test integrals.** If measurable densities `h n`
converge pointwise almost everywhere to `h₀` and all carry the same finite total mass, then
integrals against a bounded test function converge. Pointwise convergence alone is not
enough (no dominating function is available); the equal-mass hypothesis is what supplies
the missing uniform integrability, through the two one-sided defects `h₀ − h n` and
`h n − h₀`, which have equal integrals and tend to `0` by dominated convergence. -/
private lemma tendsto_lintegral_mul_of_tendsto_of_mass_eq
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {h : ℕ → α → ℝ≥0∞} {h₀ : α → ℝ≥0∞}
    (hmeas : ∀ n, Measurable (h n)) (hmeas₀ : Measurable h₀)
    (hmass : ∀ n, ∫⁻ x, h n x ∂ν = ∫⁻ x, h₀ x ∂ν)
    (hfin : ∫⁻ x, h₀ x ∂ν ≠ ∞)
    (hae : ∀ᵐ x ∂ν, Tendsto (fun n => h n x) atTop (𝓝 (h₀ x)))
    {ψ : α → ℝ≥0∞} (hψ : Measurable ψ) {K : ℝ≥0∞} (hKfin : K ≠ ∞) (hK : ∀ x, ψ x ≤ K) :
    Tendsto (fun n => ∫⁻ x, ψ x * h n x ∂ν) atTop (𝓝 (∫⁻ x, ψ x * h₀ x ∂ν)) := by
  have hlt : ∀ᵐ x ∂ν, h₀ x ≠ ∞ := (ae_lt_top hmeas₀ hfin).mono fun _ hx => hx.ne
  set d : ℕ → α → ℝ≥0∞ := fun n x => h₀ x - h n x with hd
  set e : ℕ → α → ℝ≥0∞ := fun n x => h n x - h₀ x with he
  have hdm : ∀ n, Measurable (d n) := fun n => hmeas₀.sub (hmeas n)
  have hem : ∀ n, Measurable (e n) := fun n => (hmeas n).sub hmeas₀
  -- (i) the defect integrates to `0`, by dominated convergence with dominating function `h₀`
  have hd0 : Tendsto (fun n => ∫⁻ x, d n x ∂ν) atTop (𝓝 0) := by
    have key := tendsto_lintegral_of_dominated_convergence (μ := ν) (F := d) (f := fun _ => 0)
      h₀ hdm (fun n => ae_of_all _ fun x => tsub_le_self) hfin ?_
    · simpa using key
    · filter_upwards [hae, hlt] with x hx hxfin
      simpa using ENNReal.Tendsto.sub tendsto_const_nhds hx (Or.inl hxfin)
  -- (ii) both one-sided defects have the same integral, since the masses agree
  have hmax : ∀ n x, h n x + d n x = h₀ x + e n x := by
    intro n x
    simp only [hd, he, add_tsub_eq_max, max_comm]
  have hde : ∀ n, ∫⁻ x, e n x ∂ν = ∫⁻ x, d n x ∂ν := by
    intro n
    have h1 : ∫⁻ x, (h n x + d n x) ∂ν = ∫⁻ x, (h₀ x + e n x) ∂ν :=
      lintegral_congr fun x => hmax n x
    rw [lintegral_add_left (hmeas n), lintegral_add_left hmeas₀, hmass n] at h1
    exact ((ENNReal.add_right_inj hfin).mp h1).symm
  -- (iii) a two-sided bound: `K` times the defect
  have hub : ∀ n, ∫⁻ x, ψ x * h n x ∂ν ≤ (∫⁻ x, ψ x * h₀ x ∂ν) + K * ∫⁻ x, d n x ∂ν := by
    intro n
    calc ∫⁻ x, ψ x * h n x ∂ν ≤ ∫⁻ x, (ψ x * h₀ x + K * e n x) ∂ν := by
          refine lintegral_mono fun x => ?_
          have hle : h n x ≤ h₀ x + e n x := by
            simp only [he, add_tsub_eq_max]; exact le_max_right _ _
          calc ψ x * h n x ≤ ψ x * (h₀ x + e n x) := by gcongr
            _ = ψ x * h₀ x + ψ x * e n x := mul_add _ _ _
            _ ≤ ψ x * h₀ x + K * e n x := by gcongr; exact hK x
      _ = (∫⁻ x, ψ x * h₀ x ∂ν) + K * ∫⁻ x, e n x ∂ν := by
          rw [lintegral_add_left (hψ.fun_mul hmeas₀), lintegral_const_mul _ (hem n)]
      _ = _ := by rw [hde n]
  have hlb : ∀ n, ∫⁻ x, ψ x * h₀ x ∂ν ≤ (∫⁻ x, ψ x * h n x ∂ν) + K * ∫⁻ x, d n x ∂ν := by
    intro n
    calc ∫⁻ x, ψ x * h₀ x ∂ν ≤ ∫⁻ x, (ψ x * h n x + K * d n x) ∂ν := by
          refine lintegral_mono fun x => ?_
          have hle : h₀ x ≤ h n x + d n x := by
            simp only [hd, add_tsub_eq_max]; exact le_max_right _ _
          calc ψ x * h₀ x ≤ ψ x * (h n x + d n x) := by gcongr
            _ = ψ x * h n x + ψ x * d n x := mul_add _ _ _
            _ ≤ ψ x * h n x + K * d n x := by gcongr; exact hK x
      _ = (∫⁻ x, ψ x * h n x ∂ν) + K * ∫⁻ x, d n x ∂ν := by
          rw [lintegral_add_left (hψ.fun_mul (hmeas n)), lintegral_const_mul _ (hdm n)]
  -- (iv) squeeze
  have hAfin : ∫⁻ x, ψ x * h₀ x ∂ν ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hKfin hfin) ?_
    calc ∫⁻ x, ψ x * h₀ x ∂ν ≤ ∫⁻ x, K * h₀ x ∂ν := by
          refine lintegral_mono fun x => ?_; gcongr; exact hK x
      _ = K * ∫⁻ x, h₀ x ∂ν := lintegral_const_mul _ hmeas₀
  have ht0 : Tendsto (fun n => K * ∫⁻ x, d n x ∂ν) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hd0 (Or.inr hKfin)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => (∫⁻ x, ψ x * h₀ x ∂ν) - K * ∫⁻ x, d n x ∂ν)
    (h := fun n => (∫⁻ x, ψ x * h₀ x ∂ν) + K * ∫⁻ x, d n x ∂ν) ?_ ?_ ?_ ?_
  · simpa using ENNReal.Tendsto.sub tendsto_const_nhds ht0 (Or.inl hAfin)
  · simpa using tendsto_const_nhds.add ht0
  · exact fun n => tsub_le_iff_right.mpr (hlb n)
  · exact fun n => hub n

/-- Translating an almost-everywhere statement on `Fin n → ℝ`; Lebesgue measure is
translation invariant, so null sets stay null. -/
private lemma ae_volume_translate {n : ℕ} (P : (Fin n → ℝ) → Prop) (a : Fin n → ℝ)
    (hP : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), P x) :
    ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), P (x + a) := by
  rw [ae_iff] at hP ⊢
  exact (measure_add_right_null volume a).mpr hP

/-- **A single observation and a bounded loss.** For one observation the equivariant
estimators are exactly `X − c`, so an MRE estimator exists as soon as
`c ↦ E₀[ρ(X − c)]` attains its infimum. That happens for a loss which is bounded, tends
to its bound at `±∞`, and is faced with an almost-everywhere continuous density — a case
where the loss need not be convex at all.

No finite-risk hypothesis is needed: a loss bounded by `M` gives every estimator risk at
most `M` under a probability law. -/
theorem exists_isLocMRE_of_bounded_loss (f : (Fin 1 → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    (ρ : ℝ → ℝ)
    -- LEAN-ONLY: measurability of the loss
    (hρ : Measurable ρ)
    {M : ℝ}
    -- USER-INPUT: the loss is nonnegative and bounded by `M`
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρM : ∀ t, ρ t ≤ M)
    -- USER-INPUT: the loss attains its bound in the limit at both ends
    (hatTop : Filter.Tendsto ρ Filter.atTop (nhds M))
    (hatBot : Filter.Tendsto ρ Filter.atBot (nhds M))
    -- USER-INPUT: the density is continuous almost everywhere
    (hcont : ∀ᵐ x ∂(volume : Measure (Fin 1 → ℝ)), ContinuousAt f x) :
    ∃ δ, IsLocMRE f ρ δ := by
  -- The equivariant class for a single observation is exactly `{x ↦ x 0 − c}` (step (7)),
  -- so the whole problem is the one-dimensional minimization of the shifted risk `G`.
  set G : ℝ → ℝ≥0∞ :=
    fun c => ∫⁻ x, ENNReal.ofReal (ρ (x 0 - c)) ∂(locationBase f) with hGdef
  have hπ : Measurable fun x : Fin 1 → ℝ => x 0 := measurable_pi_apply 0
  have hρmeas : ∀ c : ℝ, Measurable fun x : Fin 1 → ℝ => ENNReal.ofReal (ρ (x 0 - c)) :=
    fun c => ENNReal.measurable_ofReal.comp (hρ.comp (hπ.sub_const c))
  -- (1) the objective is bounded by the bound of the loss
  have hGle : ∀ c, G c ≤ ENNReal.ofReal M := by
    intro c
    calc G c ≤ ∫⁻ _x : Fin 1 → ℝ, ENNReal.ofReal M ∂(locationBase f) :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hρM _)
      _ = ENNReal.ofReal M := by simp
  -- (2) and tends to that bound at infinity
  have hρcocompact : Tendsto ρ (cocompact ℝ) (𝓝 M) := by
    rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]; exact ⟨hatBot, hatTop⟩
  have hsub : ∀ c : ℝ, Tendsto (fun w => c - w) (cocompact ℝ) (cocompact ℝ) := by
    intro c
    rw [cocompact_eq_atBot_atTop]
    refine Filter.tendsto_sup.mpr ⟨?_, ?_⟩
    · refine Filter.Tendsto.mono_right ?_ le_sup_right
      exact (Filter.tendsto_atTop_add_const_left atBot c
        Filter.tendsto_neg_atBot_atTop).congr (fun w => by ring)
    · refine Filter.Tendsto.mono_right ?_ le_sup_left
      exact (Filter.tendsto_atBot_add_const_left atTop c
        Filter.tendsto_neg_atTop_atBot).congr (fun w => by ring)
  haveI : (cocompact ℝ).IsCountablyGenerated := by
    rw [cocompact_eq_atBot_atTop]; infer_instance
  have hGtend : Tendsto G (cocompact ℝ) (𝓝 (ENNReal.ofReal M)) := by
    have key := tendsto_lintegral_filter_of_dominated_convergence
      (μ := locationBase f) (l := cocompact ℝ)
      (F := fun c (x : Fin 1 → ℝ) => ENNReal.ofReal (ρ (x 0 - c)))
      (f := fun _ : Fin 1 → ℝ => ENNReal.ofReal M)
      (fun _ => ENNReal.ofReal M)
      (Eventually.of_forall hρmeas)
      (Eventually.of_forall fun c => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal (hρM _))
      (by simp) (ae_of_all _ fun x =>
        (ENNReal.continuous_ofReal.tendsto _).comp (hρcocompact.comp (hsub (x 0))))
    simpa using key
  -- (3) an a.e.-continuous density is a.e. measurable; fix a measurable version
  have hfae : AEMeasurable f (volume : Measure (Fin 1 → ℝ)) := by
    have h1 : ContinuousOn f {x | ContinuousAt f x} := fun x hx => hx.continuousWithinAt
    have h2 := h1.aemeasurable (μ := (volume : Measure (Fin 1 → ℝ)))
      (IsGδ.setOf_continuousAt f).measurableSet
    have h3 : (volume : Measure (Fin 1 → ℝ)).restrict {x | ContinuousAt f x} = volume :=
      Measure.restrict_eq_self_of_ae_mem hcont
    rwa [h3] at h2
  set g : (Fin 1 → ℝ) → ℝ := hfae.mk f with hgdef
  have hgm : Measurable g := hfae.measurable_mk
  have hgd : Measurable fun x : Fin 1 → ℝ => ENNReal.ofReal (g x) :=
    ENNReal.measurable_ofReal.comp hgm
  have hfg : f =ᵐ[(volume : Measure (Fin 1 → ℝ))] g := hfae.ae_eq_mk
  have hbase : locationBase f = (volume : Measure (Fin 1 → ℝ)).withDensity
      fun x => ENNReal.ofReal (g x) := by
    unfold locationBase
    refine withDensity_congr_ae (hfg.mono fun x hx => ?_)
    show ENNReal.ofReal (f x) = ENNReal.ofReal (g x)
    rw [hx]
  have hmass1 : ∫⁻ x, ENNReal.ofReal (g x) ∂(volume : Measure (Fin 1 → ℝ)) = 1 := by
    have h := measure_univ (μ := locationBase f)
    rw [hbase, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  -- (4) move the shift onto the density
  have hGrep : ∀ c : ℝ, G c = ∫⁻ x, ENNReal.ofReal (ρ (x 0)) *
      ENNReal.ofReal (g (x + c • (1 : Fin 1 → ℝ))) ∂(volume : Measure (Fin 1 → ℝ)) := by
    intro c
    have h1 : G c = ∫⁻ x, ENNReal.ofReal (g x) * ENNReal.ofReal (ρ (x 0 - c))
        ∂(volume : Measure (Fin 1 → ℝ)) := by
      rw [hGdef]
      simp only []
      rw [hbase, lintegral_withDensity_eq_lintegral_mul _ hgd (hρmeas c)]
      rfl
    rw [h1, ← lintegral_add_right_eq_self
      (fun x : Fin 1 → ℝ => ENNReal.ofReal (g x) * ENNReal.ofReal (ρ (x 0 - c)))
      (c • (1 : Fin 1 → ℝ))]
    refine lintegral_congr fun x => ?_
    have hx0 : (x + c • (1 : Fin 1 → ℝ)) 0 - c = x 0 := by simp
    rw [hx0, mul_comm]
  -- (5) continuity, by the Scheffé-type stability lemma
  have hGcont : Continuous G := by
    rw [continuous_iff_seqContinuous]
    intro cs c₀ hcs
    have hshiftm : ∀ c : ℝ, Measurable fun x : Fin 1 → ℝ =>
        ENNReal.ofReal (g (x + c • (1 : Fin 1 → ℝ))) := fun c =>
      ENNReal.measurable_ofReal.comp (hgm.comp (measurable_id.add_const _))
    have hmassc : ∀ c : ℝ, ∫⁻ x, ENNReal.ofReal (g (x + c • (1 : Fin 1 → ℝ)))
        ∂(volume : Measure (Fin 1 → ℝ)) = 1 := by
      intro c
      rw [lintegral_add_right_eq_self (fun x : Fin 1 → ℝ => ENNReal.ofReal (g x))
        (c • (1 : Fin 1 → ℝ))]
      exact hmass1
    have hae : ∀ᵐ x ∂(volume : Measure (Fin 1 → ℝ)),
        Tendsto (fun n => ENNReal.ofReal (g (x + cs n • (1 : Fin 1 → ℝ)))) atTop
          (𝓝 (ENNReal.ofReal (g (x + c₀ • (1 : Fin 1 → ℝ))))) := by
      have hfg' : ∀ c : ℝ, ∀ᵐ x ∂(volume : Measure (Fin 1 → ℝ)),
          f (x + c • (1 : Fin 1 → ℝ)) = g (x + c • (1 : Fin 1 → ℝ)) := fun c =>
        ae_volume_translate _ _ hfg
      have hcont' : ∀ᵐ x ∂(volume : Measure (Fin 1 → ℝ)),
          ContinuousAt f (x + c₀ • (1 : Fin 1 → ℝ)) :=
        ae_volume_translate _ _ hcont
      filter_upwards [hcont', hfg' c₀, ae_all_iff.mpr fun n => hfg' (cs n)]
        with x hx hx₀ hxn
      have hpt : Tendsto (fun n => x + cs n • (1 : Fin 1 → ℝ)) atTop
          (𝓝 (x + c₀ • (1 : Fin 1 → ℝ))) := tendsto_const_nhds.add (hcs.smul_const _)
      have hlimf := hx.tendsto.comp hpt
      have hlimg : Tendsto (fun n => g (x + cs n • (1 : Fin 1 → ℝ))) atTop
          (𝓝 (g (x + c₀ • (1 : Fin 1 → ℝ)))) := by
        rw [← hx₀]
        exact hlimf.congr fun n => hxn n
      exact (ENNReal.continuous_ofReal.tendsto _).comp hlimg
    have key := tendsto_lintegral_mul_of_tendsto_of_mass_eq
      (ν := (volume : Measure (Fin 1 → ℝ)))
      (h := fun n x => ENNReal.ofReal (g (x + cs n • (1 : Fin 1 → ℝ))))
      (h₀ := fun x => ENNReal.ofReal (g (x + c₀ • (1 : Fin 1 → ℝ))))
      (fun n => hshiftm _) (hshiftm _)
      (fun n => by rw [hmassc, hmassc]) (by rw [hmassc]; exact ENNReal.one_ne_top) hae
      (ψ := fun x : Fin 1 → ℝ => ENNReal.ofReal (ρ (x 0)))
      (ENNReal.measurable_ofReal.comp (hρ.comp hπ))
      (K := ENNReal.ofReal M) ENNReal.ofReal_ne_top
      (fun x => ENNReal.ofReal_le_ofReal (hρM _))
    simpa only [Function.comp_def, hGrep] using key
  -- (6) the minimum is attained
  obtain ⟨c₁, hc₁⟩ : ∃ c, ∀ c', G c ≤ G c' := by
    by_cases hconstG : ∀ c, G c = ENNReal.ofReal M
    · exact ⟨0, fun c' => by rw [hconstG 0, hconstG c']⟩
    · obtain ⟨c₀, hc₀⟩ := not_forall.mp hconstG
      have hlt : G c₀ < ENNReal.ofReal M := lt_of_le_of_ne (hGle c₀) hc₀
      exact hGcont.exists_forall_le' c₀
        ((hGtend.eventually_const_lt hlt).mono fun c hc => hc.le)
  -- (7) assemble
  refine ⟨fun x => x 0 - c₁, hπ.sub_const c₁, ?_, ?_⟩
  · intro a x
    show (x + a • (1 : Fin 1 → ℝ)) 0 - c₁ = (x 0 - c₁) + a
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    ring
  · intro δ' _ hδ'eq
    set c := - δ' 0 with hc
    have hrep : ∀ x : Fin 1 → ℝ, δ' x = x 0 - c := by
      intro x
      have hx : ((0 : Fin 1 → ℝ) + (x 0) • (1 : Fin 1 → ℝ)) = x := by
        funext i; fin_cases i; simp
      have h2 := hδ'eq (x 0) (0 : Fin 1 → ℝ)
      rw [hx] at h2
      rw [h2, hc]; ring
    have hrisk : locRisk f ρ δ' = G c := by
      unfold locRisk
      exact lintegral_congr fun x => by rw [hrep x]
    show G c₁ ≤ locRisk f ρ δ'
    rw [hrisk]
    exact hc₁ _

end LocationMRE

end StatLean.PointEstimation
