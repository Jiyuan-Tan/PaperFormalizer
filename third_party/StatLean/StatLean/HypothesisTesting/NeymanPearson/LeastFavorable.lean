module
public import StatLean.HypothesisTesting.NeymanPearson.Lemma
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Least favorable distributions: reducing a composite hypothesis to a simple one

To test a composite hypothesis `H : {f_θ, θ ∈ ω}` against a simple alternative `g`, replace
`H` by the **simple** hypothesis `H_Λ` whose density is the mixture
$$ h_\Lambda(x) \;=\; \int_\omega f_\theta(x) \, d\Lambda(\theta) $$
over a prior `Λ` carried by `ω`. The fundamental lemma solves the mixed problem. If the
resulting most powerful test happens to keep size `≤ α` against **every** member of `ω`,
then it is most powerful for the original composite problem, and `Λ` is a *least
favorable* prior: no other prior makes the testing problem harder.

Contents:
* `mixtureMeasure μ f Λ` — the mixed hypothesis `H_Λ`;
* `maxPower P₀ G α` — the largest power against `G` available to a level-`α` test of `P₀`;
* `IsLeastFavorable` — `Λ` minimizes that quantity over priors carried by `ω`;
* `isMostPowerful_composite_of_leastFavorable` — the mixed-problem optimum solves the
  composite problem;
* `unique_mostPowerful_composite_of_leastFavorable` — the same transfer for uniqueness;
* `leastFavorable_max_power` — such a `Λ` is least favorable;
* `isMostPowerful_composite_of_npShape` — the practical sufficient condition: a
  likelihood-ratio test against the mixture, whose power is constant `= α` on a
  `Λ`-carrier `ω' ⊆ ω` and `≤ α` on all of `ω`, is most powerful.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.8 (Least Favorable Distributions), Theorem 3.8.1 and Corollary 3.8.1
(reduction of a composite null to a simple one via a least favorable distribution). (`TSH4
§3.8 Thm 3.8.1, Cor 3.8.1`.)

**Proof formalization notes.**
* The prior is carried as a measure `Λ : Measure Θ` on the parameter space together with
  `Λ ω = 1`, rather than as a measure on the subtype `ω`. This keeps `power P φ θ` and
  `IsLevel P ω φ α` usable verbatim, and makes "`Λ'` ranges over priors over `ω`" a plain
  side condition rather than a change of ambient type.
* Joint measurability of `(θ, x) ↦ f_θ(x)` is a genuine external input: it is what makes
  `h_Λ` measurable and lets Fubini give `∫ h_Λ dμ = 1`, i.e. that the mixture really is a
  probability density. It cannot be derived from measurability in `x` for each fixed `θ`.
* `maxPower` is a supremum of real numbers over a nonempty set bounded by `1` whenever
  `0 ≤ α`; for `α < 0` the competitor set is empty and the junk value is `0` (Mathlib's
  `sSup ∅`). The theorems below all carry `0 ≤ α`.
* Uniqueness is rendered as `μ`-a.e. equality of critical functions, which is the only
  sense in which a test is ever determined.
* The sufficient condition transcribes the printed pair of conditions faithfully: power
  exactly `α` at every point of the carrier `ω'`, and power at most `α` everywhere on `ω`
  (together these say the supremum over `ω` is attained and equals `α`, since `Λ ω' = 1`
  forces `ω'` to be nonempty).

**Bibliographic comments.** Reducing a composite hypothesis by averaging its members
against a weight function goes back to A. Wald ("Tests of statistical hypotheses
concerning several parameters when the number of observations is large," *Trans. Amer.
Math. Soc.* **54** (1943), 426–482), and the notion of a least favorable prior is central
to A. Wald, *Statistical Decision Functions* (Wiley, 1950). The existence theory and the
transfer results formalized here are due to E. L. Lehmann ("On the existence of least
favorable distributions," *Ann. Math. Statist.* **23** (1952), 408–416); the underlying
optimality of the likelihood-ratio test is J. Neyman and E. S. Pearson (*Phil. Trans. R.
Soc. Lond. A* **231** (1933), 289–337).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]

/-- The **mixed hypothesis** `H_Λ`: the measure whose density with respect to `μ` is the
mixture `h_Λ(x) = ∫ f_θ(x) dΛ(θ)` of the family against the prior. When the inner integral
fails to converge the Bochner integral returns `0` (Mathlib's junk convention); the
theorems below carry the joint-measurability hypothesis that rules this out.

The mixture density is written inline rather than named, because the same notion is already
introduced elsewhere in this area under the name `mixtureDensity`; the two should be
unified into a single shared declaration. -/
noncomputable def mixtureMeasure (μ : Measure 𝓧) (f : Θ → 𝓧 → ℝ) (Λ : Measure Θ) :
    Measure 𝓧 :=
  μ.withDensity fun x => ENNReal.ofReal (∫ θ, f θ x ∂Λ)

/-- The **maximum attainable power** against `G` among level-`α` tests of the simple
hypothesis `P₀`. For `0 ≤ α` the competitor set contains the constant test `φ ≡ α` and is
bounded above by `1`, so this is a genuine supremum; for `α < 0` the set is empty and the
value is the junk `sSup ∅ = 0`. -/
noncomputable def maxPower (P₀ G : Measure 𝓧) (α : ℝ) : ℝ :=
  sSup {b | ∃ φ, IsCriticalFn φ ∧ powerAgainst P₀ φ ≤ α ∧ powerAgainst G φ = b}

/-- `Λ` is **least favorable** at level `α` for testing the family `f` over `ω` against
`G`: no prior carried by `ω` makes less power available to a level-`α` test. -/
def IsLeastFavorable (μ : Measure 𝓧) (f : Θ → 𝓧 → ℝ) (G : Measure 𝓧) (ω : Set Θ)
    (α : ℝ) (Λ : Measure Θ) : Prop :=
  ∀ Λ' : Measure Θ, IsProbabilityMeasure Λ' → Λ' ω = 1 →
    maxPower (mixtureMeasure μ f Λ) G α ≤ maxPower (mixtureMeasure μ f Λ') G α

section Bridge

variable {μ : Measure 𝓧} {P : Θ → Measure 𝓧} {f : Θ → 𝓧 → ℝ}

/-- The power of a critical function against a density-carrying measure. Local copy of the
`powerAgainst_eq` lemma from `NeymanPearson.Lemma` (which is `private`). -/
private lemma lf_powerAgainst_eq {p : 𝓧 → ℝ} {Q : Measure 𝓧}
    (h : HasDensity μ p Q) (φ : 𝓧 → ℝ) :
    powerAgainst Q φ = ∫ x, φ x * p x ∂μ := by
  obtain ⟨hmeas, hnn, hQeq⟩ := h
  unfold powerAgainst
  rw [hQeq, integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hnn x)]; ring

/-- A density of a probability measure integrates to `1`. -/
private lemma lf_density_integral_one {p : 𝓧 → ℝ} {Q : Measure 𝓧} [IsProbabilityMeasure Q]
    (h : HasDensity μ p Q) : ∫ x, p x ∂μ = 1 := by
  have := lf_powerAgainst_eq h (fun _ => (1 : ℝ))
  simp only [one_mul] at this
  rw [← this]
  unfold powerAgainst
  rw [integral_const]; simp

/-- A density of a probability measure is integrable. -/
private lemma lf_density_integrable {p : 𝓧 → ℝ} {Q : Measure 𝓧} [IsProbabilityMeasure Q]
    (h : HasDensity μ p Q) : Integrable p μ := by
  obtain ⟨hmeas, hnn, hQeq⟩ := h
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  have h1 : (μ.withDensity fun x => ENNReal.ofReal (p x)) Set.univ = 1 := by
    rw [← hQeq]; exact measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [h1]; exact ENNReal.one_lt_top

/-- Integrability of the joint function `(x, θ) ↦ ψ x * f θ x` on `μ.prod Λ`, when each
`f θ` is a probability density and `ψ` is critical. The dominating bound is `|ψ x · f θ x|
≤ f θ x`, whose double integral is `∫ 1 dΛ = 1 < ∞`. -/
private lemma lf_integrable_prod [∀ θ, IsProbabilityMeasure (P θ)]
    (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    (Λ : Measure Θ) [IsProbabilityMeasure Λ] {ψ : 𝓧 → ℝ} (hψ : IsCriticalFn ψ)
    [SFinite μ] :
    Integrable (Function.uncurry fun x θ => ψ x * f θ x) (μ.prod Λ) := by
  have hjoint' : Measurable fun q : 𝓧 × Θ => ψ q.1 * f q.2 q.1 :=
    (hψ.1.comp measurable_fst).mul (hjoint.comp measurable_swap)
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x θ => ψ x * f θ x) (μ.prod Λ) :=
    hjoint'.aestronglyMeasurable
  rw [integrable_prod_iff' hmeas]
  refine ⟨Filter.Eventually.of_forall fun θ => ?_, ?_⟩
  · -- for each θ, `x ↦ ψ x * f θ x` is integrable
    simpa [Function.uncurry] using
      (lf_density_integrable (hf θ)).bdd_mul hψ.1.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hψ.2 x).1]; exact (hψ.2 x).2)
  · -- `θ ↦ ∫ ‖ψ x * f θ x‖ dμ` is integrable, since it is `≤ 1` and Λ is finite
    have hbound : ∀ θ, (∫ x, ‖Function.uncurry (fun x θ => ψ x * f θ x) (x, θ)‖ ∂μ)
        ≤ ∫ x, f θ x ∂μ := by
      intro θ
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (lf_density_integrable (hf θ)) (Filter.Eventually.of_forall fun x => ?_)
      simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      have h1 : |ψ x| ≤ 1 := by rw [abs_of_nonneg (hψ.2 x).1]; exact (hψ.2 x).2
      have hf0 : 0 ≤ f θ x := (hf θ).2.1 x
      calc |ψ x| * |f θ x| ≤ 1 * |f θ x| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = f θ x := by rw [one_mul, abs_of_nonneg hf0]
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun θ => ?_)
    · -- measurability of `θ ↦ ∫ ‖…‖ dμ`
      exact (hmeas.norm.prod_swap).integral_prod_right'
    · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact le_trans (hbound θ) (le_of_eq (lf_density_integral_one (hf θ)))

/-- **The mixture-Fubini bridge.** For any critical `ψ`, the power against the mixture of
the family over `Λ` equals the `Λ`-average of the power against each member. -/
private lemma lf_bridge [SFinite μ] [∀ θ, IsProbabilityMeasure (P θ)]
    (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    (Λ : Measure Θ) [IsProbabilityMeasure Λ] {ψ : 𝓧 → ℝ} (hψ : IsCriticalFn ψ) :
    powerAgainst (mixtureMeasure μ f Λ) ψ = ∫ θ, power P ψ θ ∂Λ := by
  have hmixnn : StronglyMeasurable fun x => ∫ θ, f θ x ∂Λ := by
    have h : StronglyMeasurable fun q : 𝓧 × Θ => f q.2 q.1 :=
      (hjoint.comp measurable_swap).stronglyMeasurable
    exact h.integral_prod_right'
  -- step 1: withDensity transfer
  unfold powerAgainst mixtureMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmixnn.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have hstep1 : (∫ x, (ENNReal.ofReal (∫ θ, f θ x ∂Λ)).toReal • ψ x ∂μ)
      = ∫ x, (∫ θ, ψ x * f θ x ∂Λ) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    have hnn : 0 ≤ ∫ θ, f θ x ∂Λ :=
      integral_nonneg fun θ => (hf θ).2.1 x
    rw [smul_eq_mul, ENNReal.toReal_ofReal hnn, mul_comm (∫ θ, f θ x ∂Λ) (ψ x),
      ← integral_const_mul (ψ x) (fun θ => f θ x)]
  rw [hstep1]
  -- step 2: Fubini swap. `integral_integral_swap` turns `∫ x, ∫ θ, … ∂Λ ∂μ` into
  -- `∫ θ, ∫ x, … ∂μ ∂Λ`.
  have hint := lf_integrable_prod (P := P) hf hjoint Λ hψ
  rw [integral_integral_swap (f := fun x θ => ψ x * f θ x) hint]
  -- step 3: per-θ density transfer
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only
  rw [← lf_powerAgainst_eq (hf θ) ψ]; rfl

/-- The power function `θ ↦ power P ψ θ` of a critical test is `Λ`-integrable. -/
private lemma lf_power_integrable [SFinite μ] [∀ θ, IsProbabilityMeasure (P θ)]
    (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    (Λ : Measure Θ) [IsProbabilityMeasure Λ] {ψ : 𝓧 → ℝ} (hψ : IsCriticalFn ψ) :
    Integrable (fun θ => power P ψ θ) Λ := by
  have hint := (lf_integrable_prod (P := P) hf hjoint Λ hψ).integral_prod_right
  refine hint.congr (Filter.Eventually.of_forall fun θ => ?_)
  simp only [Function.uncurry]
  rw [← lf_powerAgainst_eq (hf θ) ψ]; rfl

/-- If a critical `ψ` has level `α` on `ω` and the prior `Λ` is carried by `ω`, then the
`Λ`-average of the power is at most `α`; i.e. the mixed size is `≤ α`. -/
private lemma lf_bridge_le [SFinite μ] [∀ θ, IsProbabilityMeasure (P θ)]
    (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    {ω : Set Θ} (Λ : Measure Θ) [IsProbabilityMeasure Λ] (hΛ : Λ ω = 1)
    {α : ℝ} {ψ : 𝓧 → ℝ} (hψ : IsCriticalFn ψ) (hlevel : IsLevel P ω ψ α) :
    powerAgainst (mixtureMeasure μ f Λ) ψ ≤ α := by
  rw [lf_bridge (P := P) hf hjoint Λ hψ]
  have hpi : Integrable (fun θ => power P ψ θ) Λ :=
    lf_power_integrable (P := P) hf hjoint Λ hψ
  -- `{θ | power P ψ θ ≤ α}` is null-measurable and has full measure (it contains `ω`).
  have hnm : NullMeasurableSet {θ | power P ψ θ ≤ α} Λ :=
    nullMeasurableSet_le hpi.1.aemeasurable aemeasurable_const
  have hsub : ω ⊆ {θ | power P ψ θ ≤ α} := fun θ hθ => hlevel θ hθ
  have hfull : Λ {θ | power P ψ θ ≤ α} = 1 :=
    le_antisymm prob_le_one (hΛ ▸ measure_mono hsub)
  have hae : ∀ᵐ θ ∂Λ, power P ψ θ ≤ α := (mem_ae_iff_prob_eq_one₀ hnm).mpr hfull
  calc ∫ θ, power P ψ θ ∂Λ ≤ ∫ _θ, α ∂Λ := integral_mono_ae hpi (integrable_const α) hae
    _ = α := by rw [integral_const]; simp

/-- If a critical `ψ` has power exactly `α` on a `Λ`-carrier `ω'`, then the mixed size
equals `α`. -/
private lemma lf_bridge_eq [SFinite μ] [∀ θ, IsProbabilityMeasure (P θ)]
    (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    {ω' : Set Θ} (Λ : Measure Θ) [IsProbabilityMeasure Λ] (hΛ : Λ ω' = 1)
    {α : ℝ} {ψ : 𝓧 → ℝ} (hψ : IsCriticalFn ψ) (hsize : ∀ θ ∈ ω', power P ψ θ = α) :
    powerAgainst (mixtureMeasure μ f Λ) ψ = α := by
  rw [lf_bridge (P := P) hf hjoint Λ hψ]
  have hpi : Integrable (fun θ => power P ψ θ) Λ :=
    lf_power_integrable (P := P) hf hjoint Λ hψ
  have hnm : NullMeasurableSet {θ | power P ψ θ = α} Λ :=
    nullMeasurableSet_eq_fun hpi.1.aemeasurable aemeasurable_const
  have hsub : ω' ⊆ {θ | power P ψ θ = α} := fun θ hθ => hsize θ hθ
  have hfull : Λ {θ | power P ψ θ = α} = 1 :=
    le_antisymm prob_le_one (hΛ ▸ measure_mono hsub)
  have hae : ∀ᵐ θ ∂Λ, power P ψ θ = α := (mem_ae_iff_prob_eq_one₀ hnm).mpr hfull
  rw [integral_congr_ae hae, integral_const]; simp

/-- The mixture of probability densities is again a probability measure. -/
private lemma lf_isProbabilityMeasure_mixture [SFinite μ] [∀ θ, IsProbabilityMeasure (P θ)]
    (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    (Λ : Measure Θ) [IsProbabilityMeasure Λ] :
    IsProbabilityMeasure (mixtureMeasure μ f Λ) := by
  have hmixmeas : Measurable fun x => ∫ θ, f θ x ∂Λ :=
    (((hjoint.comp measurable_swap).stronglyMeasurable :
      StronglyMeasurable fun q : 𝓧 × Θ => f q.2 q.1).integral_prod_right').measurable
  constructor
  -- total mass = `∫⁻ ofReal (∫ f dΛ) dμ = ∫ (∫ f dΛ) dμ = ∫∫ f = 1`.
  have hmixnn : ∀ x, 0 ≤ ∫ θ, f θ x ∂Λ := fun x => integral_nonneg fun θ => (hf θ).2.1 x
  have hcrit : IsCriticalFn (fun _ : 𝓧 => (1 : ℝ)) :=
    ⟨measurable_const, fun _ => ⟨zero_le_one, le_refl 1⟩⟩
  have hbridge := lf_bridge (P := P) hf hjoint Λ hcrit
  have hrhs : (∫ θ, power P (fun _ : 𝓧 => (1 : ℝ)) θ ∂Λ) = 1 := by
    have : ∀ θ, power P (fun _ : 𝓧 => (1 : ℝ)) θ = 1 := by
      intro θ; unfold power; rw [integral_const]; simp
    simp only [this]; rw [integral_const]; simp
  have hlhs : powerAgainst (mixtureMeasure μ f Λ) (fun _ : 𝓧 => (1 : ℝ))
      = ((mixtureMeasure μ f Λ) Set.univ).toReal := by
    unfold powerAgainst; rw [integral_const]; simp [measureReal_def]
  rw [hlhs] at hbridge
  have hval : ((mixtureMeasure μ f Λ) Set.univ).toReal = 1 := by rw [hbridge, hrhs]
  have hmixint : Integrable (fun x => ∫ θ, f θ x ∂Λ) μ := by
    have := (lf_integrable_prod (P := P) hf hjoint Λ hcrit).integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.uncurry, one_mul]
  have hfin : (mixtureMeasure μ f Λ) Set.univ ≠ ⊤ := by
    unfold mixtureMeasure
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact ((hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hmixnn)).mp hmixint.2).ne
  rw [← ENNReal.ofReal_toReal hfin, hval, ENNReal.ofReal_one]

end Bridge

/-- **Transfer of optimality.** If a most powerful level-`α` test of the mixed hypothesis
`H_Λ` against `g` happens to have size at most `α` against every member of the composite
hypothesis, then it is most powerful for the composite problem itself. -/
theorem isMostPowerful_composite_of_leastFavorable
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the family under the null, given as probability measures
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: their densities with respect to `μ`
    (f : Θ → 𝓧 → ℝ) (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    -- USER-INPUT: joint measurability of `(θ, x) ↦ f_θ(x)` — what makes the mixture a
    -- density; not implied by measurability in `x` at each fixed `θ`
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    -- USER-INPUT: the simple alternative and its density
    (G : Measure 𝓧) [IsProbabilityMeasure G] (g : 𝓧 → ℝ) (hg : HasDensity μ g G)
    -- USER-INPUT: the null parameter set
    (ω : Set Θ)
    -- USER-INPUT: the prior, a probability measure carried by `ω`
    (Λ : Measure Θ) [IsProbabilityMeasure Λ] (hΛ : Λ ω = 1)
    -- USER-INPUT: nonnegative level
    {α : ℝ} (hα : 0 ≤ α) {φ : 𝓧 → ℝ}
    -- USER-INPUT: `φ` is most powerful for the *mixed* problem
    (hMP : IsMostPowerful (mixtureMeasure μ f Λ) G α φ)
    -- USER-INPUT: and it keeps level `α` against every member of the composite null —
    -- the hypothesis that makes the whole device work
    (hlevel : IsLevel P ω φ α) :
    IsCriticalFn φ ∧ IsLevel P ω φ α ∧
      ∀ ψ, IsCriticalFn ψ → IsLevel P ω ψ α → powerAgainst G ψ ≤ powerAgainst G φ := by
  refine ⟨hMP.1, hlevel, fun ψ hψ hψlevel => ?_⟩
  -- The competitor `ψ` keeps mixed size `≤ α` by the bridge, so mixed optimality applies.
  have hmixed : powerAgainst (mixtureMeasure μ f Λ) ψ ≤ α :=
    lf_bridge_le (P := P) hf hjoint Λ hΛ hψ hψlevel
  exact hMP.2.2 ψ hψ hmixed

/-- **Transfer of uniqueness.** Under the hypotheses above, if the mixed problem has an
essentially unique most powerful level-`α` test, then so does the composite problem, with
the same solution. -/
theorem unique_mostPowerful_composite_of_leastFavorable
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the family under the null and its densities
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → 𝓧 → ℝ) (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    -- USER-INPUT: joint measurability of the family
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    -- USER-INPUT: the simple alternative and its density
    (G : Measure 𝓧) [IsProbabilityMeasure G] (g : 𝓧 → ℝ) (hg : HasDensity μ g G)
    -- USER-INPUT: the null parameter set and the prior carried by it
    (ω : Set Θ) (Λ : Measure Θ) [IsProbabilityMeasure Λ] (hΛ : Λ ω = 1)
    -- USER-INPUT: nonnegative level
    {α : ℝ} (hα : 0 ≤ α) {φ : 𝓧 → ℝ}
    -- USER-INPUT: `φ` is most powerful for the mixed problem, and keeps level on `ω`
    (hMP : IsMostPowerful (mixtureMeasure μ f Λ) G α φ)
    (hlevel : IsLevel P ω φ α)
    -- USER-INPUT: essential uniqueness for the mixed problem — the printed hypothesis
    (huniq : ∀ ψ, IsMostPowerful (mixtureMeasure μ f Λ) G α ψ → ψ =ᵐ[μ] φ) :
    ∀ ψ, IsCriticalFn ψ → IsLevel P ω ψ α →
      (∀ χ, IsCriticalFn χ → IsLevel P ω χ α → powerAgainst G χ ≤ powerAgainst G ψ) →
      ψ =ᵐ[μ] φ := by
  intro ψ hψ hψlevel hψopt
  -- `φ` is most powerful for the composite problem (Theorem 1 above).
  have hφcomp := isMostPowerful_composite_of_leastFavorable μ P f hf hjoint G g hg ω Λ hΛ hα
    hMP hlevel
  -- `power G ψ = power G φ`: each dominates the other among composite-level tests.
  have h1 : powerAgainst G ψ ≤ powerAgainst G φ := hφcomp.2.2 ψ hψ hψlevel
  have h2 : powerAgainst G φ ≤ powerAgainst G ψ := hψopt φ hMP.1 hlevel
  have hpow : powerAgainst G ψ = powerAgainst G φ := le_antisymm h1 h2
  -- `ψ` is most powerful for the mixed problem, so uniqueness applies.
  refine huniq ψ ⟨hψ, lf_bridge_le (P := P) hf hjoint Λ hΛ hψ hψlevel, fun χ hχ hχmix => ?_⟩
  rw [hpow]
  exact hMP.2.2 χ hχ hχmix

/-- **The prior is least favorable.** A prior whose mixed-problem optimum keeps level `α`
against the whole composite null minimizes the power available against the alternative. -/
theorem leastFavorable_max_power
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the family under the null and its densities
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → 𝓧 → ℝ) (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    -- USER-INPUT: joint measurability of the family
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    -- USER-INPUT: the simple alternative and its density
    (G : Measure 𝓧) [IsProbabilityMeasure G] (g : 𝓧 → ℝ) (hg : HasDensity μ g G)
    -- USER-INPUT: the null parameter set and the prior carried by it
    (ω : Set Θ) (Λ : Measure Θ) [IsProbabilityMeasure Λ] (hΛ : Λ ω = 1)
    -- USER-INPUT: nonnegative level
    {α : ℝ} (hα : 0 ≤ α) {φ : 𝓧 → ℝ}
    -- USER-INPUT: `φ` is most powerful for the mixed problem, and keeps level on `ω`
    (hMP : IsMostPowerful (mixtureMeasure μ f Λ) G α φ)
    (hlevel : IsLevel P ω φ α) :
    IsLeastFavorable μ f G ω α Λ := by
  -- `powerAgainst G φ` is a common value: it is `maxPower` for `Λ` and a lower bound for
  -- any `Λ'` carried by `ω`.
  -- The competitor set of any `maxPower _ G α` is bounded above by `1`.
  have hbdd : ∀ Q : Measure 𝓧,
      BddAbove {b | ∃ ψ, IsCriticalFn ψ ∧ powerAgainst Q ψ ≤ α ∧ powerAgainst G ψ = b} := by
    intro Q
    refine ⟨1, fun b hb => ?_⟩
    obtain ⟨ψ, hψ, _, hbeq⟩ := hb
    rw [← hbeq]
    calc powerAgainst G ψ = ∫ x, ψ x ∂G := rfl
      _ ≤ ∫ _x, (1 : ℝ) ∂G :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => (hψ.2 x).1)
            (integrable_const 1) (Filter.Eventually.of_forall fun x => (hψ.2 x).2)
      _ = 1 := by rw [integral_const]; simp
  -- `maxPower (...Λ) G α = powerAgainst G φ`.
  have hmaxΛ : maxPower (mixtureMeasure μ f Λ) G α = powerAgainst G φ := by
    apply le_antisymm
    · refine csSup_le ⟨powerAgainst G φ, φ, hMP.1, hMP.2.1, rfl⟩ ?_
      rintro b ⟨ψ, hψ, hψsize, rfl⟩
      exact hMP.2.2 ψ hψ hψsize
    · exact le_csSup (hbdd _) ⟨φ, hMP.1, hMP.2.1, rfl⟩
  intro Λ' _ hΛ'
  rw [hmaxΛ]
  -- `φ` is a level-`α` competitor for the `Λ'`-mixture, hence its power is `≤ maxPower(Λ')`.
  refine le_csSup (hbdd _) ⟨φ, hMP.1, ?_, rfl⟩
  exact lf_bridge_le (P := P) hf hjoint Λ' hΛ' hMP.1 hlevel

/-- **The practical sufficient condition.** Let `Λ` be a prior carried by a subset
`ω' ⊆ ω` with `Λ ω' = 1`, and let `φ` be a likelihood-ratio test of the mixture density
against `g` at some threshold `k`. If the power of `φ` is exactly `α` at every point of
`ω'` and at most `α` on all of `ω`, then `φ` is most powerful at level `α` for the
composite problem. -/
theorem isMostPowerful_composite_of_npShape
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the family under the null and its densities
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → 𝓧 → ℝ) (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    -- USER-INPUT: joint measurability of the family
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    -- USER-INPUT: the simple alternative and its density
    (G : Measure 𝓧) [IsProbabilityMeasure G] (g : 𝓧 → ℝ) (hg : HasDensity μ g G)
    -- USER-INPUT: the null parameter set, and a `Λ`-carrier inside it
    (ω ω' : Set Θ) (hω' : ω' ⊆ ω)
    -- USER-INPUT: the prior, carried by `ω'`
    (Λ : Measure Θ) [IsProbabilityMeasure Λ] (hΛ : Λ ω' = 1)
    -- USER-INPUT: nonnegative level, threshold, and the candidate test
    {α : ℝ} (hα : 0 ≤ α) {k : ℝ≥0∞} {φ : 𝓧 → ℝ} (hφ : IsCriticalFn φ)
    -- USER-INPUT: `φ` is a likelihood-ratio test of the mixture against the alternative
    (hshape : HasNPShape μ (fun x => ∫ θ, f θ x ∂Λ) g k φ)
    -- USER-INPUT: its power is exactly `α` on the carrier — first half of the printed
    -- condition; together with `Λ ω' = 1` this forces `ω'` to be nonempty
    (hsize : ∀ θ ∈ ω', power P φ θ = α)
    -- USER-INPUT: and at most `α` on the whole null — second half (the supremum over `ω`
    -- is attained on `ω'` and equals `α`)
    (hlevel : IsLevel P ω φ α) :
    IsCriticalFn φ ∧ IsLevel P ω φ α ∧
      ∀ ψ, IsCriticalFn ψ → IsLevel P ω ψ α → powerAgainst G ψ ≤ powerAgainst G φ := by
  -- The mixture measure carries the mixture density with respect to `μ`.
  have hmixmeas : Measurable fun x => ∫ θ, f θ x ∂Λ :=
    (((hjoint.comp measurable_swap).stronglyMeasurable :
      StronglyMeasurable fun q : 𝓧 × Θ => f q.2 q.1).integral_prod_right').measurable
  have h₀ : HasDensity μ (fun x => ∫ θ, f θ x ∂Λ) (mixtureMeasure μ f Λ) :=
    ⟨hmixmeas, fun x => integral_nonneg fun θ => (hf θ).2.1 x, rfl⟩
  -- Its size equals `α` (bridge + power exactly `α` on the carrier `ω'`).
  have hsize' : powerAgainst (mixtureMeasure μ f Λ) φ = α :=
    lf_bridge_eq (P := P) hf hjoint Λ hΛ hφ hsize
  -- Hence `φ` is most powerful for the mixed problem by the fundamental lemma.
  haveI : IsProbabilityMeasure (mixtureMeasure μ f Λ) :=
    lf_isProbabilityMeasure_mixture (P := P) hf hjoint Λ
  have hMP : IsMostPowerful (mixtureMeasure μ f Λ) G α φ :=
    isMostPowerful_of_npShape μ (mixtureMeasure μ f Λ) G h₀ hg hφ hsize' hshape
  -- `Λ` is also carried by `ω` since `ω' ⊆ ω`.
  have hΛω : Λ ω = 1 := le_antisymm prob_le_one (hΛ ▸ measure_mono hω')
  -- Transfer via Theorem 1.
  exact isMostPowerful_composite_of_leastFavorable μ P f hf hjoint G g hg ω Λ hΛω hα hMP hlevel

end StatLean.HypothesisTesting
