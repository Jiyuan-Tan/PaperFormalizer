module
public import StatLean.HypothesisTesting.Invariance.Admissibility
public import StatLean.Bayesian.Conjugacy.NormalNormal
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Admissibility via unique Bayes solutions, and the Gaussian scale-mixture device

A general decision-theoretic route to admissibility is to exhibit a procedure as the
**unique Bayes solution** of some prior problem. For testing, the prior problem is a pair
of priors — one carried by the null class, one by the alternative class — under 0–1 loss.
Averaging the two families produces two mixture densities
$$ h_i(x) \;=\; \int f_\theta(x)\,d\Lambda_i(\theta), \qquad i = 0, 1, $$
and the Bayes test rejects where `h₁ ≥ k h₀`. This is a Neyman–Pearson test for the simple
problem `h₀` versus `h₁`; when the boundary `{h₁ = k h₀}` is null, that test is unique, and
uniqueness upgrades directly to admissibility of the original test. If moreover the prior
on the null class concentrates on the parameters where the size `α` is attained, the
sharper `α`-admissibility follows. Everything applies verbatim to any subclass of
alternatives carrying the alternative prior.

The second half of the file records the device that makes the method work in normal
problems with **nuisance means**. A Gaussian location family with a fixed variance `σ²`,
mixed over its mean by a suitable prior, reproduces a centred Gaussian of any larger
variance `M²`; choosing `M²` above all the variances in play makes the contribution of the
nuisance means to the likelihood ratio cancel, so that the ratio reduces to the one
computed with the means known.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 6 (Invariance), §6.7
(Admissibility), Theorem 6.7.2 (a unique Bayes test is admissible) and Lemma 6.7.1 (the
Gaussian scale-mixture integral identity). (`TSH4 §6.7 Thm 6.7.2, Lem 6.7.1`.)

**Main results.**
* `mixtureDensity`, `bayesTest` — the two-prior mixture densities and the nonrandomized
  Bayes test;
* `bayesTest_isDAdmissible`, `bayesTest_isAlphaAdmissible` — admissibility of the Bayes
  test against the alternative class;
* `bayesTest_admissible_of_subset` — the same conclusions against any subclass carrying
  the alternative prior;
* `exists_gaussian_scale_mixture` — the mixing identity producing a centred Gaussian of
  prescribed larger variance.

**Proof formalization notes.**
* The boundary condition is written division-free as `μ {x | h₁ x = k * h₀ x} = 0`; with
  the `θ`-free support hypothesis this is the same as the vanishing of the set where the
  likelihood ratio equals `k`, and it avoids junk values of division.
* The support hypothesis (`hsupp`) is the source's "the set `{x : f_θ(x) > 0}` does not
  depend on `θ`"; the joint measurability of `(θ, x) ↦ f_θ(x)` is what makes the mixture
  densities measurable.
* The priors are probability measures on the parameter space with `Λ₀` carried by the null
  class and `Λ₁` by the alternative class, transcribing `Λ₀(Θ_H) = Λ₁(Θ_K) = 1`.
* `bayesTest` is nonrandomized by construction, matching the source: randomized
  competitors are allowed, but the Bayes test itself must be an indicator for the
  uniqueness argument to apply.
* `exists_gaussian_scale_mixture` is stated in two equivalent readings: the pointwise
  density identity of the source, and the measure-level mixture identity. The intended
  tool for the construction (the mixing prior is itself centred Gaussian, of variance
  `M² − σ²`) is the normal–normal conjugacy already developed in `StatLean.Bayesian`.
* Positivity `σ² ≠ 0` is required for the Gaussian density to be the nondegenerate one;
  the source's `σ²` is a genuine variance.

**Bibliographic comments.** Exhibiting a test as a unique Bayes solution as a route to
admissibility, and the limiting-prior technique behind the normal examples, are due to
C. Stein ("The admissibility of Hotelling's $T^2$-test," *Ann. Math. Statist.* **27**
(1956), 616–623) and A. Birnbaum ("Characterizations of complete classes of tests of some
multiparametric hypotheses, with applications to likelihood ratio tests," *Ann. Math.
Statist.* **26** (1955), 21–36); the corresponding complete-class results for the
multivariate exponential family are due to K. Matthes and D. R. Truax ("Tests of composite
hypotheses for the multivariate exponential family," *Ann. Math. Statist.* **38** (1967),
681–697). The admissibility of the one- and two-sided $t$-tests against all invariant
classes of alternatives, obtained by approximating the improper uniform prior on
$\log\sigma$, is due to E. L. Lehmann and C. Stein (1953), extending their earlier joint
work (*Ann. Math. Statist.* **20** (1949), 28–45). The underlying optimality criterion is
that of J. Neyman and E. S. Pearson (*Phil. Trans. R. Soc. A* **231** (1933), 289–337).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

/-! ## The two-prior Bayes test -/

section Bayes

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace Θ]

/-- The **mixture density** of a dominated family against a prior:
`h(x) = ∫ f_θ(x) dΛ(θ)`. -/
noncomputable def mixtureDensity (f : Θ → 𝓧 → ℝ) (Λ : Measure Θ) (x : 𝓧) : ℝ :=
  ∫ θ, f θ x ∂Λ

/-- The **nonrandomized Bayes test** for the two-prior 0–1-loss problem with threshold
`k`: reject exactly where the alternative mixture density is at least `k` times the null
mixture density. -/
noncomputable def bayesTest (h₀ h₁ : 𝓧 → ℝ) (k : ℝ) : 𝓧 → ℝ :=
  fun x => if k * h₀ x ≤ h₁ x then 1 else 0

/-- A `[-1,1]`-valued measurable function is integrable against a finite measure. -/
private lemma bayes_bounded_integrable {ν : Measure 𝓧} [IsFiniteMeasure ν]
    {g : 𝓧 → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) : Integrable g ν :=
  (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)

/-- With a parameter-free support, the members of a dominated family are mutually absolutely
continuous. -/
private lemma bayes_ac {P : Θ → Measure 𝓧} {μ : Measure 𝓧} {f : Θ → 𝓧 → ℝ}
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2) (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    (hsupp : ∀ (θ θ' : Θ) (x : 𝓧), 0 < f θ x ↔ 0 < f θ' x) (θ θ' : Θ) : P θ ≪ P θ' := by
  have hmθ : Measurable fun x => ENNReal.ofReal (f θ x) :=
    (hjoint.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hmθ' : Measurable fun x => ENNReal.ofReal (f θ' x) :=
    (hjoint.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [hdens θ', withDensity_apply _ hs, setLIntegral_eq_zero_iff hs hmθ'] at hs0
  rw [hdens θ, withDensity_apply _ hs, setLIntegral_eq_zero_iff hs hmθ]
  filter_upwards [hs0] with x hx hxs
  have hx0 := hx hxs
  simp only [ENNReal.ofReal_eq_zero] at hx0 ⊢
  have hf'0 : ¬ (0 < f θ' x) := not_lt.mpr hx0
  rw [← hsupp θ θ' x] at hf'0
  exact not_lt.mp hf'0

/-- The mixture density is a.e.-strongly measurable. -/
private lemma mixtureDensity_aestronglyMeasurable {f : Θ → 𝓧 → ℝ}
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2) {Λ : Measure Θ} [SFinite Λ]
    {μ : Measure 𝓧} : AEStronglyMeasurable (mixtureDensity f Λ) μ := by
  have h : StronglyMeasurable (Function.uncurry fun (x : 𝓧) (θ : Θ) => f θ x) :=
    (hjoint.comp measurable_swap).stronglyMeasurable
  exact (h.integral_prod_right (ν := Λ)).aestronglyMeasurable

/-- The mixture density of a probability model against a prior is integrable (total mass one). -/
private lemma bayes_mix_integrable {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {f : Θ → 𝓧 → ℝ} {Λ : Measure Θ} [IsProbabilityMeasure Λ]
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2) (hfnonneg : ∀ θ x, 0 ≤ f θ x) :
    Integrable (mixtureDensity f Λ) μ := by
  have hmass : ∀ θ, ∫⁻ x, ENNReal.ofReal (f θ x) ∂μ = 1 := by
    intro θ
    have h2 : (P θ) Set.univ = 1 := measure_univ
    rwa [hdens θ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h2
  refine ⟨mixtureDensity_aestronglyMeasurable hjoint, ?_⟩
  show ∫⁻ x, ‖mixtureDensity f Λ x‖ₑ ∂μ < ∞
  refine lt_of_le_of_lt ?_ ENNReal.one_lt_top
  have hle : ∀ x, ‖mixtureDensity f Λ x‖ₑ ≤ ∫⁻ θ, ENNReal.ofReal (f θ x) ∂Λ := by
    intro x
    simp only [mixtureDensity]
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun θ => hfnonneg θ x),
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun θ => hfnonneg θ x)
        ((hjoint.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)]
    exact ENNReal.ofReal_toReal_le
  calc ∫⁻ x, ‖mixtureDensity f Λ x‖ₑ ∂μ
      ≤ ∫⁻ x, ∫⁻ θ, ENNReal.ofReal (f θ x) ∂Λ ∂μ := lintegral_mono hle
    _ = ∫⁻ θ, ∫⁻ x, ENNReal.ofReal (f θ x) ∂μ ∂Λ :=
        lintegral_lintegral_swap ((hjoint.comp measurable_swap).ennreal_ofReal).aemeasurable
    _ = ∫⁻ _θ, 1 ∂Λ := lintegral_congr fun θ => hmass θ
    _ = 1 := by rw [lintegral_const, one_mul, measure_univ]

/-- **Fubini for the mixture density**: integrating a bounded test against the mixture density is
the same as averaging its power over the prior. -/
private lemma bayes_fubini_mix {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {f : Θ → 𝓧 → ℝ} {Λ : Measure Θ} [IsProbabilityMeasure Λ]
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2) (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    {g : 𝓧 → ℝ} (hg : Measurable g) (hgb : ∀ x, |g x| ≤ 1) :
    ∫ x, g x * mixtureDensity f Λ x ∂μ = ∫ θ, (∫ x, g x ∂(P θ)) ∂Λ := by
  -- each `f θ` has unit mass
  have hmass : ∀ θ, ∫⁻ x, ENNReal.ofReal (f θ x) ∂μ = 1 := by
    intro θ
    have h2 : (P θ) Set.univ = 1 := measure_univ
    rwa [hdens θ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h2
  -- the joint density has unit mass, hence is integrable
  have hfInt : Integrable (fun q : Θ × 𝓧 => f q.1 q.2) (Λ.prod μ) := by
    refine ⟨hjoint.aestronglyMeasurable, ?_⟩
    have henorm : (fun q : Θ × 𝓧 => ‖f q.1 q.2‖ₑ)
        = fun q => ENNReal.ofReal (f q.1 q.2) := by
      funext q; rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (hfnonneg _ _)]
    have : ∫⁻ q : Θ × 𝓧, ‖f q.1 q.2‖ₑ ∂(Λ.prod μ) = 1 := by
      rw [henorm, lintegral_prod _ (hjoint.ennreal_ofReal).aemeasurable]
      calc ∫⁻ θ, ∫⁻ x, ENNReal.ofReal (f θ x) ∂μ ∂Λ
          = ∫⁻ _θ, 1 ∂Λ := by exact lintegral_congr fun θ => hmass θ
        _ = 1 := by rw [lintegral_const, one_mul, measure_univ]
    show ∫⁻ q : Θ × 𝓧, ‖f q.1 q.2‖ₑ ∂(Λ.prod μ) < ∞
    rw [this]; exact ENNReal.one_lt_top
  -- dominate `g·f` by `f`
  have hFInt : Integrable (Function.uncurry fun θ x => g x * f θ x) (Λ.prod μ) := by
    refine hfInt.mono' ((hg.comp measurable_snd).mul hjoint).aestronglyMeasurable ?_
    refine ae_of_all _ fun q => ?_
    simp only [Function.uncurry, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hfnonneg _ _)]
    exact mul_le_of_le_one_left (hfnonneg q.1 q.2) (hgb q.2)
  -- assemble
  have hswap := integral_integral_swap hFInt
  have hleft : ∫ x, g x * mixtureDensity f Λ x ∂μ
      = ∫ x, ∫ θ, g x * f θ x ∂Λ ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [mixtureDensity]
    rw [integral_const_mul]
  have hright : ∀ θ, ∫ x, g x * f θ x ∂μ = ∫ x, g x ∂(P θ) := by
    intro θ
    have hmθ : Measurable fun x => ENNReal.ofReal (f θ x) :=
      (hjoint.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
    rw [hdens θ, integral_withDensity_eq_integral_toReal_smul hmθ
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hfnonneg θ x), smul_eq_mul]
    ring
  rw [hleft, ← hswap]
  exact integral_congr_ae (ae_of_all _ fun θ => hright θ)

/-- The power function `θ ↦ ∫ g dP_θ` of a bounded measurable test is measurable in the
parameter (through the joint density). -/
private lemma bayes_power_measurable {P : Θ → Measure 𝓧} {μ : Measure 𝓧} [SigmaFinite μ]
    {f : Θ → 𝓧 → ℝ}
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2) (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    {g : 𝓧 → ℝ} (hg : Measurable g) : Measurable fun θ => power P g θ := by
  have heq : (fun θ => power P g θ) = fun θ => ∫ x, g x * f θ x ∂μ := by
    funext θ
    have hmθ : Measurable fun x => ENNReal.ofReal (f θ x) :=
      (hjoint.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
    simp only [power]
    rw [hdens θ, integral_withDensity_eq_integral_toReal_smul hmθ
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hfnonneg θ x), smul_eq_mul]; ring
  rw [heq]
  have hsm : StronglyMeasurable (Function.uncurry fun (θ : Θ) (x : 𝓧) => g x * f θ x) := by
    change StronglyMeasurable fun p : Θ × 𝓧 => g p.2 * f p.1 p.2
    exact ((hg.comp measurable_snd).mul hjoint).stronglyMeasurable
  exact (hsm.integral_prod_right (ν := μ)).measurable

/-- **Core of the Bayes admissibility arguments.** Given the alternative-side domination
pointwise on `Θ_K` and the null-side domination `Λ₀`-almost everywhere, the competitor has
the same power function as the Bayes test everywhere. -/
private lemma bayes_admissible_core {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {f : Θ → 𝓧 → ℝ} {Λ₀ Λ₁ : Measure Θ}
    [IsProbabilityMeasure Λ₀] [IsProbabilityMeasure Λ₁] {Θ_K : Set Θ} {k : ℝ}
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2) (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    (hsupp : ∀ (θ θ' : Θ) (x : 𝓧), 0 < f θ x ↔ 0 < f θ' x)
    (hΘK : MeasurableSet Θ_K) (hΛ₁ : Λ₁ Θ_K = 1)
    (hbdry : μ {x | mixtureDensity f Λ₁ x = k * mixtureDensity f Λ₀ x} = 0)
    {φ : 𝓧 → ℝ} (hφ : IsCriticalFn φ)
    (hdomK : ∀ θ ∈ Θ_K,
      power P (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) θ ≤ power P φ θ)
    (hdomH_ae : ∀ᵐ θ ∂Λ₀,
      power P φ θ ≤ power P (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) θ) :
    ∀ θ, power P φ θ
      = power P (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) θ := by
  set φ₀ := bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k with hφ0def
  -- measurability and bounds
  have hsm : StronglyMeasurable (Function.uncurry fun (x : 𝓧) (θ : Θ) => f θ x) :=
    (hjoint.comp measurable_swap).stronglyMeasurable
  have hh0meas : Measurable (mixtureDensity f Λ₀) :=
    (hsm.integral_prod_right (ν := Λ₀)).measurable
  have hh1meas : Measurable (mixtureDensity f Λ₁) :=
    (hsm.integral_prod_right (ν := Λ₁)).measurable
  have hh0nn : ∀ x, 0 ≤ mixtureDensity f Λ₀ x := fun x => integral_nonneg fun θ => hfnonneg θ x
  have hh1nn : ∀ x, 0 ≤ mixtureDensity f Λ₁ x := fun x => integral_nonneg fun θ => hfnonneg θ x
  have hφ0meas : Measurable φ₀ := by
    simp only [hφ0def, bayesTest]
    exact Measurable.ite (measurableSet_le (measurable_const.mul hh0meas) hh1meas)
      measurable_const measurable_const
  have hφ0mem : ∀ x, φ₀ x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x; simp only [hφ0def, bayesTest]; split <;> simp
  have hgφmeas : Measurable fun x => φ₀ x - φ x := hφ0meas.sub hφ.1
  have hgφb : ∀ x, |φ₀ x - φ x| ≤ 1 := by
    intro x; rw [abs_le]
    exact ⟨by linarith [(hφ0mem x).1, (hφ.2 x).2], by linarith [(hφ0mem x).2, (hφ.2 x).1]⟩
  have hh0int : Integrable (mixtureDensity f Λ₀) μ := bayes_mix_integrable hdens hjoint hfnonneg
  have hh1int : Integrable (mixtureDensity f Λ₁) μ := bayes_mix_integrable hdens hjoint hfnonneg
  have hφint : ∀ θ, Integrable φ (P θ) := fun θ =>
    bayes_bounded_integrable hφ.1 fun x => abs_le.mpr ⟨by linarith [(hφ.2 x).1], (hφ.2 x).2⟩
  have hφ0int : ∀ θ, Integrable φ₀ (P θ) := fun θ =>
    bayes_bounded_integrable hφ0meas fun x => abs_le.mpr ⟨by linarith [(hφ0mem x).1], (hφ0mem x).2⟩
  -- Fubini identity for the difference against a prior
  have hfubi : ∀ (Λ : Measure Θ) [IsProbabilityMeasure Λ],
      ∫ x, (φ₀ x - φ x) * mixtureDensity f Λ x ∂μ
        = ∫ θ, (power P φ₀ θ - power P φ θ) ∂Λ := by
    intro Λ _
    rw [bayes_fubini_mix hdens hjoint hfnonneg hgφmeas hgφb]
    refine integral_congr_ae (ae_of_all _ fun θ => ?_)
    simp only [power]
    exact integral_sub (hφ0int θ) (hφint θ)
  -- `Θ_K` is nonempty
  obtain ⟨θ₁, hθ₁K⟩ : Θ_K.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, measure_empty] at hΛ₁; exact zero_ne_one hΛ₁
  -- main a.e. equality against the fixed alternative parameter
  have hae1 : φ =ᵐ[P θ₁] φ₀ := by
    rcases le_or_gt 0 k with hk | hk
    · -- `k ≥ 0`: `φ = φ₀` `μ`-a.e. by the vanishing Bayes objective
      have hμae : φ =ᵐ[μ] φ₀ := by
        have hIpt : ∀ x, 0 ≤ (φ₀ x - φ x) * (mixtureDensity f Λ₁ x - k * mixtureDensity f Λ₀ x) := by
          intro x
          by_cases hcond : k * mixtureDensity f Λ₀ x ≤ mixtureDensity f Λ₁ x
          · have e0 : φ₀ x = 1 := by rw [hφ0def]; simp only [bayesTest, if_pos hcond]
            exact mul_nonneg (by rw [e0]; linarith [(hφ.2 x).2]) (by linarith)
          · push_neg at hcond
            have e0 : φ₀ x = 0 := by rw [hφ0def]; simp only [bayesTest, if_neg (not_le.mpr hcond)]
            have hg0 : φ₀ x - φ x ≤ 0 := by rw [e0]; linarith [(hφ.2 x).1]
            have hd0 : mixtureDensity f Λ₁ x - k * mixtureDensity f Λ₀ x ≤ 0 := by linarith
            exact mul_nonneg_iff.mpr (Or.inr ⟨hg0, hd0⟩)
        have hI1 : Integrable (fun x => (φ₀ x - φ x) * mixtureDensity f Λ₁ x) μ :=
          hh1int.bdd_mul hgφmeas.aestronglyMeasurable
            (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hgφb x)
        have hI0 : Integrable (fun x => (φ₀ x - φ x) * mixtureDensity f Λ₀ x) μ :=
          hh0int.bdd_mul hgφmeas.aestronglyMeasurable
            (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hgφb x)
        have hIint : Integrable
            (fun x => (φ₀ x - φ x) * (mixtureDensity f Λ₁ x - k * mixtureDensity f Λ₀ x)) μ := by
          have heq : (fun x => (φ₀ x - φ x) * (mixtureDensity f Λ₁ x - k * mixtureDensity f Λ₀ x))
              = fun x => (φ₀ x - φ x) * mixtureDensity f Λ₁ x
                - k * ((φ₀ x - φ x) * mixtureDensity f Λ₀ x) := by funext x; ring
          rw [heq]; exact hI1.sub (hI0.const_mul k)
        have hIval : ∫ x, (φ₀ x - φ x) * (mixtureDensity f Λ₁ x - k * mixtureDensity f Λ₀ x) ∂μ
            = (∫ θ, (power P φ₀ θ - power P φ θ) ∂Λ₁)
              - k * ∫ θ, (power P φ₀ θ - power P φ θ) ∂Λ₀ := by
          have hsplit : ∫ x, (φ₀ x - φ x) * (mixtureDensity f Λ₁ x - k * mixtureDensity f Λ₀ x) ∂μ
              = (∫ x, (φ₀ x - φ x) * mixtureDensity f Λ₁ x ∂μ)
                - k * ∫ x, (φ₀ x - φ x) * mixtureDensity f Λ₀ x ∂μ := by
            rw [← integral_const_mul, ← integral_sub hI1 (hI0.const_mul k)]
            exact integral_congr_ae (ae_of_all _ fun x => by ring)
          rw [hsplit, hfubi Λ₁, hfubi Λ₀]
        have haeK : ∀ᵐ θ ∂Λ₁, θ ∈ Θ_K := by
          rw [ae_iff, show {θ | ¬ θ ∈ Θ_K} = Θ_Kᶜ from rfl, measure_compl hΘK (measure_ne_top _ _),
            measure_univ, hΛ₁, tsub_self]
        have hT1 : ∫ θ, (power P φ₀ θ - power P φ θ) ∂Λ₁ ≤ 0 := by
          refine integral_nonpos_of_ae ?_
          filter_upwards [haeK] with θ hθ
          simp only [Pi.zero_apply]; linarith [hdomK θ hθ]
        have hT2 : 0 ≤ ∫ θ, (power P φ₀ θ - power P φ θ) ∂Λ₀ := by
          refine integral_nonneg_of_ae ?_
          filter_upwards [hdomH_ae] with θ hθ
          simp only [Pi.zero_apply]; linarith [hθ]
        have hIzero : ∫ x, (φ₀ x - φ x)
            * (mixtureDensity f Λ₁ x - k * mixtureDensity f Λ₀ x) ∂μ = 0 :=
          le_antisymm (by rw [hIval]; nlinarith [hT1, hT2, hk]) (integral_nonneg hIpt)
        have hIae := (integral_eq_zero_iff_of_nonneg hIpt hIint).mp hIzero
        have hbdry' : ∀ᵐ x ∂μ, mixtureDensity f Λ₁ x ≠ k * mixtureDensity f Λ₀ x := by
          rw [ae_iff]; simp only [ne_eq, not_not]; exact hbdry
        filter_upwards [hIae, hbdry'] with x hx hxne
        simp only [Pi.zero_apply] at hx
        rcases mul_eq_zero.mp hx with h | h
        · exact (sub_eq_zero.mp h).symm
        · exact absurd (by linarith [h] : mixtureDensity f Λ₁ x = k * mixtureDensity f Λ₀ x) hxne
      exact ((hdens θ₁ ▸ withDensity_absolutelyContinuous μ _ : P θ₁ ≪ μ)).ae_eq hμae
    · -- `k < 0`: the Bayes test rejects everywhere, so mutual a.c. forces `φ = 1`
      have hφ01 : ∀ x, φ₀ x = 1 := by
        intro x; simp only [hφ0def, bayesTest]
        exact if_pos (le_trans (mul_nonpos_iff.mpr (Or.inr ⟨hk.le, hh0nn x⟩)) (hh1nn x))
      have hPunit : (P θ₁).real Set.univ = 1 := by
        show (P θ₁ Set.univ).toReal = 1; rw [measure_univ, ENNReal.toReal_one]
      have hp0 : power P φ₀ θ₁ = 1 := by
        simp only [power]; simp_rw [hφ01]
        rw [integral_const, hPunit, smul_eq_mul, mul_one]
      have hple : power P φ θ₁ ≤ 1 := by
        simp only [power]
        calc ∫ x, φ x ∂P θ₁ ≤ ∫ _x, (1 : ℝ) ∂P θ₁ :=
              integral_mono_ae (hφint θ₁) (integrable_const 1) (ae_of_all _ fun x => (hφ.2 x).2)
          _ = 1 := by rw [integral_const, hPunit, smul_eq_mul, mul_one]
      have hpow1 : power P φ θ₁ = 1 :=
        le_antisymm hple (by have := hdomK θ₁ hθ₁K; rwa [hp0] at this)
      have hzero : ∫ x, (1 - φ x) ∂P θ₁ = 0 := by
        rw [integral_sub (integrable_const 1) (hφint θ₁), integral_const, hPunit, smul_eq_mul,
          mul_one, show (∫ x, φ x ∂P θ₁) = power P φ θ₁ from rfl, hpow1, sub_self]
      have hae01 := (integral_eq_zero_iff_of_nonneg
        (fun x => sub_nonneg.mpr (hφ.2 x).2) ((integrable_const 1).sub (hφint θ₁))).mp hzero
      filter_upwards [hae01] with x hx
      simp only [Pi.sub_apply, Pi.one_apply, Pi.zero_apply, sub_eq_zero] at hx
      rw [hφ01 x]; exact hx.symm
  intro θ
  simp only [power]
  exact integral_congr_ae ((bayes_ac hdens hjoint hfnonneg hsupp θ θ₁).ae_eq hae1)

/-- From a level-`α` competitor and a null prior concentrated on the size-attaining
parameters, the competitor is `Λ₀`-a.e. no more powerful than the reference test on the
null class. -/
private lemma bayes_domH_ae {P : Θ → Measure 𝓧} {μ : Measure 𝓧} [SigmaFinite μ]
    {f : Θ → 𝓧 → ℝ} {Λ₀ : Measure Θ} [IsProbabilityMeasure Λ₀]
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2) (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    {Θ_H : Set Θ} (hΘH : MeasurableSet Θ_H) {α : ℝ} {ψ : 𝓧 → ℝ} (hψmeas : Measurable ψ)
    {φ : 𝓧 → ℝ} (hφlevel : IsLevel P Θ_H φ α)
    (hω : Λ₀ {θ ∈ Θ_H | power P ψ θ = α} = 1) :
    ∀ᵐ θ ∂Λ₀, power P φ θ ≤ power P ψ θ := by
  have hpm : Measurable fun θ => power P ψ θ :=
    bayes_power_measurable hdens hjoint hfnonneg hψmeas
  have hSmeas : MeasurableSet {θ ∈ Θ_H | power P ψ θ = α} :=
    hΘH.inter (hpm (measurableSet_singleton α))
  have hScompl : Λ₀ {θ ∈ Θ_H | power P ψ θ = α}ᶜ = 0 := by
    rw [measure_compl hSmeas (measure_ne_top _ _), measure_univ, hω, tsub_self]
  have haeS : ∀ᵐ θ ∂Λ₀, θ ∈ {θ ∈ Θ_H | power P ψ θ = α} := by
    rw [ae_iff]; exact hScompl
  filter_upwards [haeS] with θ hθS
  rw [hθS.2]; exact hφlevel θ hθS.1

/-- **A Bayes test with null boundary is d-admissible.** -/
theorem bayesTest_isDAdmissible {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {f : Θ → 𝓧 → ℝ} {Λ₀ Λ₁ : Measure Θ}
    [IsProbabilityMeasure Λ₀] [IsProbabilityMeasure Λ₁] {Θ_H Θ_K : Set Θ} {k : ℝ}
    -- USER-INPUT: the model is dominated by `μ` with densities `f`, jointly measurable
    -- in parameter and observation
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    -- USER-INPUT: the support of the density does not depend on the parameter
    (hsupp : ∀ (θ θ' : Θ) (x : 𝓧), 0 < f θ x ↔ 0 < f θ' x)
    -- USER-INPUT: the null and alternative classes are measurable
    (hΘH : MeasurableSet Θ_H) (hΘK : MeasurableSet Θ_K)
    -- USER-INPUT: the priors are carried by the null and alternative classes
    (hΛ₀ : Λ₀ Θ_H = 1) (hΛ₁ : Λ₁ Θ_K = 1)
    -- USER-INPUT: the Bayes boundary is null
    (hbdry : μ {x | mixtureDensity f Λ₁ x = k * mixtureDensity f Λ₀ x} = 0) :
    IsDAdmissible P Θ_H Θ_K
      (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) := by
  intro φ hφ hdomK hdomH θ _
  refine bayes_admissible_core hdens hjoint hfnonneg hsupp hΘK hΛ₁ hbdry hφ hdomK ?_ θ
  have haeH : ∀ᵐ θ ∂Λ₀, θ ∈ Θ_H := by
    rw [ae_iff, show {θ | ¬ θ ∈ Θ_H} = Θ_Hᶜ from rfl, measure_compl hΘH (measure_ne_top _ _),
      measure_univ, hΛ₀, tsub_self]
  filter_upwards [haeH] with θ hθ'; exact hdomH θ hθ'

/-- **A Bayes test whose null prior concentrates on the size-attaining parameters is
`α`-admissible.** -/
theorem bayesTest_isAlphaAdmissible {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {f : Θ → 𝓧 → ℝ} {Λ₀ Λ₁ : Measure Θ}
    [IsProbabilityMeasure Λ₀] [IsProbabilityMeasure Λ₁] {Θ_H Θ_K : Set Θ} {k α : ℝ}
    -- USER-INPUT: dominated model with jointly measurable nonnegative densities
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    -- USER-INPUT: the support of the density does not depend on the parameter
    (hsupp : ∀ (θ θ' : Θ) (x : 𝓧), 0 < f θ x ↔ 0 < f θ' x)
    -- USER-INPUT: the null and alternative classes are measurable
    (hΘH : MeasurableSet Θ_H) (hΘK : MeasurableSet Θ_K)
    -- USER-INPUT: the priors are carried by the null and alternative classes
    (hΛ₀ : Λ₀ Θ_H = 1) (hΛ₁ : Λ₁ Θ_K = 1)
    -- USER-INPUT: the Bayes boundary is null
    (hbdry : μ {x | mixtureDensity f Λ₁ x = k * mixtureDensity f Λ₀ x} = 0)
    -- USER-INPUT: `α` is the size of the Bayes test on the null class
    (hlevel : IsLevel P Θ_H (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) α)
    -- USER-INPUT: the null prior concentrates on the parameters where the size is attained
    (hω : Λ₀ {θ ∈ Θ_H |
      power P (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) θ = α} = 1) :
    IsAlphaAdmissible P Θ_H Θ_K α
      (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) := by
  intro φ hφ hφlevel hdomK θ _
  refine bayes_admissible_core hdens hjoint hfnonneg hsupp hΘK hΛ₁ hbdry hφ hdomK ?_ θ
  have hsm : StronglyMeasurable (Function.uncurry fun (x : 𝓧) (θ : Θ) => f θ x) :=
    (hjoint.comp measurable_swap).stronglyMeasurable
  have hφ0meas : Measurable (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) :=
    Measurable.ite (measurableSet_le
      (measurable_const.mul (hsm.integral_prod_right (ν := Λ₀)).measurable)
      (hsm.integral_prod_right (ν := Λ₁)).measurable)
      measurable_const measurable_const
  exact bayes_domH_ae hdens hjoint hfnonneg hΘH hφ0meas hφlevel hω

/-- **Admissibility against any subclass carrying the alternative prior.** If `Λ₁` gives
probability one to a subclass `Θ'` of the alternatives, both conclusions hold with `Θ'` in
place of the full alternative class. -/
theorem bayesTest_admissible_of_subset {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {f : Θ → 𝓧 → ℝ} {Λ₀ Λ₁ : Measure Θ}
    [IsProbabilityMeasure Λ₀] [IsProbabilityMeasure Λ₁] {Θ_H Θ_K Θ' : Set Θ} {k α : ℝ}
    -- USER-INPUT: dominated model with jointly measurable nonnegative densities
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    -- USER-INPUT: the support of the density does not depend on the parameter
    (hsupp : ∀ (θ θ' : Θ) (x : 𝓧), 0 < f θ x ↔ 0 < f θ' x)
    -- USER-INPUT: the classes are measurable and `Θ'` is a subclass of the alternatives
    (hΘH : MeasurableSet Θ_H) (hΘK : MeasurableSet Θ_K) (hΘ' : MeasurableSet Θ')
    (hsub : Θ' ⊆ Θ_K)
    -- USER-INPUT: the priors are carried by the null class and by the subclass
    (hΛ₀ : Λ₀ Θ_H = 1) (hΛ₁ : Λ₁ Θ' = 1)
    -- USER-INPUT: the Bayes boundary is null
    (hbdry : μ {x | mixtureDensity f Λ₁ x = k * mixtureDensity f Λ₀ x} = 0)
    -- USER-INPUT: `α` is the size of the Bayes test, attained `Λ₀`-almost surely
    (hlevel : IsLevel P Θ_H (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) α)
    (hω : Λ₀ {θ ∈ Θ_H |
      power P (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) θ = α} = 1) :
    IsDAdmissible P Θ_H Θ'
        (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) ∧
      IsAlphaAdmissible P Θ_H Θ' α
        (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) := by
  have hsm : StronglyMeasurable (Function.uncurry fun (x : 𝓧) (θ : Θ) => f θ x) :=
    (hjoint.comp measurable_swap).stronglyMeasurable
  have hφ0meas : Measurable (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) :=
    Measurable.ite (measurableSet_le
      (measurable_const.mul (hsm.integral_prod_right (ν := Λ₀)).measurable)
      (hsm.integral_prod_right (ν := Λ₁)).measurable)
      measurable_const measurable_const
  refine ⟨?_, ?_⟩
  · -- d-admissibility against the subclass: pointwise null domination
    intro φ hφ hdomK hdomH θ _
    refine bayes_admissible_core hdens hjoint hfnonneg hsupp hΘ' hΛ₁ hbdry hφ hdomK ?_ θ
    have haeH : ∀ᵐ θ ∂Λ₀, θ ∈ Θ_H := by
      rw [ae_iff, show {θ | ¬ θ ∈ Θ_H} = Θ_Hᶜ from rfl, measure_compl hΘH (measure_ne_top _ _),
        measure_univ, hΛ₀, tsub_self]
    filter_upwards [haeH] with θ hθ'; exact hdomH θ hθ'
  · -- α-admissibility against the subclass: level + concentration null domination
    intro φ hφ hφlevel hdomK θ _
    refine bayes_admissible_core hdens hjoint hfnonneg hsupp hΘ' hΛ₁ hbdry hφ hdomK ?_ θ
    exact bayes_domH_ae hdens hjoint hfnonneg hΘH hφ0meas hφlevel hω

end Bayes

/-! ## The Gaussian scale-mixture identity -/

open StatLean.Bayesian in
/-- The Gaussian known-variance kernel evaluated at `m'` is the Gaussian law `N(m', v)`
(re-derivation of the private `gaussKernel_apply_eq` for use here). -/
private theorem gaussKernel_apply_eq' {v : ℝ≥0} (hv : v ≠ 0) (m' : ℝ) :
    gaussKernel v m' = gaussianReal m' v := by
  have hmeas : Measurable (Function.uncurry fun θ x => gaussianPDF θ v x) := by
    change Measurable fun z : ℝ × ℝ => ENNReal.ofReal (gaussianPDFReal z.1 v z.2)
    refine Measurable.ennreal_ofReal ?_
    unfold gaussianPDFReal
    fun_prop
  rw [gaussKernel, Kernel.withDensity_apply _ hmeas, Kernel.const_apply,
    gaussianReal_of_var_ne_zero _ hv]

/-- **Mixing a Gaussian location family over its mean reproduces a wider centred
Gaussian.** For a variance `σ² > 0` and any larger `M²`, there is a prior on the mean
under which the mixture of `N(ζ, σ²)` over `ζ` is exactly `N(0, M²)` — stated both as the
pointwise density identity and as the measure-level mixture identity.

This is the device that removes nuisance means from a likelihood ratio: choosing `M²`
above every variance in play makes the mean contributions to the two mixture densities
cancel. The intended construction takes the mixing prior itself centred Gaussian with
variance `M² − σ²`, for which the normal–normal conjugacy of `StatLean.Bayesian` supplies
the computation. -/
theorem exists_gaussian_scale_mixture {σ2 M2 : NNReal}
    -- USER-INPUT: the inner variance is nondegenerate
    (hσ : σ2 ≠ 0)
    -- USER-INPUT: the target variance is strictly larger
    (hσM : σ2 < M2) :
    ∃ Λ : Measure ℝ, IsProbabilityMeasure Λ ∧
      (∀ z : ℝ, ∫ ζ, gaussianPDFReal ζ σ2 z ∂Λ = gaussianPDFReal 0 M2 z) ∧
      (∀ B : Set ℝ, MeasurableSet B →
        ∫⁻ ζ, gaussianReal ζ σ2 B ∂Λ = gaussianReal 0 M2 B) := by
  classical
  have hM2pos : (0 : NNReal) < M2 := lt_of_le_of_lt (zero_le) hσM
  have hM2 : M2 ≠ 0 := hM2pos.ne'
  -- The measure-level mixture identity, via the Gaussian convolution kernel.
  have hkey : ∀ B : Set ℝ, MeasurableSet B →
      ∫⁻ ζ, gaussianReal ζ σ2 B ∂(gaussianReal 0 (M2 - σ2)) = gaussianReal 0 M2 B := by
    intro B hB
    haveI hmark := StatLean.Bayesian.isMarkovKernel_gaussKernel hσ
    have key : StatLean.Bayesian.gaussKernel σ2 ∘ₘ gaussianReal 0 (M2 - σ2)
        = gaussianReal 0 M2 := by
      rw [StatLean.Bayesian.comp_gaussKernel_gaussianReal hσ, tsub_add_cancel_of_le hσM.le]
    calc ∫⁻ ζ, gaussianReal ζ σ2 B ∂(gaussianReal 0 (M2 - σ2))
        = ∫⁻ ζ, StatLean.Bayesian.gaussKernel σ2 ζ B ∂(gaussianReal 0 (M2 - σ2)) := by
          refine lintegral_congr fun ζ => ?_
          rw [gaussKernel_apply_eq' hσ]
      _ = (StatLean.Bayesian.gaussKernel σ2 ∘ₘ gaussianReal 0 (M2 - σ2)) B :=
          (Measure.bind_apply hB (Kernel.measurable _).aemeasurable).symm
      _ = gaussianReal 0 M2 B := by rw [key]
  refine ⟨gaussianReal 0 (M2 - σ2), inferInstance, ?_, hkey⟩
  -- Pointwise density identity, obtained from `hkey` by density uniqueness + continuity.
  -- Joint measurability of `(w, ζ) ↦ gaussianPDF ζ σ2 w`.
  have hjm : Measurable (Function.uncurry fun w ζ => gaussianPDF ζ σ2 w) := by
    change Measurable fun p : ℝ × ℝ => ENNReal.ofReal (gaussianPDFReal p.2 σ2 p.1)
    refine Measurable.ennreal_ofReal ?_
    unfold gaussianPDFReal
    fun_prop
  have hLmeas : Measurable
      fun w => ∫⁻ ζ, gaussianPDF ζ σ2 w ∂(gaussianReal 0 (M2 - σ2)) :=
    hjm.lintegral_prod_right (ν := gaussianReal 0 (M2 - σ2))
  -- The mixture measure has marginal density `w ↦ ∫⁻ ζ, gaussianPDF ζ σ2 w ∂Λ`.
  have hwd : (volume : Measure ℝ).withDensity
      (fun w => ∫⁻ ζ, gaussianPDF ζ σ2 w ∂(gaussianReal 0 (M2 - σ2)))
      = gaussianReal 0 M2 := by
    ext B hB
    rw [withDensity_apply _ hB, ← hkey B hB,
      lintegral_lintegral_swap (μ := volume.restrict B)
        (ν := gaussianReal 0 (M2 - σ2)) hjm.aemeasurable]
    refine lintegral_congr fun ζ => ?_
    rw [gaussianReal_of_var_ne_zero ζ hσ, withDensity_apply _ hB]
  -- Density uniqueness gives the a.e. identity at the `ℝ≥0∞` level.
  have hae : (fun w => ∫⁻ ζ, gaussianPDF ζ σ2 w ∂(gaussianReal 0 (M2 - σ2)))
      =ᵐ[volume] gaussianPDF 0 M2 := by
    have h1 : (volume : Measure ℝ).withDensity
        (fun w => ∫⁻ ζ, gaussianPDF ζ σ2 w ∂(gaussianReal 0 (M2 - σ2)))
        = (volume : Measure ℝ).withDensity (gaussianPDF 0 M2) := by
      rw [hwd, gaussianReal_of_var_ne_zero 0 hM2]
    exact (withDensity_eq_iff_of_sigmaFinite hLmeas.aemeasurable
      (measurable_gaussianPDF 0 M2).aemeasurable).mp h1
  -- The Bochner density is the `toReal` of the `ℝ≥0∞` one.
  have hdL : ∀ z, ∫ ζ, gaussianPDFReal ζ σ2 z ∂(gaussianReal 0 (M2 - σ2))
      = (∫⁻ ζ, gaussianPDF ζ σ2 z ∂(gaussianReal 0 (M2 - σ2))).toReal := by
    intro z
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun ζ => gaussianPDFReal_nonneg ζ σ2 z)
      (Continuous.aestronglyMeasurable (by unfold gaussianPDFReal; fun_prop))]
    rfl
  -- Transport the a.e. identity to the real level.
  have hae_real : (fun z => ∫ ζ, gaussianPDFReal ζ σ2 z ∂(gaussianReal 0 (M2 - σ2)))
      =ᵐ[volume] fun z => gaussianPDFReal 0 M2 z := by
    filter_upwards [hae] with z hz
    rw [hdL z, hz, gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 M2 z)]
  -- Both densities are continuous, so a.e. equality upgrades to everywhere.
  have hcont_g : Continuous fun z => gaussianPDFReal 0 M2 z := by
    unfold gaussianPDFReal; fun_prop
  have hcont_d : Continuous
      fun z => ∫ ζ, gaussianPDFReal ζ σ2 z ∂(gaussianReal 0 (M2 - σ2)) := by
    refine continuous_of_dominated (bound := fun _ => (Real.sqrt (2 * Real.pi * σ2))⁻¹)
      (fun z => ?_) (fun z => ?_) (integrable_const _) (ae_of_all _ fun ζ => ?_)
    · exact (Continuous.aestronglyMeasurable (by unfold gaussianPDFReal; fun_prop))
    · refine ae_of_all _ fun ζ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg ζ σ2 z)]
      calc gaussianPDFReal ζ σ2 z
          = (Real.sqrt (2 * Real.pi * σ2))⁻¹ * Real.exp (-(z - ζ) ^ 2 / (2 * σ2)) := rfl
        _ ≤ (Real.sqrt (2 * Real.pi * σ2))⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_one_iff.mpr (by
                rw [div_nonpos_iff]
                exact Or.inr ⟨neg_nonpos.mpr (sq_nonneg _), by positivity⟩))
              (by positivity)
        _ = (Real.sqrt (2 * Real.pi * σ2))⁻¹ := mul_one _
    · unfold gaussianPDFReal; fun_prop
  exact fun z => congrFun (Measure.eq_of_ae_eq hae_real hcont_d hcont_g) z

end StatLean.HypothesisTesting
