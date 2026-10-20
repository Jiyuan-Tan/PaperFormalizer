module
public import StatLean.HypothesisTesting.Tests.Defs
public import StatLean.HypothesisTesting.ForMathlib.QuantileFunction
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# The fundamental lemma of testing a simple hypothesis against a simple alternative

Let `P₀` and `P₁` be probability measures with densities `p₀`, `p₁` with respect to a
σ-finite measure `μ`. The **likelihood-ratio test** with threshold `C` and boundary
randomization `γ`,
$$ \varphi(x) \;=\; \begin{cases} 1 & p_1(x) > C\,p_0(x), \\
\gamma & p_1(x) = C\,p_0(x), \\ 0 & p_1(x) < C\,p_0(x), \end{cases} $$
is optimal in the strongest possible sense: a suitable `(C, γ)` achieves **exactly** size
`α`, every test of that shape and size is most powerful, and — conversely — every most
powerful test has that shape almost everywhere.

Contents:
* `HasDensity μ p P` — `P = p·μ` for a nonnegative measurable `p` (the dominated setup);
* `npTest p₀ p₁ C γ` — the likelihood-ratio test above;
* `exists_mostPowerful` — existence of `(C, γ)` with size exactly `α`, and optimality;
* `isMostPowerful_of_npShape`, `isMostPowerful_npTest` — sufficiency;
* `npTest_necessity` — necessity of the shape a.e., plus the exact-size clause;
* `power_gt_alpha_of_ne`, `power_eq_alpha_of_eq` — strict unbiasedness, and the honest
  degenerate case.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.2 (The Neyman–Pearson Fundamental Lemma), Theorem 3.2.1 (the fundamental
lemma: existence, sufficiency and necessity of the likelihood-ratio form) and Corollary 3.2.1
(strict unbiasedness unless the two distributions coincide). (`TSH4 §3.2 Thm 3.2.1, Cor
3.2.1`.)

**Proof formalization notes.**
* The threshold lives in `ℝ≥0∞`: this is what admits the corner value `C = ∞` needed for
  `α = 0`, and it makes the convention "`0 · ∞ = 0`" (used exactly at that corner) the
  ambient `ENNReal` arithmetic rather than a side convention. The comparison is therefore
  `C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x)` rather than a real inequality.
* The classical construction takes `α(c) = P₀{p₁/p₀ > c}`; `1 - α` is a cumulative
  distribution function, so `α(c)` is nonincreasing and right-continuous, and the
  boundary weight is `γ = (α - α(C))/(α(C⁻) - α(C))` whenever the denominator is nonzero.
  The `ℝ≥0∞` formulation avoids forming the ratio `p₁/p₀` at all.
* The necessity statement is transcribed with its escape clause: exact size `α` is forced
  only when no test of size `< α` already has power `1`.
* `HasDensity` is a local convenience predicate for the dominated setup; it is a
  candidate for promotion into the shared test-layer data model.

**Bibliographic comments.** The lemma, the randomized-test formulation, and the
existence/sufficiency/necessity trichotomy are due to J. Neyman and E. S. Pearson ("On
the problem of the most efficient tests of statistical hypotheses," *Phil. Trans. R. Soc.
Lond. A* **231** (1933), 289–337), with the systematic treatment of the boundary
randomization in J. Neyman and E. S. Pearson ("Contributions to the theory of testing
statistical hypotheses," *Stat. Res. Mem.* **1** (1936), 1–37). Measure-theoretic
formulations under an arbitrary dominating measure were given by G. B. Dantzig and
A. Wald ("On the fundamental lemma of Neyman and Pearson," *Ann. Math. Statist.* **22**
(1951), 87–93).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- `P` **has density** `p` with respect to `μ`: `p` is measurable and nonnegative and
`P = p·μ`. This is the dominated setup "`P` possesses the density `p` with respect to
the measure `μ`"; nonnegativity is carried explicitly because densities are real-valued
here, and `ENNReal.ofReal` would otherwise silently truncate. -/
def HasDensity (μ : Measure 𝓧) (p : 𝓧 → ℝ) (P : Measure 𝓧) : Prop :=
  Measurable p ∧ (∀ x, 0 ≤ p x) ∧ P = μ.withDensity fun x => ENNReal.ofReal (p x)

/-- The **Neyman–Pearson (likelihood-ratio) test** with threshold `C : ℝ≥0∞` and boundary
randomization `γ`: reject when `p₁ > C·p₀`, reject with probability `γ` when
`p₁ = C·p₀`, accept when `p₁ < C·p₀`.

The threshold is extended-nonnegative-real so that the corner `C = ∞` (needed for
`α = 0`) is available and `0 · ∞ = 0` is the ambient arithmetic. For `C = 0` the test
rejects wherever `p₁ > 0`. No constraint is imposed on `γ` by the definition: for `γ`
outside `[0,1]` the result is not a critical function, and the theorems below therefore
carry `γ ∈ [0,1]` explicitly. -/
noncomputable def npTest (p₀ p₁ : 𝓧 → ℝ) (C : ℝ≥0∞) (γ : ℝ) : 𝓧 → ℝ := fun x =>
  if C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x) then 1
  else if ENNReal.ofReal (p₁ x) = C * ENNReal.ofReal (p₀ x) then γ
  else 0

/-- `φ` **has Neyman–Pearson shape** at threshold `C`: it rejects `μ`-a.e. where
`p₁ > C·p₀` and accepts `μ`-a.e. where `p₁ < C·p₀`, with no constraint on the boundary
set `{p₁ = C·p₀}`. This is the almost-everywhere form of the displayed test above, and
is the shape that most powerful tests are forced to have. -/
def HasNPShape (μ : Measure 𝓧) (p₀ p₁ : 𝓧 → ℝ) (C : ℝ≥0∞) (φ : 𝓧 → ℝ) : Prop :=
  (∀ᵐ x ∂μ, C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x) → φ x = 1) ∧
    (∀ᵐ x ∂μ, ENNReal.ofReal (p₁ x) < C * ENNReal.ofReal (p₀ x) → φ x = 0)

/-- A density of a probability measure is integrable. -/
private lemma hasDensity_integrable {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    [IsProbabilityMeasure P] (h : HasDensity μ p P) : Integrable p μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  have h1 : (μ.withDensity fun x => ENNReal.ofReal (p x)) Set.univ = 1 := by
    rw [← hPeq]; exact measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [h1]; exact ENNReal.one_lt_top

/-- The power of a critical function against a density-carrying measure is the integral of the
critical function times the density. -/
private lemma powerAgainst_eq {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    (h : HasDensity μ p P) (φ : 𝓧 → ℝ) :
    powerAgainst P φ = ∫ x, φ x * p x ∂μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  unfold powerAgainst
  rw [hPeq, integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hnn x)]; ring

/-- Integrability of a critical function times a density. -/
private lemma integrable_crit_mul {μ : Measure 𝓧} {p φ : 𝓧 → ℝ} (hp : Integrable p μ)
    (hφ : IsCriticalFn φ) : Integrable (fun x => φ x * p x) μ :=
  hp.bdd_mul hφ.1.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.2 x).1]; exact (hφ.2 x).2)

/-- The density of a probability measure integrates to `1`. -/
private lemma hasDensity_integral_one {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    [IsProbabilityMeasure P] (h : HasDensity μ p P) : ∫ x, p x ∂μ = 1 := by
  have h1 : powerAgainst P (fun _ => (1 : ℝ)) = ∫ x, (1 : ℝ) * p x ∂μ := powerAgainst_eq h _
  unfold powerAgainst at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, one_mul] at h1
  exact h1.symm

/-- Real form of the two strict threshold comparisons, at a finite threshold: the `ℝ≥0∞`
conditions defining `npTest` and `HasNPShape` are the honest real inequalities. -/
private lemma npCompare_iff {C : ℝ≥0∞} (hC : C ≠ ⊤) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (C * ENNReal.ofReal a < ENNReal.ofReal b ↔ C.toReal * a < b) ∧
      (ENNReal.ofReal b < C * ENNReal.ofReal a ↔ b < C.toReal * a) := by
  set c := C.toReal with hcdef
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hCeq : C = ENNReal.ofReal c := (ENNReal.ofReal_toReal hC).symm
  rw [hCeq, ← ENNReal.ofReal_mul hc0]
  exact ⟨ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hc0 ha),
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb⟩

/-- **Fundamental inequality, finite threshold.** For a finite threshold `C`, any test of
Neyman–Pearson shape whose `P₀`-size dominates that of a competitor `ψ` dominates it in
`P₁`-power as well. This is the pointwise `(φ − ψ)(p₁ − C·p₀) ≥ 0` argument. -/
private lemma np_fundamental_finite (μ : Measure 𝓧) [SigmaFinite μ]
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} (h₀ : HasDensity μ p₀ P₀) (h₁ : HasDensity μ p₁ P₁)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {φ ψ : 𝓧 → ℝ}
    (hφc : IsCriticalFn φ) (hψc : IsCriticalFn ψ)
    (hshape : HasNPShape μ p₀ p₁ C φ)
    (hsize : powerAgainst P₀ ψ ≤ powerAgainst P₀ φ) :
    powerAgainst P₁ ψ ≤ powerAgainst P₁ φ := by
  have hp0nn := h₀.2.1
  have hp1nn := h₁.2.1
  set c := C.toReal with hcdef
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hCeq : C = ENNReal.ofReal c := (ENNReal.ofReal_toReal hC).symm
  obtain ⟨hsp1, hsp0⟩ := hshape
  -- Pointwise `(φ − ψ)(p₁ − c·p₀) ≥ 0`.
  have hpt : 0 ≤ᵐ[μ] fun x => (φ x - ψ x) * (p₁ x - c * p₀ x) := by
    filter_upwards [hsp1, hsp0] with x hx1 hx0
    have hp0x := hp0nn x; have hp1x := hp1nn x
    have hφ1 := (hφc.2 x).2; have hψ0 := (hψc.2 x).1; have hψ1 := (hψc.2 x).2
    rcases lt_trichotomy (c * p₀ x) (p₁ x) with hlt | heq | hgt
    · have hpos : 0 < p₁ x := lt_of_le_of_lt (by positivity) hlt
      have hcmp : C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x) := by
        rw [hCeq, ← ENNReal.ofReal_mul hc0]
        exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hlt
      rw [hx1 hcmp]
      exact mul_nonneg (by linarith) (by linarith)
    · have hz : p₁ x - c * p₀ x = 0 := by linarith
      simp [hz]
    · have hpos : 0 < c * p₀ x := lt_of_le_of_lt hp1x hgt
      have hcmp : ENNReal.ofReal (p₁ x) < C * ENNReal.ofReal (p₀ x) := by
        rw [hCeq, ← ENNReal.ofReal_mul hc0]
        exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hgt
      rw [hx0 hcmp]
      have hrw : (0 - ψ x) * (p₁ x - c * p₀ x) = ψ x * (c * p₀ x - p₁ x) := by ring
      rw [hrw]
      exact mul_nonneg (by linarith) (by linarith)
  have hnn := integral_nonneg_of_ae hpt
  have hp0i : Integrable p₀ μ := hasDensity_integrable h₀
  have hp1i : Integrable p₁ μ := hasDensity_integrable h₁
  have hφp1 := integrable_crit_mul hp1i hφc
  have hψp1 := integrable_crit_mul hp1i hψc
  have hφp0 := integrable_crit_mul hp0i hφc
  have hψp0 := integrable_crit_mul hp0i hψc
  have key : ∫ x, (φ x - ψ x) * (p₁ x - c * p₀ x) ∂μ
      = (powerAgainst P₁ φ - powerAgainst P₁ ψ) - c * (powerAgainst P₀ φ - powerAgainst P₀ ψ) := by
    have hAB : Integrable (fun x => φ x * p₁ x - ψ x * p₁ x) μ := hφp1.sub hψp1
    have hDE : Integrable (fun x => c * (φ x * p₀ x - ψ x * p₀ x)) μ :=
      (hφp0.sub hψp0).const_mul c
    rw [powerAgainst_eq h₁ φ, powerAgainst_eq h₁ ψ, powerAgainst_eq h₀ φ, powerAgainst_eq h₀ ψ,
      ← integral_sub hφp1 hψp1, ← integral_sub hφp0 hψp0, ← integral_const_mul,
      ← integral_sub hAB hDE]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [key] at hnn
  have hc_nonneg : 0 ≤ c * (powerAgainst P₀ φ - powerAgainst P₀ ψ) :=
    mul_nonneg hc0 (by linarith)
  linarith

/-- **Fundamental inequality, infinite threshold** (the `α = 0` corner). A test of
Neyman–Pearson shape at `C = ∞` has `P₀`-size zero; any competitor with size `≤ 0` puts no
mass where `p₀ > 0`, so `φ` dominates it in `P₁`-power. -/
private lemma np_fundamental_top (μ : Measure 𝓧) [SigmaFinite μ]
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} (h₀ : HasDensity μ p₀ P₀) (h₁ : HasDensity μ p₁ P₁)
    {φ ψ : 𝓧 → ℝ} (hφc : IsCriticalFn φ) (hψc : IsCriticalFn ψ)
    (hshape : HasNPShape μ p₀ p₁ ⊤ φ)
    (hsize : powerAgainst P₀ ψ ≤ powerAgainst P₀ φ) :
    powerAgainst P₁ ψ ≤ powerAgainst P₁ φ := by
  have hp0nn := h₀.2.1; have hp1nn := h₁.2.1
  obtain ⟨hsp1, hsp0⟩ := hshape
  have hp0i : Integrable p₀ μ := hasDensity_integrable h₀
  have hp1i : Integrable p₁ μ := hasDensity_integrable h₁
  have hφp0z : (fun x => φ x * p₀ x) =ᵐ[μ] 0 := by
    filter_upwards [hsp0] with x hx0
    show φ x * p₀ x = 0
    rcases eq_or_lt_of_le (hp0nn x) with h | h
    · rw [← h, mul_zero]
    · have hc2 : ENNReal.ofReal (p₁ x) < ⊤ * ENNReal.ofReal (p₀ x) := by
        rw [ENNReal.top_mul (by simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; exact h)]
        exact ENNReal.ofReal_lt_top
      rw [hx0 hc2, zero_mul]
  have hpAφ0 : powerAgainst P₀ φ = 0 := by
    rw [powerAgainst_eq h₀ φ, integral_congr_ae hφp0z]; simp
  have hψp0nn : 0 ≤ᵐ[μ] fun x => ψ x * p₀ x :=
    Filter.Eventually.of_forall fun x => mul_nonneg (hψc.2 x).1 (hp0nn x)
  have hψp0i : Integrable (fun x => ψ x * p₀ x) μ := integrable_crit_mul hp0i hψc
  have hψp0z : (fun x => ψ x * p₀ x) =ᵐ[μ] 0 := by
    have hle : ∫ x, ψ x * p₀ x ∂μ ≤ 0 := by
      rw [← powerAgainst_eq h₀ ψ]; rw [hpAφ0] at hsize; exact hsize
    have heq0 : ∫ x, ψ x * p₀ x ∂μ = 0 := le_antisymm hle (integral_nonneg_of_ae hψp0nn)
    exact (integral_eq_zero_iff_of_nonneg_ae hψp0nn hψp0i).mp heq0
  have hpt : 0 ≤ᵐ[μ] fun x => (φ x - ψ x) * p₁ x := by
    filter_upwards [hsp1, hsp0, hψp0z] with x hx1 hx0 hxψ0
    show 0 ≤ (φ x - ψ x) * p₁ x
    rcases eq_or_lt_of_le (hp0nn x) with hp0 | hp0
    · rcases eq_or_lt_of_le (hp1nn x) with hp1 | hp1
      · rw [← hp1]; simp
      · have hc1 : (⊤ : ℝ≥0∞) * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x) := by
          rw [← hp0, ENNReal.ofReal_zero, mul_zero]
          exact ENNReal.ofReal_pos.mpr hp1
        rw [hx1 hc1]
        exact mul_nonneg (by linarith [(hψc.2 x).2]) (le_of_lt hp1)
    · have hc2 : ENNReal.ofReal (p₁ x) < ⊤ * ENNReal.ofReal (p₀ x) := by
        rw [ENNReal.top_mul (by simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp0)]
        exact ENNReal.ofReal_lt_top
      have hψ0 : ψ x = 0 := by
        simp only [Pi.zero_apply] at hxψ0
        rcases mul_eq_zero.mp hxψ0 with h | h
        · exact h
        · exact absurd h (ne_of_gt hp0)
      rw [hx0 hc2, hψ0]; simp
  have hnn := integral_nonneg_of_ae hpt
  have hφp1 := integrable_crit_mul hp1i hφc
  have hψp1 := integrable_crit_mul hp1i hψc
  have key : ∫ x, (φ x - ψ x) * p₁ x ∂μ = powerAgainst P₁ φ - powerAgainst P₁ ψ := by
    rw [powerAgainst_eq h₁ φ, powerAgainst_eq h₁ ψ, ← integral_sub hφp1 hψp1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [key] at hnn
  linarith

/-- **Necessity, finite threshold.** The converse of `np_fundamental_finite`: if a competitor
`ψ` *matches* the power of a test `φ` of Neyman–Pearson shape while not exceeding its size,
then `ψ` has the same shape `μ`-a.e. The nonnegative integrand of the fundamental inequality
now has integral `≤ 0`, hence vanishes a.e., and the shape of `φ` reads off the shape of
`ψ` on each of the two strict-inequality sets. -/
private lemma npShape_of_maxPower_finite (μ : Measure 𝓧) [SigmaFinite μ]
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} (h₀ : HasDensity μ p₀ P₀) (h₁ : HasDensity μ p₁ P₁)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {φ ψ : 𝓧 → ℝ}
    (hφc : IsCriticalFn φ) (hψc : IsCriticalFn ψ)
    (hshape : HasNPShape μ p₀ p₁ C φ)
    (hsize : powerAgainst P₀ ψ ≤ powerAgainst P₀ φ)
    (hpow : powerAgainst P₁ φ ≤ powerAgainst P₁ ψ) :
    (∀ᵐ x ∂μ, (φ x - ψ x) * (p₁ x - C.toReal * p₀ x) = 0) ∧ HasNPShape μ p₀ p₁ C ψ := by
  have hp0nn := h₀.2.1
  have hp1nn := h₁.2.1
  set c := C.toReal with hcdef
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hCeq : C = ENNReal.ofReal c := (ENNReal.ofReal_toReal hC).symm
  obtain ⟨hsp1, hsp0⟩ := hshape
  -- The two strict-inequality conditions, in real form.
  have hreal1 : ∀ x, C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x) ↔ c * p₀ x < p₁ x :=
    fun x => (npCompare_iff hC (hp0nn x) (hp1nn x)).1
  have hreal0 : ∀ x, ENNReal.ofReal (p₁ x) < C * ENNReal.ofReal (p₀ x) ↔ p₁ x < c * p₀ x :=
    fun x => (npCompare_iff hC (hp0nn x) (hp1nn x)).2
  -- Pointwise `(φ − ψ)(p₁ − c·p₀) ≥ 0`.
  have hpt : 0 ≤ᵐ[μ] fun x => (φ x - ψ x) * (p₁ x - c * p₀ x) := by
    filter_upwards [hsp1, hsp0] with x hx1 hx0
    have hφ1 := (hφc.2 x).2; have hψ0 := (hψc.2 x).1; have hψ1 := (hψc.2 x).2
    rcases lt_trichotomy (c * p₀ x) (p₁ x) with hlt | heq | hgt
    · rw [hx1 ((hreal1 x).mpr hlt)]
      exact mul_nonneg (by linarith) (by linarith)
    · have hz : p₁ x - c * p₀ x = 0 := by linarith
      simp [hz]
    · rw [hx0 ((hreal0 x).mpr hgt)]
      have hrw : (0 - ψ x) * (p₁ x - c * p₀ x) = ψ x * (c * p₀ x - p₁ x) := by ring
      rw [hrw]
      exact mul_nonneg (by linarith) (by linarith)
  have hp0i : Integrable p₀ μ := hasDensity_integrable h₀
  have hp1i : Integrable p₁ μ := hasDensity_integrable h₁
  have hφp1 := integrable_crit_mul hp1i hφc
  have hψp1 := integrable_crit_mul hp1i hψc
  have hφp0 := integrable_crit_mul hp0i hφc
  have hψp0 := integrable_crit_mul hp0i hψc
  have hint : Integrable (fun x => (φ x - ψ x) * (p₁ x - c * p₀ x)) μ := by
    refine ((hφp1.sub hψp1).sub ((hφp0.sub hψp0).const_mul c)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have key : ∫ x, (φ x - ψ x) * (p₁ x - c * p₀ x) ∂μ
      = (powerAgainst P₁ φ - powerAgainst P₁ ψ) - c * (powerAgainst P₀ φ - powerAgainst P₀ ψ) := by
    have hAB : Integrable (fun x => φ x * p₁ x - ψ x * p₁ x) μ := hφp1.sub hψp1
    have hDE : Integrable (fun x => c * (φ x * p₀ x - ψ x * p₀ x)) μ :=
      (hφp0.sub hψp0).const_mul c
    rw [powerAgainst_eq h₁ φ, powerAgainst_eq h₁ ψ, powerAgainst_eq h₀ φ, powerAgainst_eq h₀ ψ,
      ← integral_sub hφp1 hψp1, ← integral_sub hφp0 hψp0, ← integral_const_mul,
      ← integral_sub hAB hDE]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  -- The integral is `≤ 0` as well, hence `0`, hence the integrand vanishes a.e.
  have hle : ∫ x, (φ x - ψ x) * (p₁ x - c * p₀ x) ∂μ ≤ 0 := by
    rw [key]
    have := mul_nonneg hc0 (sub_nonneg.mpr hsize)
    linarith
  have hzero : ∀ᵐ x ∂μ, (φ x - ψ x) * (p₁ x - c * p₀ x) = 0 := by
    have h0 : ∫ x, (φ x - ψ x) * (p₁ x - c * p₀ x) ∂μ = 0 :=
      le_antisymm hle (integral_nonneg_of_ae hpt)
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hpt hint).mp h0] with x hx
    simpa using hx
  refine ⟨hzero, ?_, ?_⟩
  · filter_upwards [hsp1, hzero] with x hx1 hxz hcmp
    have hlt : c * p₀ x < p₁ x := (hreal1 x).mp hcmp
    rw [hx1 hcmp] at hxz
    have := (mul_eq_zero.mp hxz).resolve_right (by linarith)
    linarith
  · filter_upwards [hsp0, hzero] with x hx0 hxz hcmp
    have hlt : p₁ x < c * p₀ x := (hreal0 x).mp hcmp
    rw [hx0 hcmp] at hxz
    have := (mul_eq_zero.mp hxz).resolve_right (by linarith)
    linarith

/-- A test of Neyman–Pearson shape at the infinite threshold has size `0`: it rejects only
where the null density vanishes. -/
private lemma powerAgainst_eq_zero_of_shape_top {μ : Measure 𝓧}
    {P₀ : Measure 𝓧} {p₀ p₁ : 𝓧 → ℝ} (h₀ : HasDensity μ p₀ P₀) {φ : 𝓧 → ℝ}
    (hshape : HasNPShape μ p₀ p₁ ⊤ φ) : powerAgainst P₀ φ = 0 := by
  have hp0nn := h₀.2.1
  have hφp0z : (fun x => φ x * p₀ x) =ᵐ[μ] 0 := by
    filter_upwards [hshape.2] with x hx0
    change φ x * p₀ x = 0
    rcases eq_or_lt_of_le (hp0nn x) with h | h
    · rw [← h, mul_zero]
    · have hc2 : ENNReal.ofReal (p₁ x) < ⊤ * ENNReal.ofReal (p₀ x) := by
        rw [ENNReal.top_mul (by simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; exact h)]
        exact ENNReal.ofReal_lt_top
      rw [hx0 hc2, zero_mul]
  rw [powerAgainst_eq h₀ φ, integral_congr_ae hφp0z]; simp

/-- **Necessity, infinite threshold** (the `α = 0` corner of `npShape_of_maxPower_finite`). -/
private lemma npShape_of_maxPower_top (μ : Measure 𝓧) [SigmaFinite μ]
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} (h₀ : HasDensity μ p₀ P₀) (h₁ : HasDensity μ p₁ P₁)
    {φ ψ : 𝓧 → ℝ} (hφc : IsCriticalFn φ) (hψc : IsCriticalFn ψ)
    (hshape : HasNPShape μ p₀ p₁ ⊤ φ)
    (hsize : powerAgainst P₀ ψ ≤ powerAgainst P₀ φ)
    (hpow : powerAgainst P₁ φ ≤ powerAgainst P₁ ψ) :
    HasNPShape μ p₀ p₁ ⊤ ψ := by
  have hp0nn := h₀.2.1; have hp1nn := h₁.2.1
  obtain ⟨hsp1, hsp0⟩ := hshape
  have hp0i : Integrable p₀ μ := hasDensity_integrable h₀
  have hp1i : Integrable p₁ μ := hasDensity_integrable h₁
  have hpAφ0 : powerAgainst P₀ φ = 0 :=
    powerAgainst_eq_zero_of_shape_top h₀ ⟨hsp1, hsp0⟩
  -- The competitor also puts no mass where the null density is positive.
  have hψp0nn : 0 ≤ᵐ[μ] fun x => ψ x * p₀ x :=
    Filter.Eventually.of_forall fun x => mul_nonneg (hψc.2 x).1 (hp0nn x)
  have hψp0i : Integrable (fun x => ψ x * p₀ x) μ := integrable_crit_mul hp0i hψc
  have hψp0z : (fun x => ψ x * p₀ x) =ᵐ[μ] 0 := by
    have hle : ∫ x, ψ x * p₀ x ∂μ ≤ 0 := by
      rw [← powerAgainst_eq h₀ ψ]; rw [hpAφ0] at hsize; exact hsize
    exact (integral_eq_zero_iff_of_nonneg_ae hψp0nn hψp0i).mp
      (le_antisymm hle (integral_nonneg_of_ae hψp0nn))
  -- The difference of powers is a nonnegative integrand with nonpositive integral.
  have hpt : 0 ≤ᵐ[μ] fun x => (φ x - ψ x) * p₁ x := by
    filter_upwards [hsp1, hsp0, hψp0z] with x hx1 hx0 hxψ0
    change 0 ≤ (φ x - ψ x) * p₁ x
    rcases eq_or_lt_of_le (hp0nn x) with hp0 | hp0
    · rcases eq_or_lt_of_le (hp1nn x) with hp1 | hp1
      · rw [← hp1]; simp
      · have hc1 : (⊤ : ℝ≥0∞) * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x) := by
          rw [← hp0, ENNReal.ofReal_zero, mul_zero]
          exact ENNReal.ofReal_pos.mpr hp1
        rw [hx1 hc1]
        exact mul_nonneg (by linarith [(hψc.2 x).2]) (le_of_lt hp1)
    · have hc2 : ENNReal.ofReal (p₁ x) < ⊤ * ENNReal.ofReal (p₀ x) := by
        rw [ENNReal.top_mul (by simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp0)]
        exact ENNReal.ofReal_lt_top
      have hψ0 : ψ x = 0 := by
        simp only [Pi.zero_apply] at hxψ0
        exact (mul_eq_zero.mp hxψ0).resolve_right (ne_of_gt hp0)
      rw [hx0 hc2, hψ0]; simp
  have hφp1 := integrable_crit_mul hp1i hφc
  have hψp1 := integrable_crit_mul hp1i hψc
  have hint : Integrable (fun x => (φ x - ψ x) * p₁ x) μ :=
    (hφp1.sub hψp1).congr
      (Filter.Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  have key : ∫ x, (φ x - ψ x) * p₁ x ∂μ = powerAgainst P₁ φ - powerAgainst P₁ ψ := by
    rw [powerAgainst_eq h₁ φ, powerAgainst_eq h₁ ψ, ← integral_sub hφp1 hψp1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hzero : ∀ᵐ x ∂μ, (φ x - ψ x) * p₁ x = 0 := by
    have h0 : ∫ x, (φ x - ψ x) * p₁ x ∂μ = 0 :=
      le_antisymm (by rw [key]; linarith) (integral_nonneg_of_ae hpt)
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hpt hint).mp h0] with x hx
    simpa using hx
  refine ⟨?_, ?_⟩
  · filter_upwards [hsp1, hzero] with x hx1 hxz hcmp
    have hp1pos : 0 < p₁ x := by
      by_contra hle
      exact absurd hcmp (by simp [ENNReal.ofReal_of_nonpos (not_lt.mp hle)])
    rw [hx1 hcmp] at hxz
    have := (mul_eq_zero.mp hxz).resolve_right (ne_of_gt hp1pos)
    linarith
  · filter_upwards [hψp0z] with x hxψ0 hcmp
    have hp0pos : 0 < p₀ x := by
      rcases eq_or_lt_of_le (hp0nn x) with h | h
      · exact absurd hcmp (by rw [← h]; simp)
      · exact h
    simp only [Pi.zero_apply] at hxψ0
    exact (mul_eq_zero.mp hxψ0).resolve_right (ne_of_gt hp0pos)

/-- The combined fundamental inequality for an arbitrary (possibly infinite) threshold. -/
private lemma np_fundamental (μ : Measure 𝓧) [SigmaFinite μ]
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} (h₀ : HasDensity μ p₀ P₀) (h₁ : HasDensity μ p₁ P₁)
    {C : ℝ≥0∞} {φ ψ : 𝓧 → ℝ}
    (hφc : IsCriticalFn φ) (hψc : IsCriticalFn ψ)
    (hshape : HasNPShape μ p₀ p₁ C φ)
    (hsize : powerAgainst P₀ ψ ≤ powerAgainst P₀ φ) :
    powerAgainst P₁ ψ ≤ powerAgainst P₁ φ := by
  rcases eq_or_ne C ⊤ with hC | hC
  · subst hC; exact np_fundamental_top μ P₀ P₁ h₀ h₁ hφc hψc hshape hsize
  · exact np_fundamental_finite μ P₀ P₁ h₀ h₁ hC hφc hψc hshape hsize

/-- The likelihood-ratio test has (exact, everywhere) Neyman–Pearson shape. -/
private lemma hasNPShape_npTest (μ : Measure 𝓧) (p₀ p₁ : 𝓧 → ℝ) (C : ℝ≥0∞) (γ : ℝ) :
    HasNPShape μ p₀ p₁ C (npTest p₀ p₁ C γ) := by
  refine ⟨Filter.Eventually.of_forall fun x hx => ?_, Filter.Eventually.of_forall fun x hx => ?_⟩
  · show npTest p₀ p₁ C γ x = 1
    unfold npTest; rw [if_pos hx]
  · show npTest p₀ p₁ C γ x = 0
    unfold npTest; rw [if_neg (not_lt.mpr hx.le), if_neg (ne_of_lt hx)]

/-- The likelihood-ratio test with a `[0,1]` boundary weight is a critical function. -/
private lemma isCriticalFn_npTest {p₀ p₁ : 𝓧 → ℝ} (hp0 : Measurable p₀) (hp1 : Measurable p₁)
    {C : ℝ≥0∞} {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    IsCriticalFn (npTest p₀ p₁ C γ) := by
  refine ⟨?_, fun x => ?_⟩
  · unfold npTest
    refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
    · exact measurableSet_lt (measurable_const.mul hp0.ennreal_ofReal) hp1.ennreal_ofReal
    · exact measurableSet_eq_fun hp1.ennreal_ofReal (measurable_const.mul hp0.ennreal_ofReal)
  · unfold npTest
    split_ifs
    · exact ⟨zero_le_one, le_refl 1⟩
    · exact hγ
    · exact ⟨le_refl 0, zero_le_one⟩

/-- The `μ`-density of a probability measure vanishes exactly off its support: the set where
the density is `0` carries no `P`-mass. -/
private lemma density_null {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    (h : HasDensity μ p P) : P {x | p x = 0} = 0 := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  have hs : MeasurableSet {x | p x = 0} := measurableSet_eq_fun hmeas measurable_const
  rw [hPeq, withDensity_apply _ hs]
  refine setLIntegral_eq_zero hs ?_
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  simp [hx]

/-- The power of the likelihood-ratio test against `P₀` splits into the mass of the strict
rejection region plus `γ` times the mass of the boundary set. -/
private lemma powerAgainst_npTest_eq {p₀ p₁ : 𝓧 → ℝ} {P₀ : Measure 𝓧}
    [IsProbabilityMeasure P₀] (hp0 : Measurable p₀) (hp1 : Measurable p₁)
    (C : ℝ≥0∞) (γ : ℝ) :
    powerAgainst P₀ (npTest p₀ p₁ C γ)
      = (P₀ {x | C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x)}).toReal
        + γ * (P₀ {x | ENNReal.ofReal (p₁ x) = C * ENNReal.ofReal (p₀ x)}).toReal := by
  set R := {x | C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x)} with hRdef
  set B := {x | ENNReal.ofReal (p₁ x) = C * ENNReal.ofReal (p₀ x)} with hBdef
  have hRmeas : MeasurableSet R :=
    measurableSet_lt (measurable_const.mul hp0.ennreal_ofReal) hp1.ennreal_ofReal
  have hBmeas : MeasurableSet B :=
    measurableSet_eq_fun hp1.ennreal_ofReal (measurable_const.mul hp0.ennreal_ofReal)
  have hsplit : npTest p₀ p₁ C γ = fun x =>
      R.indicator (1 : 𝓧 → ℝ) x + γ * B.indicator (1 : 𝓧 → ℝ) x := by
    funext x
    show (if C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x) then (1 : ℝ)
      else if ENNReal.ofReal (p₁ x) = C * ENNReal.ofReal (p₀ x) then γ else 0) = _
    by_cases hR : x ∈ R
    · have hxR : C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x) := hR
      have hnB : x ∉ B := fun he => absurd ((he : _) ▸ hxR) (lt_irrefl _)
      rw [Set.indicator_of_mem hR, Set.indicator_of_notMem hnB, if_pos hxR]; simp
    · have hxR : ¬ C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x) := hR
      rw [Set.indicator_of_notMem hR, if_neg hxR]
      by_cases hB : x ∈ B
      · have hxB : ENNReal.ofReal (p₁ x) = C * ENNReal.ofReal (p₀ x) := hB
        rw [Set.indicator_of_mem hB, if_pos hxB]; simp
      · have hxB : ¬ ENNReal.ofReal (p₁ x) = C * ENNReal.ofReal (p₀ x) := hB
        rw [Set.indicator_of_notMem hB, if_neg hxB]; simp
  have hR1 : Integrable (R.indicator (1 : 𝓧 → ℝ)) P₀ :=
    (show Integrable (1 : 𝓧 → ℝ) P₀ from integrable_const 1).indicator hRmeas
  have hB1 : Integrable (fun x => γ * B.indicator (1 : 𝓧 → ℝ) x) P₀ :=
    ((show Integrable (1 : 𝓧 → ℝ) P₀ from integrable_const 1).indicator hBmeas).const_mul γ
  unfold powerAgainst
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => congrFun hsplit x)),
    integral_add hR1 hB1, integral_indicator_one hRmeas, integral_const_mul,
    integral_indicator_one hBmeas]
  simp only [measureReal_def]

/-- **Existence (i).** For every level `α ∈ [0,1]` there are a threshold `C` and a
boundary weight `γ ∈ [0,1]` for which the likelihood-ratio test has size **exactly** `α`
and is most powerful at that level. The corner cases `α = 0` and `α = 1` are covered by
the extended threshold (`C = ∞`, resp. `C = 0`). -/
theorem exists_mostPowerful
    -- USER-INPUT: dominating measure, σ-finite (free choice; `μ = P₀ + P₁` always works)
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the simple null and simple alternative, given as probability measures
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    -- USER-INPUT: the two densities, supplied by the caller together with the model
    {p₀ p₁ : 𝓧 → ℝ}
    -- USER-INPUT: `P₀` possesses the density `p₀` with respect to `μ`
    (h₀ : HasDensity μ p₀ P₀)
    -- USER-INPUT: `P₁` possesses the density `p₁` with respect to `μ`
    (h₁ : HasDensity μ p₁ P₁)
    -- USER-INPUT: the nominal level, a free choice in the closed unit interval
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (C : ℝ≥0∞) (γ : ℝ), γ ∈ Set.Icc (0 : ℝ) 1 ∧
      powerAgainst P₀ (npTest p₀ p₁ C γ) = α ∧
      IsMostPowerful P₀ P₁ α (npTest p₀ p₁ C γ) := by
  obtain ⟨hα0, hα1⟩ := hα
  -- The optimality half, built directly from the fundamental inequality.
  have mp : ∀ (C : ℝ≥0∞) (γ : ℝ), γ ∈ Set.Icc (0 : ℝ) 1 →
      powerAgainst P₀ (npTest p₀ p₁ C γ) = α →
      IsMostPowerful P₀ P₁ α (npTest p₀ p₁ C γ) := by
    intro C γ hγ hsize
    refine ⟨isCriticalFn_npTest h₀.1 h₁.1 hγ, hsize.le, fun ψ hψ hψs => ?_⟩
    exact np_fundamental μ P₀ P₁ h₀ h₁ (isCriticalFn_npTest h₀.1 h₁.1 hγ) hψ
      (hasNPShape_npTest μ p₀ p₁ C γ) (by rw [hsize]; exact hψs)
  rcases eq_or_lt_of_le hα0 with hα0' | hα0'
  · -- `α = 0`: reject only on the `P₀`-null set `{p₀ = 0, p₁ > 0}`, via `C = ∞`.
    have hpe : powerAgainst P₀ (npTest p₀ p₁ ⊤ 0) = α := by
      rw [powerAgainst_npTest_eq h₀.1 h₁.1 ⊤ 0]
      have hR0 : P₀ {x | (⊤ : ℝ≥0∞) * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x)} = 0 := by
        refine measure_mono_null (fun x hx => ?_) (density_null h₀)
        simp only [Set.mem_setOf_eq] at hx ⊢
        by_contra hne
        have hpos : 0 < p₀ x := lt_of_le_of_ne (h₀.2.1 x) (Ne.symm hne)
        rw [ENNReal.top_mul (by simpa using (ENNReal.ofReal_pos.mpr hpos).ne')] at hx
        exact not_top_lt hx
      rw [hR0]; simp only [ENNReal.toReal_zero, zero_mul, add_zero]; exact hα0'
    exact ⟨⊤, 0, ⟨le_refl 0, zero_le_one⟩, hpe, mp ⊤ 0 ⟨le_refl 0, zero_le_one⟩ hpe⟩
  rcases eq_or_lt_of_le hα1 with hα1' | hα1'
  · -- `α = 1`: reject everywhere, via `C = 0, γ = 1`.
    have hone : npTest p₀ p₁ 0 1 = fun _ => (1 : ℝ) := by
      funext x
      show npTest p₀ p₁ 0 1 x = 1
      unfold npTest
      simp only [zero_mul]
      by_cases h : ENNReal.ofReal (p₁ x) = 0
      · rw [if_neg (by rw [h]; exact lt_irrefl 0), if_pos h]
      · rw [if_pos (lt_of_le_of_ne (zero_le) (Ne.symm h))]
    have hpe : powerAgainst P₀ (npTest p₀ p₁ 0 1) = α := by
      rw [hone]; unfold powerAgainst; rw [hα1']; simp
    exact ⟨0, 1, ⟨zero_le_one, le_refl 1⟩, hpe, mp 0 1 ⟨zero_le_one, le_refl 1⟩ hpe⟩
  -- `0 < α < 1`: push the likelihood ratio forward under `P₀` and randomize on its atom.
  have hrmeas : Measurable fun x => p₁ x / p₀ x := h₁.1.div h₀.1
  have hrnn : ∀ x, 0 ≤ p₁ x / p₀ x := fun x => div_nonneg (h₁.2.1 x) (h₀.2.1 x)
  set Q : Measure ℝ := P₀.map (fun x => p₁ x / p₀ x) with hQ
  haveI hQprob : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map hrmeas.aemeasurable
  obtain ⟨c, γ, hγ0, hγ1, hcrit⟩ := exists_critical_constants Q hα0' hα1'
  have hsr : MeasurableSet {x : ℝ | c < x} := measurableSet_Ioi
  have hse : MeasurableSet {x : ℝ | x = c} := by
    rw [show {x : ℝ | x = c} = {c} from by ext x; simp [eq_comm]]
    exact measurableSet_singleton c
  have hQIio : Q (Set.Iio 0) = 0 := by
    rw [hQ, Measure.map_apply hrmeas measurableSet_Iio]
    have : (fun x => p₁ x / p₀ x) ⁻¹' Set.Iio 0 = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hrnn x
    rw [this, measure_empty]
  have hc0 : 0 ≤ c := by
    by_contra hcneg
    push_neg at hcneg
    have hIic : Q (Set.Iic c) = 0 :=
      measure_mono_null (fun y hy => lt_of_le_of_lt hy hcneg) hQIio
    have h1 : Q {x : ℝ | c < x} = 1 := by
      rw [show {x : ℝ | c < x} = (Set.Iic c)ᶜ from (Set.compl_Iic).symm,
        prob_compl_eq_one_sub measurableSet_Iic, hIic, tsub_zero]
    have h2 : Q {x : ℝ | x = c} = 0 := by
      rw [hQ, Measure.map_apply hrmeas hse]
      have : (fun x => p₁ x / p₀ x) ⁻¹' {x : ℝ | x = c} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun he => absurd he (by linarith [hrnn x])
      rw [this, measure_empty]
    rw [h1, h2] at hcrit
    simp only [ENNReal.toReal_one, ENNReal.toReal_zero, mul_zero, add_zero] at hcrit
    linarith
  have hnull : P₀ {x | p₀ x = 0} = 0 := density_null h₀
  have haep : ∀ᵐ x ∂P₀, p₀ x ≠ 0 := ae_iff.mpr (by simpa using hnull)
  have hReq : P₀ {x | ENNReal.ofReal c * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x)}
      = Q {x : ℝ | c < x} := by
    rw [hQ, Measure.map_apply hrmeas hsr]
    refine measure_congr (Filter.eventuallyEq_set.mpr ?_)
    filter_upwards [haep] with x hx
    have hpos : 0 < p₀ x := lt_of_le_of_ne (h₀.2.1 x) (Ne.symm hx)
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [← ENNReal.ofReal_mul hc0,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hc0 hpos.le)]
    exact (lt_div_iff₀ hpos).symm
  have hBeq : P₀ {x | ENNReal.ofReal (p₁ x) = ENNReal.ofReal c * ENNReal.ofReal (p₀ x)}
      = Q {x : ℝ | x = c} := by
    rw [hQ, Measure.map_apply hrmeas hse]
    refine measure_congr (Filter.eventuallyEq_set.mpr ?_)
    filter_upwards [haep] with x hx
    have hpos : 0 < p₀ x := lt_of_le_of_ne (h₀.2.1 x) (Ne.symm hx)
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [← ENNReal.ofReal_mul hc0,
      ENNReal.ofReal_eq_ofReal_iff (h₁.2.1 x) (mul_nonneg hc0 hpos.le), div_eq_iff hpos.ne']
  have hpe : powerAgainst P₀ (npTest p₀ p₁ (ENNReal.ofReal c) γ) = α := by
    rw [powerAgainst_npTest_eq h₀.1 h₁.1 (ENNReal.ofReal c) γ, hReq, hBeq]
    exact hcrit
  exact ⟨ENNReal.ofReal c, γ, ⟨hγ0, hγ1⟩, hpe, mp (ENNReal.ofReal c) γ ⟨hγ0, hγ1⟩ hpe⟩

/-- **Sufficiency (ii).** Any critical function of Neyman–Pearson shape whose size equals
`α` is most powerful at level `α`. Only the shape and the size enter: the values of `φ`
on the boundary set `{p₁ = C·p₀}` are unconstrained. -/
theorem isMostPowerful_of_npShape
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the simple null and simple alternative
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} {C : ℝ≥0∞} {α : ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: `P₀` possesses the density `p₀` with respect to `μ`
    (h₀ : HasDensity μ p₀ P₀)
    -- USER-INPUT: `P₁` possesses the density `p₁` with respect to `μ`
    (h₁ : HasDensity μ p₁ P₁)
    -- USER-INPUT: the competitor class is the critical functions, so `φ` must be one
    (hφ : IsCriticalFn φ)
    -- USER-INPUT: the test has size exactly `α` — condition (3.7) of the classical form
    (hsize : powerAgainst P₀ φ = α)
    -- USER-INPUT: the test has likelihood-ratio shape at threshold `C` — condition (3.8)
    (hshape : HasNPShape μ p₀ p₁ C φ) :
    IsMostPowerful P₀ P₁ α φ := by
  refine ⟨hφ, hsize.le, fun ψ hψ hψsize => ?_⟩
  refine np_fundamental μ P₀ P₁ h₀ h₁ hφ hψ hshape ?_
  rw [hsize]; exact hψsize

/-- **Sufficiency (ii), specialized.** The likelihood-ratio test itself is most powerful
at its own size, for every threshold `C` and every boundary weight `γ ∈ [0,1]`. -/
theorem isMostPowerful_npTest
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the simple null and simple alternative
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} {C : ℝ≥0∞} {γ α : ℝ}
    -- USER-INPUT: `P₀` possesses the density `p₀` with respect to `μ`
    (h₀ : HasDensity μ p₀ P₀)
    -- USER-INPUT: `P₁` possesses the density `p₁` with respect to `μ`
    (h₁ : HasDensity μ p₁ P₁)
    -- USER-INPUT: the boundary weight is a probability, so that `npTest` is a test
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the threshold/weight pair realizes size exactly `α`
    (hsize : powerAgainst P₀ (npTest p₀ p₁ C γ) = α) :
    IsMostPowerful P₀ P₁ α (npTest p₀ p₁ C γ) :=
  isMostPowerful_of_npShape μ P₀ P₁ h₀ h₁ (isCriticalFn_npTest h₀.1 h₁.1 hγ) hsize
    (hasNPShape_npTest μ p₀ p₁ C γ)

/-- **Necessity (iii).** A most powerful level-`α` test has likelihood-ratio shape almost
everywhere for some threshold `C`; and its size is exactly `α` **unless** there already
exists a test of size strictly below `α` whose power against the alternative is `1`.

Both clauses are transcribed as stated: the shape is only claimed `μ`-a.e. (nothing is
claimed on the boundary set), and the exact-size clause is guarded by its escape
hypothesis rather than asserted unconditionally. -/
theorem npTest_necessity
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the simple null and simple alternative
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} {α : ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: `P₀` possesses the density `p₀` with respect to `μ`
    (h₀ : HasDensity μ p₀ P₀)
    -- USER-INPUT: `P₁` possesses the density `p₁` with respect to `μ`
    (h₁ : HasDensity μ p₁ P₁)
    -- USER-INPUT: `φ` is most powerful at level `α` — the property being reverse-engineered
    (hφ : IsMostPowerful P₀ P₁ α φ) :
    (∃ C : ℝ≥0∞, HasNPShape μ p₀ p₁ C φ) ∧
      ((¬ ∃ ψ, IsCriticalFn ψ ∧ powerAgainst P₀ ψ < α ∧ powerAgainst P₁ ψ = 1) →
        powerAgainst P₀ φ = α) := by
  obtain ⟨hφc, hφlevel, hφmax⟩ := hφ
  have hp1i : Integrable p₁ μ := hasDensity_integrable h₁
  have hp1one : ∫ x, p₁ x ∂μ = 1 := hasDensity_integral_one h₁
  -- The size of a critical function lies in `[0,1]`, so `α ≥ 0` and `α' := min α 1 ∈ [0,1]`.
  have hsize0 : 0 ≤ powerAgainst P₀ φ :=
    integral_nonneg fun x => (hφc.2 x).1
  have hsize1 : powerAgainst P₀ φ ≤ 1 := by
    calc powerAgainst P₀ φ ≤ ∫ _ : 𝓧, (1 : ℝ) ∂P₀ :=
          integral_mono (by
            refine (integrable_const (1 : ℝ)).mono' hφc.1.aestronglyMeasurable
              (Filter.Eventually.of_forall fun x => ?_)
            rw [Real.norm_eq_abs, abs_of_nonneg (hφc.2 x).1]; exact (hφc.2 x).2)
            (integrable_const 1) (fun x => (hφc.2 x).2)
      _ = 1 := by simp
  have hα0 : 0 ≤ α := le_trans hsize0 hφlevel
  set α' := min α 1 with hα'def
  have hα' : α' ∈ Set.Icc (0 : ℝ) 1 := ⟨le_min hα0 zero_le_one, min_le_right _ _⟩
  have hφlevel' : powerAgainst P₀ φ ≤ α' := le_min hφlevel hsize1
  -- The likelihood-ratio test of size exactly `α'`.
  obtain ⟨C, γ, hγ, hlrsize, hlrMP⟩ := exists_mostPowerful μ P₀ P₁ h₀ h₁ hα'
  set χ := npTest p₀ p₁ C γ with hχdef
  have hχc : IsCriticalFn χ := isCriticalFn_npTest h₀.1 h₁.1 hγ
  have hχshape : HasNPShape μ p₀ p₁ C χ := hasNPShape_npTest μ p₀ p₁ C γ
  -- Both tests are most powerful at level `α'`, so their powers agree.
  have hpow1 : powerAgainst P₁ χ ≤ powerAgainst P₁ φ :=
    hφmax χ hχc (by rw [hlrsize]; exact min_le_left _ _)
  have hpow2 : powerAgainst P₁ φ ≤ powerAgainst P₁ χ := hlrMP.2.2 φ hφc hφlevel'
  have hpoweq : powerAgainst P₁ χ = powerAgainst P₁ φ := le_antisymm hpow1 hpow2
  have hsizele : powerAgainst P₀ φ ≤ powerAgainst P₀ χ := by rw [hlrsize]; exact hφlevel'
  -- The necessity core, in whichever of the two threshold regimes applies.
  rcases eq_or_ne C ⊤ with hCtop | hCfin
  · -- `C = ⊤`: the shape forces size `0`, hence `α' = 0`, and with `0 ≤ α` this pins `α = 0`.
    rw [hCtop] at hχshape
    refine ⟨⟨⊤, npShape_of_maxPower_top μ P₀ P₁ h₀ h₁ hχc hφc hχshape hsizele hpoweq.le⟩, ?_⟩
    intro _
    have hα'0 : α' = 0 := by
      rw [← hlrsize]; exact powerAgainst_eq_zero_of_shape_top h₀ hχshape
    rw [hα'def] at hα'0
    have hαle : α ≤ 0 := by
      rcases le_total α 1 with h | h
      · rw [min_eq_left h] at hα'0; exact hα'0.le
      · rw [min_eq_right h] at hα'0; exact absurd hα'0 one_ne_zero
    have hα00 : α = 0 := le_antisymm hαle hα0
    rw [hα00] at hφlevel ⊢
    exact le_antisymm hφlevel hsize0
  · obtain ⟨hprod, hshape⟩ :=
      npShape_of_maxPower_finite μ P₀ P₁ h₀ h₁ hCfin hχc hφc hχshape hsizele hpoweq.le
    refine ⟨⟨C, hshape⟩, ?_⟩
    intro hno
    -- If `α > 1` the constant test `ψ ≡ 1` already refutes the escape hypothesis.
    rcases lt_or_ge 1 α with hα1 | hαle1
    · exact absurd ⟨fun _ => (1 : ℝ), ⟨measurable_const, fun _ => ⟨zero_le_one, le_rfl⟩⟩,
        by unfold powerAgainst; simpa using hα1, by unfold powerAgainst; simp⟩ hno
    have hαeq : α' = α := min_eq_left hαle1
    by_contra hne
    have hlt : powerAgainst P₀ φ < α := lt_of_le_of_ne hφlevel hne
    -- The vanishing of the fundamental integrand gives `C.toReal · (α − size φ) = 0`.
    have hp0i : Integrable p₀ μ := hasDensity_integrable h₀
    have hgap : C.toReal * (powerAgainst P₀ χ - powerAgainst P₀ φ) = 0 := by
      have h0 : ∫ x, (χ x - φ x) * (p₁ x - C.toReal * p₀ x) ∂μ = 0 := by
        rw [integral_congr_ae (g := fun _ : 𝓧 => (0 : ℝ))
          (by filter_upwards [hprod] with x hx; exact hx)]
        simp
      have hAB : Integrable (fun x => χ x * p₁ x - φ x * p₁ x) μ :=
        (integrable_crit_mul hp1i hχc).sub (integrable_crit_mul hp1i hφc)
      have hDE : Integrable (fun x => C.toReal * (χ x * p₀ x - φ x * p₀ x)) μ :=
        ((integrable_crit_mul hp0i hχc).sub
          (integrable_crit_mul hp0i hφc)).const_mul C.toReal
      have key : ∫ x, (χ x - φ x) * (p₁ x - C.toReal * p₀ x) ∂μ
          = (powerAgainst P₁ χ - powerAgainst P₁ φ)
            - C.toReal * (powerAgainst P₀ χ - powerAgainst P₀ φ) := by
        rw [powerAgainst_eq h₁ χ, powerAgainst_eq h₁ φ, powerAgainst_eq h₀ χ,
          powerAgainst_eq h₀ φ,
          ← integral_sub (integrable_crit_mul hp1i hχc) (integrable_crit_mul hp1i hφc),
          ← integral_sub (integrable_crit_mul hp0i hχc) (integrable_crit_mul hp0i hφc),
          ← integral_const_mul, ← integral_sub hAB hDE]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      rw [key, hpoweq, sub_self, zero_sub, neg_eq_zero] at h0
      exact h0
    rw [hlrsize, hαeq] at hgap
    -- Strict slack at the boundary therefore forces the threshold to be `0`.
    have hCzero : C = 0 := by
      by_contra hC0
      rcases mul_eq_zero.mp hgap with h | h
      · exact absurd h (ne_of_gt (ENNReal.toReal_pos hC0 hCfin))
      · linarith
    -- With `C = 0` the likelihood-ratio test — hence `φ` — has power `1` against `P₁`.
    have hχp1 : ∀ x, χ x * p₁ x = p₁ x := by
      intro x
      rw [hχdef, hCzero]
      unfold npTest
      simp only [zero_mul]
      by_cases h : ENNReal.ofReal (p₁ x) = 0
      · rw [if_neg (by rw [h]; exact lt_irrefl 0), if_pos h]
        have hz : p₁ x = 0 :=
          le_antisymm (by simpa using ENNReal.ofReal_eq_zero.mp h) (h₁.2.1 x)
        rw [hz, mul_zero]
      · rw [if_pos (lt_of_le_of_ne (zero_le) (Ne.symm h)), one_mul]
    have hχpow : powerAgainst P₁ χ = 1 := by
      rw [powerAgainst_eq h₁ χ, integral_congr_ae (Filter.Eventually.of_forall hχp1), hp1one]
    exact hno ⟨φ, hφc, hlt, by rw [← hpoweq]; exact hχpow⟩

/-- **Strict unbiasedness.** For `0 < α < 1` the power of a most powerful level-`α` test
strictly exceeds `α`, unless the null and the alternative are the same distribution. -/
theorem power_gt_alpha_of_ne
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the simple null and simple alternative
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} {α : ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: `P₀` possesses the density `p₀` with respect to `μ`
    (h₀ : HasDensity μ p₀ P₀)
    -- USER-INPUT: `P₁` possesses the density `p₁` with respect to `μ`
    (h₁ : HasDensity μ p₁ P₁)
    -- USER-INPUT: nondegenerate level; at `α ∈ {0,1}` the conclusion genuinely fails
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: `φ` is most powerful at level `α`
    (hφ : IsMostPowerful P₀ P₁ α φ)
    -- USER-INPUT: the two hypotheses are distinct — the stated exception of the result
    (hne : P₀ ≠ P₁) :
    α < powerAgainst P₁ φ := by
  obtain ⟨hφc, hφlevel, hφmax⟩ := hφ
  have hαIcc : α ∈ Set.Icc (0 : ℝ) 1 := ⟨hα₀.le, hα₁.le⟩
  -- The constant test `ψ ≡ α` has size and power both equal to `α`.
  have hψαc : IsCriticalFn (fun _ : 𝓧 => α) := ⟨measurable_const, fun _ => hαIcc⟩
  have hψα0 : powerAgainst P₀ (fun _ : 𝓧 => α) = α := by unfold powerAgainst; simp
  have hψα1 : powerAgainst P₁ (fun _ : 𝓧 => α) = α := by unfold powerAgainst; simp
  by_contra hcon
  push_neg at hcon
  have hge : α ≤ powerAgainst P₁ φ := by
    have h := hφmax _ hψαc (le_of_eq hψα0)
    rwa [hψα1] at h
  have hpowφ : powerAgainst P₁ φ = α := le_antisymm hcon hge
  -- The likelihood-ratio test of size exactly `α` therefore also has power exactly `α`.
  obtain ⟨C, γ, hγ, hlrsize, hlrMP⟩ := exists_mostPowerful μ P₀ P₁ h₀ h₁ hαIcc
  set χ := npTest p₀ p₁ C γ with hχdef
  have hχc : IsCriticalFn χ := isCriticalFn_npTest h₀.1 h₁.1 hγ
  have hχshape : HasNPShape μ p₀ p₁ C χ := hasNPShape_npTest μ p₀ p₁ C γ
  have hχpow : powerAgainst P₁ χ = α := by
    refine le_antisymm ?_ ?_
    · have h := hφmax χ hχc (le_of_eq hlrsize); rwa [hpowφ] at h
    · have h := hlrMP.2.2 _ hψαc (le_of_eq hψα0); rwa [hψα1] at h
  have hCfin : C ≠ ⊤ := by
    intro hCtop
    rw [hCtop] at hχshape
    have h := powerAgainst_eq_zero_of_shape_top h₀ hχshape
    rw [hlrsize] at h
    exact absurd h (ne_of_gt hα₀)
  -- Both tests being extremal, the fundamental integrand vanishes a.e.
  obtain ⟨hprod, -⟩ := npShape_of_maxPower_finite μ P₀ P₁ h₀ h₁ hCfin hχc hψαc hχshape
    (by rw [hlrsize, hψα0]) (by rw [hχpow, hψα1])
  have hprod' : ∀ᵐ x ∂μ, (χ x - α) * (p₁ x - C.toReal * p₀ x) = 0 := hprod
  -- Away from the boundary the two tests differ, so the likelihood ratio is constant a.e.
  have hae : ∀ᵐ x ∂μ, p₁ x = C.toReal * p₀ x := by
    filter_upwards [hprod'] with x hx
    rcases lt_trichotomy (C.toReal * p₀ x) (p₁ x) with hlt | heq | hgt
    · have h1 : χ x = 1 := by
        rw [hχdef]
        unfold npTest
        rw [if_pos ((npCompare_iff hCfin (h₀.2.1 x) (h₁.2.1 x)).1.mpr hlt)]
      rw [h1] at hx
      have := (mul_eq_zero.mp hx).resolve_left (by linarith)
      linarith
    · exact heq.symm
    · have hstrict : ENNReal.ofReal (p₁ x) < C * ENNReal.ofReal (p₀ x) :=
        (npCompare_iff hCfin (h₀.2.1 x) (h₁.2.1 x)).2.mpr hgt
      have h0 : χ x = 0 := by
        rw [hχdef]
        unfold npTest
        rw [if_neg (not_lt.mpr hstrict.le), if_neg (ne_of_lt hstrict)]
      rw [h0] at hx
      have := (mul_eq_zero.mp hx).resolve_left (by linarith)
      linarith
  -- Integrating identifies the constant as `1`, so the two densities agree a.e.
  have hcone : C.toReal = 1 := by
    have h := integral_congr_ae hae
    rw [hasDensity_integral_one h₁, integral_const_mul, hasDensity_integral_one h₀,
      mul_one] at h
    exact h.symm
  refine hne ?_
  rw [h₀.2.2, h₁.2.2]
  refine withDensity_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx, hcone, one_mul]

/-- **The degenerate case, stated honestly.** When the null and the alternative coincide,
every most powerful level-`α` test has power exactly `α`: no test can do better than the
constant test `φ ≡ α`, and the constant test shows `α` is attained. Together with
`power_gt_alpha_of_ne` this settles the power of a most powerful test in both cases. -/
theorem power_eq_alpha_of_eq
    -- USER-INPUT: the common distribution under the null and the alternative
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {α : ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: nondegenerate level
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: `φ` is most powerful at level `α`
    (hφ : IsMostPowerful P₀ P₁ α φ)
    -- USER-INPUT: the excluded case of the previous theorem
    (heq : P₀ = P₁) :
    powerAgainst P₁ φ = α := by
  obtain ⟨hφc, hle, hmax⟩ := hφ
  have hconst : IsCriticalFn (fun _ : 𝓧 => α) := ⟨measurable_const, fun _ => ⟨hα₀.le, hα₁.le⟩⟩
  have hcP0 : powerAgainst P₀ (fun _ : 𝓧 => α) = α := by
    unfold powerAgainst
    rw [integral_const]; simp
  have hcP1 : powerAgainst P₁ (fun _ : 𝓧 => α) = α := by
    unfold powerAgainst
    rw [integral_const]; simp
  have h1 : powerAgainst P₁ (fun _ : 𝓧 => α) ≤ powerAgainst P₁ φ := hmax _ hconst hcP0.le
  rw [hcP1] at h1
  have hp01 : powerAgainst P₁ φ = powerAgainst P₀ φ := by rw [heq]
  linarith [hle]

end StatLean.HypothesisTesting
