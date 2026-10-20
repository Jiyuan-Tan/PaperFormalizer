module
public import StatLean.HypothesisTesting.MLR.Defs
public import StatLean.HypothesisTesting.NeymanPearson.Lemma
public import StatLean.PointEstimation.ExponentialFamily.Defs
public import StatLean.PointEstimation.ExponentialFamily.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# One-sided testing under a monotone likelihood ratio

For a real parameter and a family with monotone likelihood ratio in a statistic `T`, the
one-sided problem `H : θ ≤ θ₀` against `K : θ > θ₀` has a **uniformly** most powerful
solution — the same test works against every alternative — namely
$$ \varphi(x) = 1 \ \text{ if } T(x) > C, \qquad \gamma \ \text{ if } T(x) = C,
\qquad 0 \ \text{ if } T(x) < C, $$
with `C` and `γ` fixed by the exact-size requirement `E_{θ₀}φ = α`. Beyond optimality, the
test's power function is strictly increasing wherever it is not already `0` or `1`, the
test is simultaneously UMP for every shifted null, and it minimizes the rejection
probability below `θ₀`.

Contents:
* `oneSidedTest T C γ` — the test displayed above;
* `isUMP_oneSided` — existence of `(C, γ)` with size exactly `α`, and uniform optimality;
* `power_strictMono_oneSided` — strict monotonicity of the power function;
* `isUMP_oneSided_shifted` — the same test is UMP at every other null boundary `θ'`, at
  the level it happens to have there;
* `power_min_oneSided` — among all tests of size exactly `α` at `θ₀`, it minimizes the
  rejection probability at every `θ < θ₀`;
* `testRisk`, `essentiallyComplete_oneSidedTest` — the family of one-sided tests is an
  essentially complete class for the two-decision problem with monotone losses;
* `hasMLR_expFamily`, `isUMP_oneSided_expFamily` — the one-parameter exponential family
  has monotone likelihood ratio in its natural statistic, hence a UMP one-sided test;
* `integral_mono_of_hasMLR` — a monotone statistic has monotone expectation.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.4 (Distributions with Monotone Likelihood Ratio), Theorem 3.4.1 (existence
of a UMP one-sided test under a monotone likelihood ratio), Corollary 3.4.1 (the one-parameter
exponential-family case) and Theorem 3.4.2 (the one-sided tests form an essentially complete
class). (`TSH4 §3.4 Thm 3.4.1, Cor 3.4.1, Thm 3.4.2`.)

**Proof formalization notes.**
* The frozen `HasMLR` is the division-free cross-product condition; it does **not**
  include the classical requirement that `P_θ ≠ P_{θ'}` for `θ < θ'`. That requirement is
  irrelevant for existence and optimality, but it is exactly what makes the power function
  *strictly* increasing (a constant family satisfies `HasMLR` vacuously and has constant
  power). It is therefore carried as an explicit hypothesis of
  `power_strictMono_oneSided` only, and nowhere else.
* The threshold `C` here is a real number, not an extended one: it is a level of the
  statistic `T`, not a likelihood-ratio threshold. Extended thresholds appear only at the
  likelihood-ratio layer.
* The risk of a test is written directly in terms of its power,
  `R(θ, φ) = β_φ(θ)·L₁(θ) + (1 - β_φ(θ))·L₀(θ)`, which agrees with the integral form
  `∫ p_θ {φ L₁ + (1-φ)L₀} dμ` because `∫ p_θ dμ = 1`.
* The minimal-essential-completeness clause (which additionally assumes that the support
  `{x : p_θ(x) > 0}` does not depend on `θ`) is not stated here; only essential
  completeness is.
* The decreasing-`Q` half of the exponential-family corollary is obtained by applying the
  increasing case to `-T`, and is not stated separately.
* `integral_mono_of_hasMLR` is stated in the one-dimensional form, generalized from
  "nondecreasing in `x`" to "nondecreasing along `T`" (taking `𝓧 = ℝ`, `T = id` recovers
  the printed statement). The `n`-sample clause — a function nondecreasing in each of `n`
  independent coordinates has nondecreasing expectation — is a separate induction and is
  not stated here.

**Bibliographic comments.** Monotone likelihood ratio, the resulting uniformly most
powerful one-sided tests, and the complete-class property of the family they form are due
to S. Karlin and H. Rubin ("The theory of decision procedures for distributions with
monotone likelihood ratio," *Ann. Math. Statist.* **27** (1956), 272–299); the
one-parameter exponential-family case and the underlying optimality argument go back to
J. Neyman and E. S. Pearson ("Contributions to the theory of testing statistical
hypotheses," *Stat. Res. Mem.* **1** (1936), 1–37).
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation

/-- The real inner product on `ℝ` is multiplication. -/
private lemma real_inner_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  have h1 : ⟪(1 : ℝ), b⟫_ℝ = b := by
    have h := real_inner_smul_right (1 : ℝ) 1 b
    simpa [real_inner_self_eq_norm_mul_norm] using h
  have h2 := real_inner_smul_left (1 : ℝ) b a
  simpa [h1] using h2

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **one-sided test** based on the statistic `T` with critical value `C` and boundary
randomization `γ`: reject when `T > C`, reject with probability `γ` when `T = C`, accept
when `T < C`. No constraint on `γ` is imposed by the definition; for `γ ∉ [0,1]` the
result is not a critical function, so the theorems carry `γ ∈ [0,1]` explicitly. -/
noncomputable def oneSidedTest (T : 𝓧 → ℝ) (C γ : ℝ) : 𝓧 → ℝ := fun x =>
  if C < T x then 1 else if T x = C then γ else 0

/-- The **risk** of a test in the two-decision problem: `L₀ θ` is the loss incurred by
accepting the null at `θ` and `L₁ θ` the loss incurred by rejecting it, so the risk is the
power-weighted average `β_φ(θ)·L₁(θ) + (1 - β_φ(θ))·L₀(θ)`. For a probability model this
is the integral form `∫ p_θ {φ L₁ + (1-φ) L₀} dμ`. -/
noncomputable def testRisk {Θ : Type*} (P : Θ → Measure 𝓧) (L₀ L₁ : Θ → ℝ) (φ : 𝓧 → ℝ)
    (θ : Θ) : ℝ :=
  power P φ θ * L₁ θ + (1 - power P φ θ) * L₀ θ

/-- A density of a probability measure is integrable (local copy of the NP-layer lemma). -/
private lemma density_integrable {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    [IsProbabilityMeasure P] (h : HasDensity μ p P) : Integrable p μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  have h1 : (μ.withDensity fun x => ENNReal.ofReal (p x)) Set.univ = 1 := by
    rw [← hPeq]; exact measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [h1]; exact ENNReal.one_lt_top

/-- Expectation against a density-carrying measure equals the integral against the density. -/
private lemma integral_density_eq {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    (h : HasDensity μ p P) (ψ : 𝓧 → ℝ) : ∫ x, ψ x ∂P = ∫ x, ψ x * p x ∂μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  rw [hPeq, integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hnn x)]; ring

/-- The density integrates to `1`. -/
private lemma density_integral_one {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    [IsProbabilityMeasure P] (h : HasDensity μ p P) : ∫ x, p x ∂μ = 1 := by
  have h1 : ∫ x, (1 : ℝ) ∂P = ∫ x, (1 : ℝ) * p x ∂μ := integral_density_eq h (fun _ => 1)
  simp only [one_mul] at h1
  rw [← h1]; simp

/-- If `ψ` is `P`-integrable and `P` has density `p`, then `ψ·p` is `μ`-integrable. -/
private lemma density_mul_integrable {μ : Measure 𝓧} {p ψ : 𝓧 → ℝ} {P : Measure 𝓧}
    (h : HasDensity μ p P) (hψ : Integrable ψ P) : Integrable (fun x => ψ x * p x) μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  rw [hPeq] at hψ
  refine ((integrable_withDensity_iff hmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hψ).congr ?_
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (hnn x)]

/-- The one-sided test is measurable when `T` is. -/
private lemma measurable_oneSidedTest {T : 𝓧 → ℝ} (hT : Measurable T) (C γ : ℝ) :
    Measurable (oneSidedTest T C γ) := by
  unfold oneSidedTest
  refine Measurable.ite (measurableSet_lt measurable_const hT) measurable_const
    (Measurable.ite (measurableSet_eq_fun hT measurable_const) measurable_const measurable_const)

/-- The one-sided test with `γ ∈ [0,1]` is a critical function. -/
private lemma isCriticalFn_oneSidedTest {T : 𝓧 → ℝ} (hT : Measurable T) {C γ : ℝ}
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1) : IsCriticalFn (oneSidedTest T C γ) := by
  refine ⟨measurable_oneSidedTest hT C γ, fun x => ?_⟩
  unfold oneSidedTest
  split_ifs
  · exact ⟨zero_le_one, le_refl 1⟩
  · exact hγ
  · exact ⟨le_refl 0, zero_le_one⟩

/-- The one-sided test is nondecreasing along `T`. -/
private lemma oneSidedTest_mono {T : 𝓧 → ℝ} {C γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    {x y : 𝓧} (hxy : T x ≤ T y) : oneSidedTest T C γ x ≤ oneSidedTest T C γ y := by
  unfold oneSidedTest
  by_cases hbx : C < T x
  · rw [if_pos hbx, if_pos (lt_of_lt_of_le hbx hxy)]
  · rw [if_neg hbx]
    by_cases hex : T x = C
    · rw [if_pos hex]
      have hyC : C ≤ T y := hex ▸ hxy
      by_cases hby : C < T y
      · rw [if_pos hby]; exact hγ.2
      · rw [if_neg hby, if_pos (le_antisymm (not_lt.mp hby) hyC)]
    · rw [if_neg hex]
      split_ifs
      · exact zero_le_one
      · exact hγ.1
      · exact le_refl 0

/-- The power of the one-sided test splits into the tail mass plus `γ` times the atom mass. -/
private lemma power_oneSidedTest_eq {P : ℝ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {T : 𝓧 → ℝ} (hT : Measurable T) (C γ : ℝ) (θ : ℝ) :
    power P (oneSidedTest T C γ) θ
      = (P θ {x | C < T x}).toReal + γ * (P θ {x | T x = C}).toReal := by
  set R := {x | C < T x} with hRdef
  set B := {x | T x = C} with hBdef
  have hRmeas : MeasurableSet R := measurableSet_lt measurable_const hT
  have hBmeas : MeasurableSet B := measurableSet_eq_fun hT measurable_const
  have hsplit : oneSidedTest T C γ = fun x =>
      R.indicator (1 : 𝓧 → ℝ) x + γ * B.indicator (1 : 𝓧 → ℝ) x := by
    funext x
    show (if C < T x then (1 : ℝ) else if T x = C then γ else 0) = _
    by_cases hR : x ∈ R
    · have hxR : C < T x := hR
      have hnB : x ∉ B := fun he => absurd (he : T x = C) (ne_of_gt hxR)
      rw [Set.indicator_of_mem hR, Set.indicator_of_notMem hnB, if_pos hxR]; simp
    · have hxR : ¬ C < T x := hR
      rw [Set.indicator_of_notMem hR, if_neg hxR]
      by_cases hB : x ∈ B
      · have hxB : T x = C := hB
        rw [Set.indicator_of_mem hB, if_pos hxB]; simp
      · have hxB : ¬ T x = C := hB
        rw [Set.indicator_of_notMem hB, if_neg hxB]; simp
  have hR1 : Integrable (R.indicator (1 : 𝓧 → ℝ)) (P θ) :=
    (show Integrable (1 : 𝓧 → ℝ) (P θ) from integrable_const 1).indicator hRmeas
  have hB1 : Integrable (fun x => γ * B.indicator (1 : 𝓧 → ℝ) x) (P θ) :=
    ((show Integrable (1 : 𝓧 → ℝ) (P θ) from integrable_const 1).indicator hBmeas).const_mul γ
  unfold power
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => congrFun hsplit x)),
    integral_add hR1 hB1, integral_indicator_one hRmeas, integral_const_mul,
    integral_indicator_one hBmeas]
  simp only [measureReal_def]

/-- **Existence of the separating multiplier.** Given the monotone likelihood ratio, a
threshold `C`, and one point of positive `θ`-density with `T ≥ C`, there is a real `k ≥ 0`
that separates the two densities across the level set: `p_{θ'} ≤ k·p_θ` where `T ≤ C` and
`k·p_θ ≤ p_{θ'}` where `T ≥ C`. This is the division-free Karlin–Rubin separation. -/
private lemma exists_sep_const {μ : Measure 𝓧} {P : ℝ → Measure 𝓧} {p : ℝ → 𝓧 → ℝ}
    (hp : ∀ θ, HasDensity μ (p θ) (P θ)) {T : 𝓧 → ℝ} (hMLR : HasMLR p T)
    {θ θ' : ℝ} (hlt : θ < θ') {C : ℝ} (hz : ∃ z, C ≤ T z ∧ 0 < p θ z) :
    ∃ k : ℝ, 0 ≤ k ∧ (∀ x, T x ≤ C → p θ' x ≤ k * p θ x) ∧
      (∀ x, C ≤ T x → k * p θ x ≤ p θ' x) := by
  obtain ⟨z₀, hz₀C, hz₀pos⟩ := hz
  have hnn' : ∀ x, 0 ≤ p θ' x := (hp θ').2.1
  have hnn : ∀ x, 0 ≤ p θ x := (hp θ).2.1
  set S : Set ℝ := {r | ∃ x, T x ≤ C ∧ 0 < p θ x ∧ r = p θ' x / p θ x} with hSdef
  set ratz := p θ' z₀ / p θ z₀ with hratz
  have hratz_nn : 0 ≤ ratz := div_nonneg (hnn' z₀) hz₀pos.le
  -- `ratz` bounds `insert 0 S` above, so the supremum exists.
  have hUB : ∀ r ∈ insert (0 : ℝ) S, r ≤ ratz := by
    intro r hr
    rcases hr with hr0 | ⟨x, hxC, hxpos, hxeq⟩
    · exact hr0 ▸ hratz_nn
    · rw [hxeq, hratz, div_le_div_iff₀ hxpos hz₀pos]
      have := hMLR hlt x z₀ (le_trans hxC hz₀C)
      nlinarith [this]
  have hbdd : BddAbove (insert (0 : ℝ) S) := ⟨ratz, hUB⟩
  have hne : (insert (0 : ℝ) S).Nonempty := ⟨0, Set.mem_insert 0 S⟩
  set k := sSup (insert (0 : ℝ) S) with hkdef
  have hk0 : 0 ≤ k := le_csSup hbdd (Set.mem_insert 0 S)
  refine ⟨k, hk0, ?_, ?_⟩
  · intro x hxC
    rcases eq_or_lt_of_le (hnn x) with hpx | hpx
    · -- `p θ x = 0`: MLR against `z₀` forces `p θ' x = 0`.
      have hkey := hMLR hlt x z₀ (le_trans hxC hz₀C)
      rw [← hpx, zero_mul] at hkey
      have : p θ' x * p θ z₀ ≤ 0 := hkey
      have hpx'0 : p θ' x = 0 :=
        le_antisymm (nonpos_of_mul_nonpos_left this hz₀pos) (hnn' x)
      rw [hpx'0, ← hpx, mul_zero]
    · have hmem : p θ' x / p θ x ∈ insert (0 : ℝ) S :=
        Set.mem_insert_iff.mpr (Or.inr ⟨x, hxC, hpx, rfl⟩)
      have hle : p θ' x / p θ x ≤ k := le_csSup hbdd hmem
      rw [div_le_iff₀ hpx] at hle
      linarith [hle]
  · intro x hxC
    rcases eq_or_lt_of_le (hnn x) with hpx | hpx
    · rw [← hpx, mul_zero]; exact hnn' x
    · -- `p θ x > 0`: `p θ' x / p θ x` is an upper bound of `insert 0 S`, so `k ≤` it.
      have hUBx : ∀ r ∈ insert (0 : ℝ) S, r ≤ p θ' x / p θ x := by
        intro r hr
        rcases hr with hr0 | ⟨y, hyC, hypos, hyeq⟩
        · exact hr0 ▸ div_nonneg (hnn' x) hpx.le
        · rw [hyeq, div_le_div_iff₀ hypos hpx]
          have := hMLR hlt y x (le_trans hyC hxC)
          nlinarith [this]
      have hle : k ≤ p θ' x / p θ x := csSup_le hne hUBx
      rw [le_div_iff₀ hpx] at hle
      linarith [hle]

/-- **The one-sided test has Neyman–Pearson shape** for `θ < θ'`, at the multiplier `k`
produced by `exists_sep_const`. -/
private lemma hasNPShape_oneSided {μ : Measure 𝓧} {P : ℝ → Measure 𝓧} {p : ℝ → 𝓧 → ℝ}
    (hp : ∀ θ, HasDensity μ (p θ) (P θ)) {T : 𝓧 → ℝ} (hMLR : HasMLR p T)
    {θ θ' : ℝ} (hlt : θ < θ') {C : ℝ} (γ : ℝ) (hz : ∃ z, C ≤ T z ∧ 0 < p θ z) :
    ∃ K : ℝ≥0∞, HasNPShape μ (p θ) (p θ') K (oneSidedTest T C γ) := by
  obtain ⟨k, hk0, hle, hge⟩ := exists_sep_const hp hMLR hlt hz
  have hnn : ∀ x, 0 ≤ p θ x := (hp θ).2.1
  refine ⟨ENNReal.ofReal k, ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun x hx => ?_
    rw [← ENNReal.ofReal_mul hk0] at hx
    have hlt' : k * p θ x < p θ' x := by
      by_contra hcon
      push_neg at hcon
      exact absurd hx (not_lt.mpr (ENNReal.ofReal_le_ofReal hcon))
    have hTC : C < T x := by
      by_contra hcon
      exact absurd (hle x (not_lt.mp hcon)) (not_le.mpr hlt')
    show oneSidedTest T C γ x = 1
    unfold oneSidedTest; rw [if_pos hTC]
  · refine Filter.Eventually.of_forall fun x hx => ?_
    rw [← ENNReal.ofReal_mul hk0] at hx
    have hlt' : p θ' x < k * p θ x := by
      by_contra hcon
      push_neg at hcon
      exact absurd hx (not_lt.mpr (ENNReal.ofReal_le_ofReal hcon))
    have hTC : T x < C := by
      by_contra hcon
      exact absurd (hge x (not_lt.mp hcon)) (not_le.mpr hlt')
    show oneSidedTest T C γ x = 0
    unfold oneSidedTest; rw [if_neg (not_lt.mpr hTC.le), if_neg (ne_of_lt hTC)]

/-- **The one-sided test is most powerful** for `P θ` against `P θ'` (`θ < θ'`) at its own
size, provided the `θ`-density is positive somewhere above the threshold. -/
private lemma isMostPowerful_oneSided {μ : Measure 𝓧} [SigmaFinite μ] {P : ℝ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {p : ℝ → 𝓧 → ℝ} (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    {T : 𝓧 → ℝ} (hT : Measurable T) (hMLR : HasMLR p T) {θ θ' : ℝ} (hlt : θ < θ')
    {C γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hz : ∃ z, C ≤ T z ∧ 0 < p θ z) :
    IsMostPowerful (P θ) (P θ') (power P (oneSidedTest T C γ) θ) (oneSidedTest T C γ) := by
  obtain ⟨K, hshape⟩ := hasNPShape_oneSided hp hMLR hlt γ hz
  exact isMostPowerful_of_npShape μ (P θ) (P θ') (hp θ) (hp θ')
    (isCriticalFn_oneSidedTest hT hγ) rfl hshape

/-- If the one-sided test has positive power at `θ`, some point above the threshold has
positive `θ`-density. -/
private lemma exists_pos_density_of_power_pos {μ : Measure 𝓧} {P : ℝ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {p : ℝ → 𝓧 → ℝ} (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    {T : 𝓧 → ℝ} (hT : Measurable T) {C γ : ℝ} {θ : ℝ}
    (hpow : 0 < power P (oneSidedTest T C γ) θ) : ∃ z, C ≤ T z ∧ 0 < p θ z := by
  by_contra hcon
  push_neg at hcon
  -- `p θ = 0` on `{T ≥ C}`, hence both the tail and the atom carry no `P θ`-mass.
  obtain ⟨hmeas, hnn, hPeq⟩ := hp θ
  have hnull : (P θ) {x | C ≤ T x} = 0 := by
    rw [hPeq, withDensity_apply _ (measurableSet_le measurable_const hT)]
    refine setLIntegral_eq_zero (measurableSet_le measurable_const hT) fun x hx => ?_
    simp only [Set.mem_setOf_eq] at hx
    have : p θ x ≤ 0 := hcon x hx
    simp [le_antisymm this (hnn x)]
  have hRle : (P θ) {x | C < T x} = 0 :=
    measure_mono_null (Set.setOf_subset_setOf.2 fun x hx => le_of_lt hx) hnull
  have hBle : (P θ) {x | T x = C} = 0 :=
    measure_mono_null (Set.setOf_subset_setOf.2 fun x hx => le_of_eq hx.symm) hnull
  rw [power_oneSidedTest_eq hT C γ θ, hRle, hBle] at hpow
  simp at hpow

/-- **Monotone statistics have monotone expectations.** Under a monotone likelihood ratio
in `T`, the expectation of any function that is nondecreasing along `T` is a nondecreasing
function of the parameter. Taking `𝓧 = ℝ` and `T = id` gives the classical statement for a
nondecreasing `ψ`. -/
theorem integral_mono_of_hasMLR
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic and the monotone-likelihood-ratio property
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T)
    -- USER-INPUT: the integrand
    (ψ : 𝓧 → ℝ) (hψ : Measurable ψ)
    -- USER-INPUT: it is nondecreasing along `T` (for `T = id`: nondecreasing)
    (hmono : ∀ x y, T x ≤ T y → ψ x ≤ ψ y)
    -- USER-INPUT: integrability under every member, so both sides are defined
    (hint : ∀ θ, Integrable ψ (P θ)) :
    Monotone fun θ => ∫ x, ψ x ∂(P θ) := by
  intro θ θ' hθθ'
  show ∫ x, ψ x ∂(P θ) ≤ ∫ x, ψ x ∂(P θ')
  rcases eq_or_lt_of_le hθθ' with h | hlt
  · rw [h]
  -- `θ < θ'`: the double-integral correlation identity `2·(D_θ' − D_θ) = ∫∫ F ≥ 0`.
  rw [integral_density_eq (hp θ) ψ, integral_density_eq (hp θ') ψ]
  have ha : Integrable (p θ) μ := density_integrable (hp θ)
  have hb : Integrable (p θ') μ := density_integrable (hp θ')
  have hψa : Integrable (fun x => ψ x * p θ x) μ := density_mul_integrable (hp θ) (hint θ)
  have hψb : Integrable (fun x => ψ x * p θ' x) μ := density_mul_integrable (hp θ') (hint θ')
  have hone_a : ∫ x, p θ x ∂μ = 1 := density_integral_one (hp θ)
  have hone_b : ∫ x, p θ' x ∂μ = 1 := density_integral_one (hp θ')
  have i1 : Integrable (fun z : 𝓧 × 𝓧 => p θ z.1 * (ψ z.2 * p θ' z.2)) (μ.prod μ) :=
    Integrable.mul_prod ha hψb
  have i2 : Integrable (fun z : 𝓧 × 𝓧 => p θ' z.1 * (ψ z.2 * p θ z.2)) (μ.prod μ) :=
    Integrable.mul_prod hb hψa
  have i3 : Integrable (fun z : 𝓧 × 𝓧 => ψ z.1 * p θ z.1 * p θ' z.2) (μ.prod μ) :=
    Integrable.mul_prod hψa hb
  have i4 : Integrable (fun z : 𝓧 × 𝓧 => ψ z.1 * p θ' z.1 * p θ z.2) (μ.prod μ) :=
    Integrable.mul_prod hψb ha
  have hFnn : 0 ≤ᵐ[μ.prod μ] fun z : 𝓧 × 𝓧 =>
      p θ z.1 * (ψ z.2 * p θ' z.2) - p θ' z.1 * (ψ z.2 * p θ z.2)
        - ψ z.1 * p θ z.1 * p θ' z.2 + ψ z.1 * p θ' z.1 * p θ z.2 := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    show (0 : ℝ) ≤ p θ z.1 * (ψ z.2 * p θ' z.2) - p θ' z.1 * (ψ z.2 * p θ z.2)
        - ψ z.1 * p θ z.1 * p θ' z.2 + ψ z.1 * p θ' z.1 * p θ z.2
    have key : p θ z.1 * (ψ z.2 * p θ' z.2) - p θ' z.1 * (ψ z.2 * p θ z.2)
        - ψ z.1 * p θ z.1 * p θ' z.2 + ψ z.1 * p θ' z.1 * p θ z.2
        = (ψ z.2 - ψ z.1) * (p θ z.1 * p θ' z.2 - p θ' z.1 * p θ z.2) := by ring
    rw [key]
    rcases le_total (T z.1) (T z.2) with hle | hle
    · exact mul_nonneg (by linarith [hmono z.1 z.2 hle])
        (by linarith [hMLR hlt z.1 z.2 hle])
    · refine mul_nonneg_of_nonpos_of_nonpos (by linarith [hmono z.2 z.1 hle]) ?_
      nlinarith [hMLR hlt z.2 z.1 hle]
  -- Compute the four product integrals separately, then combine.
  have e1 : ∫ z : 𝓧 × 𝓧, p θ z.1 * (ψ z.2 * p θ' z.2) ∂(μ.prod μ)
      = ∫ x, ψ x * p θ' x ∂μ := by
    rw [integral_prod_mul (p θ) (fun y => ψ y * p θ' y), hone_a, one_mul]
  have e2 : ∫ z : 𝓧 × 𝓧, p θ' z.1 * (ψ z.2 * p θ z.2) ∂(μ.prod μ)
      = ∫ x, ψ x * p θ x ∂μ := by
    rw [integral_prod_mul (p θ') (fun y => ψ y * p θ y), hone_b, one_mul]
  have e3 : ∫ z : 𝓧 × 𝓧, ψ z.1 * p θ z.1 * p θ' z.2 ∂(μ.prod μ)
      = ∫ x, ψ x * p θ x ∂μ := by
    rw [integral_prod_mul (fun x => ψ x * p θ x) (p θ'), hone_b, mul_one]
  have e4 : ∫ z : 𝓧 × 𝓧, ψ z.1 * p θ' z.1 * p θ z.2 ∂(μ.prod μ)
      = ∫ x, ψ x * p θ' x ∂μ := by
    rw [integral_prod_mul (fun x => ψ x * p θ' x) (p θ), hone_a, mul_one]
  have hf12 : Integrable (fun z : 𝓧 × 𝓧 => p θ z.1 * (ψ z.2 * p θ' z.2)
      - p θ' z.1 * (ψ z.2 * p θ z.2)) (μ.prod μ) := i1.sub i2
  have hf123 : Integrable (fun z : 𝓧 × 𝓧 => p θ z.1 * (ψ z.2 * p θ' z.2)
      - p θ' z.1 * (ψ z.2 * p θ z.2) - ψ z.1 * p θ z.1 * p θ' z.2) (μ.prod μ) := hf12.sub i3
  have hFint : (0 : ℝ) ≤ ∫ z : 𝓧 × 𝓧,
      (p θ z.1 * (ψ z.2 * p θ' z.2) - p θ' z.1 * (ψ z.2 * p θ z.2)
        - ψ z.1 * p θ z.1 * p θ' z.2 + ψ z.1 * p θ' z.1 * p θ z.2) ∂(μ.prod μ) :=
    integral_nonneg_of_ae hFnn
  rw [integral_add hf123 i4, integral_sub hf12 i3, integral_sub i1 i2, e1, e2, e3, e4] at hFint
  linarith [hFint]


/-- **Existence of a UMP one-sided test.** Under a monotone likelihood ratio in `T` there
are a critical value `C` and a boundary weight `γ ∈ [0,1]` for which the one-sided test has
size exactly `α` at `θ₀` and is uniformly most powerful at level `α` for `H : θ ≤ θ₀`
against `K : θ > θ₀`. -/
theorem isUMP_oneSided
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model, a family of probability measures indexed by a real parameter
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: its densities with respect to `μ`
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic in which the likelihood ratio is monotone
    (T : 𝓧 → ℝ) (hT : Measurable T)
    -- USER-INPUT: the monotone-likelihood-ratio property — the whole content of the setup
    (hMLR : HasMLR p T)
    -- USER-INPUT: the null boundary and the nominal level. The endpoints are genuinely
    -- excluded: the exact-size clause `power = α` is unattainable by a one-sided test at
    -- `α ∈ {0,1}` whenever `T` is essentially unbounded in the relevant tail (e.g.
    -- `𝓧 = ℝ`, `T = id`, `P θ = 𝒩(θ,1)`, where `1 − Φ(C) > 0` for every real `C`), so the
    -- former `Set.Icc` reading was FALSE at the two endpoints. This also matches
    -- `exists_critical_constants`, which requires `0 < α < 1`.
    (θ₀ : ℝ) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C γ : ℝ, γ ∈ Set.Icc (0 : ℝ) 1 ∧
      power P (oneSidedTest T C γ) θ₀ = α ∧
      IsUMP P (Set.Iic θ₀) (Set.Ioi θ₀) α (oneSidedTest T C γ) := by
  obtain ⟨hα0', hα1'⟩ := hα
  by_cases hmid : 0 < α ∧ α < 1
  · obtain ⟨hα0, hα1⟩ := hmid
    -- Boundary constants from the `T`-marginal under `θ₀`.
    haveI : IsProbabilityMeasure ((P θ₀).map T) :=
      Measure.isProbabilityMeasure_map hT.aemeasurable
    obtain ⟨C, γ, hγ0, hγ1, hcrit⟩ := exists_critical_constants ((P θ₀).map T) hα0 hα1
    have hγ' : γ ∈ Set.Icc (0 : ℝ) 1 := ⟨hγ0, hγ1⟩
    set φ := oneSidedTest T C γ with hφdef
    have hmR : MeasurableSet {x : ℝ | C < x} := measurableSet_Ioi
    have hmB : MeasurableSet {x : ℝ | x = C} := by
      rw [show {x : ℝ | x = C} = {C} from by ext x; simp [eq_comm]]
      exact measurableSet_singleton C
    have hReq : (P θ₀) {x | C < T x} = ((P θ₀).map T) {x : ℝ | C < x} := by
      rw [Measure.map_apply hT hmR]; rfl
    have hBeq : (P θ₀) {x | T x = C} = ((P θ₀).map T) {x : ℝ | x = C} := by
      rw [Measure.map_apply hT hmB]; rfl
    have hsize : power P φ θ₀ = α := by
      rw [hφdef, power_oneSidedTest_eq hT C γ θ₀, hReq, hBeq]; exact hcrit
    have hφc : IsCriticalFn φ := isCriticalFn_oneSidedTest hT hγ'
    have hφint : ∀ θ, Integrable φ (P θ) := fun θ =>
      (integrable_const (1 : ℝ)).mono' hφc.1.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hφc.2 x).1]; exact (hφc.2 x).2)
    have hmono : Monotone fun θ => power P φ θ :=
      integral_mono_of_hasMLR μ P p hp T hT hMLR φ hφc.1
        (fun x y h => oneSidedTest_mono hγ' h) hφint
    refine ⟨C, γ, hγ', hsize, hφc, ?_, ?_⟩
    · intro θ hθ
      exact le_trans (hmono (Set.mem_Iic.mp hθ)) hsize.le
    · intro ψ hψ hψlevel θ' hθ'
      have hlt : θ₀ < θ' := Set.mem_Ioi.mp hθ'
      have hz : ∃ z, C ≤ T z ∧ 0 < p θ₀ z :=
        exists_pos_density_of_power_pos hp hT (by rw [hsize]; exact hα0)
      have hMP := isMostPowerful_oneSided hp hT hMLR hlt hγ' hz
      have hlevel0 : powerAgainst (P θ₀) ψ ≤ power P φ θ₀ := by
        rw [hsize]; exact hψlevel θ₀ (Set.mem_Iic.mpr le_rfl)
      exact hMP.2.2 ψ hψ hlevel0
  · -- Impossible: `hα : α ∈ Set.Ioo 0 1` is exactly `0 < α ∧ α < 1`. (The endpoints were
    -- removed from the hypothesis because the exact-size clause is genuinely unattainable
    -- there — see the note on `hα` above.)
    exact absurd ⟨hα0', hα1'⟩ hmid

/-- **Strict monotonicity of the power function.** On the set of parameter values where
the power is neither `0` nor `1`, the power function of the one-sided test is strictly
increasing.

The distinctness hypothesis `P θ ≠ P θ'` for `θ < θ'` is part of the classical definition
of a monotone likelihood ratio but not of the division-free `HasMLR`; it is what rules out
a constant family, for which the conclusion is false. -/
theorem power_strictMono_oneSided
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic and the monotone-likelihood-ratio property
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T)
    -- USER-INPUT: distinctness of the members — the clause of the classical MLR
    -- definition that `HasMLR` omits; without it the family may be constant
    (hdist : ∀ θ θ' : ℝ, θ < θ' → P θ ≠ P θ')
    -- USER-INPUT: the critical value and the boundary weight of the test under study
    {C γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ θ θ' : ℝ, θ < θ' →
      0 < power P (oneSidedTest T C γ) θ → power P (oneSidedTest T C γ) θ < 1 →
      0 < power P (oneSidedTest T C γ) θ' → power P (oneSidedTest T C γ) θ' < 1 →
      power P (oneSidedTest T C γ) θ < power P (oneSidedTest T C γ) θ' := by
  -- The argument runs entirely through the Karlin–Rubin separation constant `k` of
  -- `exists_sep_const` — no appeal to the (still open) strict-unbiasedness lemma of the
  -- Neyman–Pearson layer is needed. Write `A = β(θ)`, `B = β(θ')`. Because `p_{θ'} ≤ k p_θ`
  -- below the threshold, `k p_θ ≤ p_{θ'}` above it, and hence `p_{θ'} = k p_θ` *on* it, the
  -- two integrands
  --   `φ·(p_{θ'} − k p_θ)`   and   `(1 − φ)·(k p_θ − p_{θ'})`
  -- are pointwise nonnegative (each vanishes identically on two of the three level sets of
  -- `φ` and is a signed separation inequality on the third). Integrating gives
  --   `B ≥ k·A`  and  `B ≥ 1 − k·(1 − A)`.
  -- For `k > 1` the first is strict because `A > 0`; for `k < 1` the second is strict
  -- because `A < 1`. At `k = 1` the two bounds degenerate to `B ≥ A`, and equality forces
  -- both nonnegative integrands to vanish a.e.; their difference is `p_{θ'} − p_θ`, so
  -- `P θ = P θ'`, contradicting `hdist`. This is exactly where the non-degeneracy clause of
  -- the classical monotone-likelihood-ratio definition is consumed.
  intro θ θ' hlt ha0 ha1 _ _
  set φ := oneSidedTest T C γ with hφdef
  have ha0' : 0 < power P (oneSidedTest T C γ) θ := by rw [← hφdef]; exact ha0
  have hφc : IsCriticalFn φ := isCriticalFn_oneSidedTest hT hγ
  have hφint : ∀ ϑ : ℝ, Integrable φ (P ϑ) := fun ϑ =>
    (integrable_const (1 : ℝ)).mono' hφc.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hφc.2 x).1]; exact (hφc.2 x).2)
  have haeq : power P φ θ = ∫ x, φ x * p θ x ∂μ := by
    unfold power; exact integral_density_eq (hp θ) φ
  have hbeq : power P φ θ' = ∫ x, φ x * p θ' x ∂μ := by
    unfold power; exact integral_density_eq (hp θ') φ
  rw [haeq, hbeq]
  rw [haeq] at ha0 ha1
  -- The separation constant at the threshold `C`.
  obtain ⟨k, hk0, hkle, hkge⟩ :=
    exists_sep_const hp hMLR hlt (exists_pos_density_of_power_pos hp hT ha0')
  -- The three level sets of `φ`, and the exact identity on the boundary one.
  have hφ0 : ∀ x, T x < C → φ x = 0 := by
    intro x hx
    rw [hφdef]; unfold oneSidedTest
    rw [if_neg (not_lt.mpr hx.le), if_neg (ne_of_lt hx)]
  have hφ1 : ∀ x, C < T x → φ x = 1 := by
    intro x hx
    rw [hφdef]; unfold oneSidedTest
    rw [if_pos hx]
  have hEq : ∀ x, T x = C → p θ' x = k * p θ x := fun x hx =>
    le_antisymm (hkle x hx.le) (hkge x hx.ge)
  -- Integrability bookkeeping.
  have hiA : Integrable (fun x => φ x * p θ x) μ := density_mul_integrable (hp θ) (hφint θ)
  have hiB : Integrable (fun x => φ x * p θ' x) μ := density_mul_integrable (hp θ') (hφint θ')
  have hipθ : Integrable (p θ) μ := density_integrable (hp θ)
  have hipθ' : Integrable (p θ') μ := density_integrable (hp θ')
  have honeθ : ∫ x, p θ x ∂μ = 1 := density_integral_one (hp θ)
  have honeθ' : ∫ x, p θ' x ∂μ = 1 := density_integral_one (hp θ')
  -- The scaled integrands are ascribed explicitly: `Integrable.const_mul` otherwise returns
  -- an un-β-reduced `fun x => k * (fun y => …) x`, which `rw` cannot match.
  have hkA : Integrable (fun x => k * (φ x * p θ x)) μ := hiA.const_mul k
  have hkp : Integrable (fun x => k * p θ x) μ := hipθ.const_mul k
  have hd1 : Integrable (fun x => k * p θ x - p θ' x) μ := hkp.sub hipθ'
  have hd2 : Integrable (fun x => k * (φ x * p θ x) - φ x * p θ' x) μ := hkA.sub hiB
  have hg1i : Integrable (fun x => φ x * p θ' x - k * (φ x * p θ x)) μ := hiB.sub hkA
  have hg2i : Integrable
      (fun x => (k * p θ x - p θ' x) - (k * (φ x * p θ x) - φ x * p θ' x)) μ := hd1.sub hd2
  have e1 : ∫ x, (φ x * p θ' x - k * (φ x * p θ x)) ∂μ
      = (∫ x, φ x * p θ' x ∂μ) - k * ∫ x, φ x * p θ x ∂μ := by
    rw [integral_sub hiB hkA, integral_const_mul]
  have e2 : ∫ x, ((k * p θ x - p θ' x) - (k * (φ x * p θ x) - φ x * p θ' x)) ∂μ
      = (k * (∫ x, p θ x ∂μ) - ∫ x, p θ' x ∂μ)
        - (k * (∫ x, φ x * p θ x ∂μ) - ∫ x, φ x * p θ' x ∂μ) := by
    rw [integral_sub hd1 hd2, integral_sub hkp hipθ', integral_sub hkA hiB,
      integral_const_mul, integral_const_mul]
  -- Pointwise nonnegativity of the two separation integrands.
  have hpt1 : 0 ≤ᵐ[μ] fun x => φ x * p θ' x - k * (φ x * p θ x) := by
    refine Filter.Eventually.of_forall fun x => ?_
    have hrw : φ x * p θ' x - k * (φ x * p θ x) = φ x * (p θ' x - k * p θ x) := by ring
    simp only [Pi.zero_apply]
    rw [hrw]
    rcases lt_trichotomy (T x) C with h | h | h
    · rw [hφ0 x h]; simp
    · rw [hEq x h]; simp
    · rw [hφ1 x h, one_mul]; linarith [hkge x h.le]
  have hpt2 : 0 ≤ᵐ[μ]
      fun x => (k * p θ x - p θ' x) - (k * (φ x * p θ x) - φ x * p θ' x) := by
    refine Filter.Eventually.of_forall fun x => ?_
    have hrw : (k * p θ x - p θ' x) - (k * (φ x * p θ x) - φ x * p θ' x)
        = (1 - φ x) * (k * p θ x - p θ' x) := by ring
    simp only [Pi.zero_apply]
    rw [hrw]
    rcases lt_trichotomy (T x) C with h | h | h
    · rw [hφ0 x h]; simp only [sub_zero, one_mul]; linarith [hkle x h.le]
    · rw [hEq x h]; simp
    · rw [hφ1 x h]; simp
  have hS1 : 0 ≤ ∫ x, (φ x * p θ' x - k * (φ x * p θ x)) ∂μ := integral_nonneg_of_ae hpt1
  have hS2 : 0 ≤ ∫ x, ((k * p θ x - p θ' x) - (k * (φ x * p θ x) - φ x * p θ' x)) ∂μ :=
    integral_nonneg_of_ae hpt2
  have hS1' : 0 ≤ (∫ x, φ x * p θ' x ∂μ) - k * ∫ x, φ x * p θ x ∂μ := by
    have h := hS1; rw [e1] at h; exact h
  have hS2' : 0 ≤ (k - 1) - (k * (∫ x, φ x * p θ x ∂μ) - ∫ x, φ x * p θ' x ∂μ) := by
    have h := hS2; rw [e2, honeθ, honeθ'] at h; linarith
  rcases lt_trichotomy k 1 with hk | hk | hk
  · -- `k < 1`: the lower bound `B ≥ 1 − k(1 − A)` is strict because `A < 1`.
    nlinarith [mul_pos (sub_pos.mpr hk) (sub_pos.mpr ha1)]
  · -- `k = 1`: equality would force `p_θ = p_{θ'}` a.e., contradicting `hdist`.
    subst hk
    by_contra hcon
    push_neg at hcon
    have hz1 : ∫ x, (φ x * p θ' x - 1 * (φ x * p θ x)) ∂μ = 0 := by rw [e1]; linarith
    have hz2 : ∫ x, ((1 * p θ x - p θ' x) - (1 * (φ x * p θ x) - φ x * p θ' x)) ∂μ = 0 := by
      rw [e2, honeθ, honeθ']; linarith
    have hae1 := (integral_eq_zero_iff_of_nonneg_ae hpt1 hg1i).mp hz1
    have hae2 := (integral_eq_zero_iff_of_nonneg_ae hpt2 hg2i).mp hz2
    have haep : p θ =ᵐ[μ] p θ' := by
      filter_upwards [hae1, hae2] with x hx1 hx2
      simp only [Pi.zero_apply] at hx1 hx2
      linarith
    have hPeq : P θ = P θ' := by
      rw [(hp θ).2.2, (hp θ').2.2]
      exact withDensity_congr_ae (haep.mono fun x hx => by simp only [hx])
    exact absurd hPeq (hdist θ θ' hlt)
  · -- `k > 1`: the lower bound `B ≥ k·A` is strict because `A > 0`.
    nlinarith [mul_pos (sub_pos.mpr hk) ha0]

/-- **The same test is UMP at every null boundary.** For any `θ'`, the one-sided test is
uniformly most powerful for `H' : θ ≤ θ'` against `K' : θ > θ'` at the level it happens to
have there, namely `α' = β(θ')`. -/
theorem isUMP_oneSided_shifted
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic and the monotone-likelihood-ratio property
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T)
    -- USER-INPUT: the critical value and the boundary weight
    {C γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (θ' : ℝ)
    -- USER-INPUT: the boundary density does not vanish on the rejection region — i.e. the
    -- test has positive size at `θ'`. This is genuinely needed: without it the statement is
    -- FALSE. Verified counterexample: `𝓧 = ℝ`, `μ = volume`, `T = id`, reflected shifted
    -- exponential `p θ x = exp (x − θ)·1_{x ≤ θ}` (a genuine MLR family) with `C = θ' + 1`,
    -- so `p θ' = 0` on `{T ≥ C}` and `power P φ θ' = 0`; the level-`0` competitor
    -- `ψ = 1_{x > θ'}` then satisfies `power ψ θ'' > power P φ θ''` for every `θ'' > θ' + 1`,
    -- so `φ` is not UMP. The classical result assumes strictly positive densities.
    (hz : ∃ z, C ≤ T z ∧ 0 < p θ' z) :
    IsUMP P (Set.Iic θ') (Set.Ioi θ') (power P (oneSidedTest T C γ) θ')
      (oneSidedTest T C γ) := by
  set φ := oneSidedTest T C γ with hφdef
  have hφc : IsCriticalFn φ := isCriticalFn_oneSidedTest hT hγ
  have hφint : ∀ θ, Integrable φ (P θ) := fun θ =>
    (integrable_const (1 : ℝ)).mono' hφc.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hφc.2 x).1]; exact (hφc.2 x).2)
  have hmono : Monotone fun θ => power P φ θ :=
    integral_mono_of_hasMLR μ P p hp T hT hMLR φ hφc.1
      (fun x y h => oneSidedTest_mono hγ h) hφint
  refine ⟨hφc, fun θ hθ => hmono (Set.mem_Iic.mp hθ), ?_⟩
  intro ψ hψ hψlevel θ'' hθ''
  have hlt : θ' < θ'' := Set.mem_Ioi.mp hθ''
  -- `hz` (positive boundary density on the rejection region) is now a hypothesis; see the
  -- note on it above for the counterexample showing it cannot be dropped.
  have hMP := isMostPowerful_oneSided hp hT hMLR hlt hγ hz
  exact hMP.2.2 ψ hψ (hψlevel θ' (Set.mem_Iic.mpr le_rfl))

/-- Power of the co-test `1 − g` is `1 −` the power of `g`. -/
private lemma powerAgainst_one_sub {P : Measure 𝓧} [IsProbabilityMeasure P] {g : 𝓧 → ℝ}
    (hg : Integrable g P) : powerAgainst P (fun x => 1 - g x) = 1 - powerAgainst P g := by
  unfold powerAgainst
  rw [integral_sub (integrable_const 1) hg, integral_const]; simp

/-- **Reversed separating multiplier.** For `θ < θ'`, given a point of positive `θ'`-density
with `T ≤ C`, there is `k ≥ 0` with `p_θ' ≤ k·p_θ` where `T ≥ C` and `k·p_θ ≤ p_θ'` where
`T ≤ C` — the mirror of `exists_sep_const`, for the ratio `p_θ'/p_θ` read as *nonincreasing*
below the boundary. -/
private lemma exists_sep_const_rev {μ : Measure 𝓧} {P : ℝ → Measure 𝓧} {p : ℝ → 𝓧 → ℝ}
    (hp : ∀ θ, HasDensity μ (p θ) (P θ)) {T : 𝓧 → ℝ} (hMLR : HasMLR p T)
    {θ θ' : ℝ} (hlt : θ < θ') {C : ℝ} (hz : ∃ z, T z ≤ C ∧ 0 < p θ' z) :
    ∃ k : ℝ, 0 ≤ k ∧ (∀ x, C ≤ T x → p θ x ≤ k * p θ' x) ∧
      (∀ x, T x ≤ C → k * p θ' x ≤ p θ x) := by
  obtain ⟨z₀, hz₀C, hz₀pos⟩ := hz
  have hnn' : ∀ x, 0 ≤ p θ' x := (hp θ').2.1
  have hnn : ∀ x, 0 ≤ p θ x := (hp θ).2.1
  set S : Set ℝ := {r | ∃ x, C ≤ T x ∧ 0 < p θ' x ∧ r = p θ x / p θ' x} with hSdef
  set ratz := p θ z₀ / p θ' z₀ with hratz
  have hratz_nn : 0 ≤ ratz := div_nonneg (hnn z₀) hz₀pos.le
  have hUB : ∀ r ∈ insert (0 : ℝ) S, r ≤ ratz := by
    intro r hr
    rcases hr with hr0 | ⟨x, hxC, hxpos, hxeq⟩
    · exact hr0 ▸ hratz_nn
    · rw [hxeq, hratz, div_le_div_iff₀ hxpos hz₀pos]
      have := hMLR hlt z₀ x (le_trans hz₀C hxC)
      nlinarith [this]
  have hbdd : BddAbove (insert (0 : ℝ) S) := ⟨ratz, hUB⟩
  have hne : (insert (0 : ℝ) S).Nonempty := ⟨0, Set.mem_insert 0 S⟩
  set k := sSup (insert (0 : ℝ) S) with hkdef
  have hk0 : 0 ≤ k := le_csSup hbdd (Set.mem_insert 0 S)
  refine ⟨k, hk0, ?_, ?_⟩
  · intro x hxC
    rcases eq_or_lt_of_le (hnn' x) with hpx | hpx
    · have hkey := hMLR hlt z₀ x (le_trans hz₀C hxC)
      rw [← hpx, mul_zero] at hkey
      have : p θ' z₀ * p θ x ≤ 0 := by nlinarith [hkey]
      have hpx'0 : p θ x = 0 :=
        le_antisymm (nonpos_of_mul_nonpos_right this hz₀pos) (hnn x)
      rw [hpx'0, ← hpx, mul_zero]
    · have hmem : p θ x / p θ' x ∈ insert (0 : ℝ) S :=
        Set.mem_insert_iff.mpr (Or.inr ⟨x, hxC, hpx, rfl⟩)
      have hle : p θ x / p θ' x ≤ k := le_csSup hbdd hmem
      rw [div_le_iff₀ hpx] at hle
      linarith [hle]
  · intro x hxC
    rcases eq_or_lt_of_le (hnn' x) with hpx | hpx
    · rw [← hpx, mul_zero]; exact hnn x
    · have hUBx : ∀ r ∈ insert (0 : ℝ) S, r ≤ p θ x / p θ' x := by
        intro r hr
        rcases hr with hr0 | ⟨y, hyC, hypos, hyeq⟩
        · exact hr0 ▸ div_nonneg (hnn x) hpx.le
        · rw [hyeq, div_le_div_iff₀ hypos hpx]
          have := hMLR hlt x y (le_trans hxC hyC)
          nlinarith [this]
      have hle : k ≤ p θ x / p θ' x := csSup_le hne hUBx
      rw [le_div_iff₀ hpx] at hle
      linarith [hle]

/-- **The co-test `1 − φ` has Neyman–Pearson shape** for the swapped simple problem
`P θ'` (null) against `P θ` (alt), `θ < θ'`, given a positive `θ'`-density point below `C`. -/
private lemma hasNPShape_coOneSided {μ : Measure 𝓧} {P : ℝ → Measure 𝓧} {p : ℝ → 𝓧 → ℝ}
    (hp : ∀ θ, HasDensity μ (p θ) (P θ)) {T : 𝓧 → ℝ} (hMLR : HasMLR p T)
    {θ θ' : ℝ} (hlt : θ < θ') {C : ℝ} (γ : ℝ) (hz : ∃ z, T z ≤ C ∧ 0 < p θ' z) :
    ∃ K : ℝ≥0∞, HasNPShape μ (p θ') (p θ) K (fun x => 1 - oneSidedTest T C γ x) := by
  obtain ⟨k, hk0, hge, hle⟩ := exists_sep_const_rev hp hMLR hlt hz
  refine ⟨ENNReal.ofReal k, ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun x hx => ?_
    rw [← ENNReal.ofReal_mul hk0] at hx
    have hlt' : k * p θ' x < p θ x := by
      by_contra hcon; push_neg at hcon
      exact absurd hx (not_lt.mpr (ENNReal.ofReal_le_ofReal hcon))
    have hTC : T x < C := by
      by_contra hcon
      exact absurd (hge x (not_lt.mp hcon)) (not_le.mpr hlt')
    show 1 - oneSidedTest T C γ x = 1
    unfold oneSidedTest
    rw [if_neg (not_lt.mpr hTC.le), if_neg (ne_of_lt hTC)]; ring
  · refine Filter.Eventually.of_forall fun x hx => ?_
    rw [← ENNReal.ofReal_mul hk0] at hx
    have hlt' : p θ x < k * p θ' x := by
      by_contra hcon; push_neg at hcon
      exact absurd hx (not_lt.mpr (ENNReal.ofReal_le_ofReal hcon))
    have hTC : C < T x := by
      by_contra hcon
      exact absurd (hle x (not_lt.mp hcon)) (not_le.mpr hlt')
    show 1 - oneSidedTest T C γ x = 0
    unfold oneSidedTest; rw [if_pos hTC]; ring

/-- If the co-test `1 − φ` has positive power at `θ`, some point at or below the threshold
has positive `θ`-density. -/
private lemma exists_pos_density_below_of_coPower_pos {μ : Measure 𝓧} {P : ℝ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {p : ℝ → 𝓧 → ℝ} (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    {T : 𝓧 → ℝ} (hT : Measurable T) {C γ : ℝ} {θ : ℝ}
    (hpow : power P (oneSidedTest T C γ) θ < 1) : ∃ z, T z ≤ C ∧ 0 < p θ z := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hmeas, hnn, hPeq⟩ := hp θ
  have hnull : (P θ) {x | T x ≤ C} = 0 := by
    rw [hPeq, withDensity_apply _ (measurableSet_le hT measurable_const)]
    refine setLIntegral_eq_zero (measurableSet_le hT measurable_const) fun x hx => ?_
    simp only [Set.mem_setOf_eq] at hx
    simp [le_antisymm (hcon x hx) (hnn x)]
  -- Off `{T ≤ C}`, i.e. on `{C < T}`, the one-sided test is `1`, so its power is `1`.
  have hone : power P (oneSidedTest T C γ) θ = 1 := by
    rw [power_oneSidedTest_eq hT C γ θ]
    have hRfull : (P θ) {x | C < T x} = 1 := by
      have hcompl : {x | C < T x} = {x | T x ≤ C}ᶜ := by
        ext x; simp [not_le]
      rw [hcompl, prob_compl_eq_one_sub (measurableSet_le hT measurable_const), hnull, tsub_zero]
    have hBle : (P θ) {x | T x = C} = 0 :=
      measure_mono_null (Set.setOf_subset_setOf.2 fun x hx => le_of_eq hx) hnull
    rw [hRfull, hBle]; simp
  rw [hone] at hpow; exact absurd hpow (lt_irrefl 1)

/-- **Minimum rejection probability below the boundary.** Among all tests whose size at
`θ₀` is exactly `α`, the one-sided test minimizes the probability of rejection — the
probability of an error of the first kind — at every `θ < θ₀`.

**Documented deviation from the printed form (forced).** The nondegeneracy hypothesis
`α < 1` is added. Without it the statement is **FALSE**.

*Counterexample.* `𝓧 = ℝ`, `μ = volume`, `T = id`, and the shifted-exponential family
`p θ x = exp(-(x - θ))·1_{x ≥ θ}`, which has monotone likelihood ratio in `T` (the
exponential factors cancel in the cross-product, and `1_{x ≥ θ'}·1_{y ≥ θ} ≤
1_{x ≥ θ}·1_{y ≥ θ'}` whenever `θ < θ'` and `x ≤ y`). Take `C = θ₀ - 1` and `γ = 0`. Then
`p θ₀` vanishes on `{T ≤ C}`, so `α = power P φ θ₀ = 1`. The competitor
`ψ = 1_{x ≥ θ₀}` is a critical function with `power P ψ θ₀ = 1 = α`, yet for every
`θ < θ₀ - 1`, `power P ψ θ = e^{θ-θ₀} < e^{θ-θ₀+1} = power P φ θ`: the one-sided test does
*not* minimize the rejection probability. The mechanism is exactly `α = 1`, and `α < 1` is
the minimal repair: it forces some point at or below `C` to carry positive `θ₀`-density
(`exists_pos_density_below_of_coPower_pos`), which is all the proof needs. The classical
statement obtains the same effect from strictly positive densities. -/
theorem power_min_oneSided
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic and the monotone-likelihood-ratio property
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T)
    -- USER-INPUT: the null boundary, level, and the constants of the test
    (θ₀ : ℝ) {α C γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: nondegenerate level. This is the documented amendment: at `α = 1` the
    -- conclusion is false (counterexample in the docstring)
    (hα₁ : α < 1)
    -- USER-INPUT: the test is the one determined by the exact-size requirement
    (hsize : power P (oneSidedTest T C γ) θ₀ = α) :
    ∀ θ < θ₀, ∀ ψ, IsCriticalFn ψ → power P ψ θ₀ = α →
      power P (oneSidedTest T C γ) θ ≤ power P ψ θ := by
  intro θ hθ ψ hψ hψsize
  -- `α < 1` rules out the degenerate configuration in which `p θ₀` vanishes on `{T ≤ C}`.
  have hz : ∃ z, T z ≤ C ∧ 0 < p θ₀ z :=
    exists_pos_density_below_of_coPower_pos hp hT (by rw [hsize]; exact hα₁)
  set φ := oneSidedTest T C γ with hφdef
  have hφc : IsCriticalFn φ := isCriticalFn_oneSidedTest hT hγ
  have hφint : ∀ θ, Integrable φ (P θ) := fun θ =>
    (integrable_const (1 : ℝ)).mono' hφc.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hφc.2 x).1]; exact (hφc.2 x).2)
  have hψint : ∀ θ, Integrable ψ (P θ) := fun θ =>
    (integrable_const (1 : ℝ)).mono' hψ.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hψ.2 x).1]; exact (hψ.2 x).2)
  -- The co-test `1 − φ` is most powerful for `P θ₀` (null) against `P θ` (alt).
  set coφ : 𝓧 → ℝ := fun x => 1 - φ x with hcoφdef
  have hcoφc : IsCriticalFn coφ :=
    ⟨measurable_const.sub hφc.1, fun x => ⟨by linarith [(hφc.2 x).2], by linarith [(hφc.2 x).1]⟩⟩
  have hcoφsize : powerAgainst (P θ₀) coφ = 1 - α := by
    rw [hcoφdef, powerAgainst_one_sub (hφint θ₀)]
    exact congrArg (1 - ·) hsize
  obtain ⟨K, hshape⟩ := hasNPShape_coOneSided hp hMLR hθ γ hz
  have hMP := isMostPowerful_of_npShape μ (P θ₀) (P θ) (hp θ₀) (hp θ) hcoφc hcoφsize hshape
  set coψ : 𝓧 → ℝ := fun x => 1 - ψ x with hcoψdef
  have hcoψc : IsCriticalFn coψ :=
    ⟨measurable_const.sub hψ.1, fun x => ⟨by linarith [(hψ.2 x).2], by linarith [(hψ.2 x).1]⟩⟩
  have hcoψsize : powerAgainst (P θ₀) coψ ≤ 1 - α := by
    rw [hcoψdef, powerAgainst_one_sub (hψint θ₀)]; exact le_of_eq (congrArg (1 - ·) hψsize)
  have hcmp := hMP.2.2 coψ hcoψc hcoψsize
  rw [hcoψdef, powerAgainst_one_sub (hψint θ), hcoφdef, powerAgainst_one_sub (hφint θ)] at hcmp
  change powerAgainst (P θ) φ ≤ powerAgainst (P θ) ψ
  linarith [hcmp]

/-- **The one-sided tests form an essentially complete class.** For the two-decision
problem whose losses satisfy `L₁ - L₀ > 0` below the boundary and `< 0` above it, every
test is matched or beaten, uniformly in `θ`, by a one-sided test.

**Documented deviation from the printed form (forced).** The competitor `ψ` is required to
have a nondegenerate size at the boundary, `power P ψ θ₀ ∈ Set.Ioo 0 1`. Without that
restriction the statement is **FALSE**, for the same reason that `isUMP_oneSided` must
exclude `α ∈ {0,1}`: a one-sided test with a *real* critical value cannot match the size of
a degenerate competitor when `T` is unbounded in the relevant tail, and the printed
docstring's own caveat that "`C` here is a real number, not an extended one" is exactly the
gap.

*Counterexample.* `𝓧 = ℝ`, `μ = volume`, `T = id`, `P θ = 𝒩(θ,1)` (an MLR family),
`θ₀ = 0`, `L₀ = 0`, `L₁ θ = -θ` — so `L₁ - L₀ > 0` strictly below `0` and `< 0` strictly
above, as the hypotheses demand. Take `ψ ≡ 1`, a critical function, with
`power P ψ θ = 1` for every `θ`, hence `testRisk P L₀ L₁ ψ θ = -θ`. Every one-sided test
with a real `C` has `power P (oneSidedTest T C γ) θ = 1 - Φ(C - θ) < 1`, so for each
`θ > 0`, `testRisk P L₀ L₁ (oneSidedTest T C γ) θ = (1 - Φ(C-θ))·(-θ) > -θ =
testRisk P L₀ L₁ ψ θ`. No one-sided test dominates `ψ`. Here `power P ψ θ₀ = 1`, which the
amended hypothesis excludes. -/
theorem essentiallyComplete_oneSidedTest
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic and the monotone-likelihood-ratio property
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T)
    -- USER-INPUT: the null boundary and the two loss functions
    (θ₀ : ℝ) (L₀ L₁ : ℝ → ℝ)
    -- USER-INPUT: rejecting costs more than accepting strictly below the boundary …
    (hloss_lt : ∀ θ < θ₀, 0 < L₁ θ - L₀ θ)
    -- USER-INPUT: … and less strictly above it (the monotone-loss condition)
    (hloss_gt : ∀ θ, θ₀ < θ → L₁ θ - L₀ θ < 0) :
    -- The size restriction on `ψ` is the documented amendment; see the docstring
    ∀ ψ, IsCriticalFn ψ → power P ψ θ₀ ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ C γ : ℝ, γ ∈ Set.Icc (0 : ℝ) 1 ∧
        ∀ θ, testRisk P L₀ L₁ (oneSidedTest T C γ) θ ≤ testRisk P L₀ L₁ ψ θ := by
  intro ψ hψ hψsize
  obtain ⟨hα0, hα1⟩ := hψsize
  -- Match the size of `ψ` at the boundary with an honest one-sided test.
  haveI : IsProbabilityMeasure ((P θ₀).map T) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  obtain ⟨C, γ, hγ0, hγ1, hcrit⟩ :=
    exists_critical_constants ((P θ₀).map T) hα0 hα1
  have hγ' : γ ∈ Set.Icc (0 : ℝ) 1 := ⟨hγ0, hγ1⟩
  set φ := oneSidedTest T C γ with hφdef
  have hmR : MeasurableSet {x : ℝ | C < x} := measurableSet_Ioi
  have hmB : MeasurableSet {x : ℝ | x = C} := by
    rw [show {x : ℝ | x = C} = {C} from by ext x; simp [eq_comm]]
    exact measurableSet_singleton C
  have hReq : (P θ₀) {x | C < T x} = ((P θ₀).map T) {x : ℝ | C < x} := by
    rw [Measure.map_apply hT hmR]; rfl
  have hBeq : (P θ₀) {x | T x = C} = ((P θ₀).map T) {x : ℝ | x = C} := by
    rw [Measure.map_apply hT hmB]; rfl
  have hsize : power P φ θ₀ = power P ψ θ₀ := by
    rw [hφdef, power_oneSidedTest_eq hT C γ θ₀, hReq, hBeq]; exact hcrit
  have hφc : IsCriticalFn φ := isCriticalFn_oneSidedTest hT hγ'
  -- The risk is affine in the power, with slope `L₁ θ − L₀ θ`.
  have hrisk : ∀ (χ : 𝓧 → ℝ) (θ : ℝ),
      testRisk P L₀ L₁ χ θ = power P χ θ * (L₁ θ - L₀ θ) + L₀ θ := by
    intro χ θ; unfold testRisk; ring
  refine ⟨C, γ, hγ', fun θ => ?_⟩
  rw [hrisk φ θ, hrisk ψ θ]
  rcases lt_trichotomy θ θ₀ with hθ | hθ | hθ
  · -- Below the boundary: the one-sided test minimizes the rejection probability.
    have hpow := power_min_oneSided μ P p hp T hT hMLR θ₀ hγ' hα1 hsize θ hθ ψ hψ rfl
    nlinarith [hloss_lt θ hθ, hpow]
  · subst hθ; rw [hsize]
  · -- Above the boundary: the one-sided test is most powerful, and the slope is negative.
    have hz : ∃ z, C ≤ T z ∧ 0 < p θ₀ z :=
      exists_pos_density_of_power_pos hp hT (by rw [hsize]; exact hα0)
    have hMP := isMostPowerful_oneSided hp hT hMLR hθ hγ' hz
    have hpow : power P ψ θ ≤ power P φ θ := hMP.2.2 ψ hψ hsize.ge
    nlinarith [hloss_gt θ hθ, hpow]

/-- **The one-parameter exponential family has a monotone likelihood ratio** in its
natural statistic, provided the parametrization `θ ↦ η(θ)` is strictly increasing. The
densities are the canonical ones, `exp(η(θ)·T(x) - A(η(θ)))`. -/
theorem hasMLR_expFamily
    -- USER-INPUT: the exponential family (reference measure and natural statistic)
    (E : ExpFamily 𝓧 ℝ)
    -- USER-INPUT: the parametrization, strictly increasing — the printed hypothesis
    -- "`Q` is strictly monotone", in its increasing case
    {ηmap : ℝ → ℝ} (hη : StrictMono ηmap) :
    HasMLR (fun θ x => Real.exp (ηmap θ * E.stat x - E.logPartition (ηmap θ))) E.stat := by
  intro θ θ' hθθ' x y hTxy
  have hηlt : ηmap θ < ηmap θ' := hη hθθ'
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_nonneg (sub_pos.mpr hηlt).le (sub_nonneg.mpr hTxy)]

/-- **UMP one-sided test in a one-parameter exponential family.** For a family presented
in canonical form through a strictly increasing `η`, the test rejecting for large values of
the natural statistic is UMP for `H : θ ≤ θ₀` against `K : θ > θ₀`. -/
theorem isUMP_oneSided_expFamily
    -- USER-INPUT: the exponential family, with σ-finite reference measure
    (E : ExpFamily 𝓧 ℝ) [SigmaFinite E.base]
    -- USER-INPUT: the model, a family of probability measures
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: the parametrization, strictly increasing
    {ηmap : ℝ → ℝ} (hη : StrictMono ηmap)
    -- USER-INPUT: the model is the canonical family read through `ηmap`
    (hrepr : IsCanonicalRepr P E ηmap)
    -- USER-INPUT: every parameter value is in the natural parameter set, so that each
    -- `P θ` really is the tilted probability measure and not the junk zero measure
    (hnat : ∀ θ, ηmap θ ∈ E.natSet)
    -- USER-INPUT: the null boundary and the nominal level. The endpoints are genuinely
    -- excluded: the exact-size clause `power = α` is unattainable by a one-sided test at
    -- `α ∈ {0,1}` whenever `T` is essentially unbounded in the relevant tail (e.g.
    -- `𝓧 = ℝ`, `T = id`, `P θ = 𝒩(θ,1)`, where `1 − Φ(C) > 0` for every real `C`), so the
    -- former `Set.Icc` reading was FALSE at the two endpoints. This also matches
    -- `exists_critical_constants`, which requires `0 < α < 1`.
    (θ₀ : ℝ) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C γ : ℝ, γ ∈ Set.Icc (0 : ℝ) 1 ∧
      power P (oneSidedTest E.stat C γ) θ₀ = α ∧
      IsUMP P (Set.Iic θ₀) (Set.Ioi θ₀) α (oneSidedTest E.stat C γ) := by
  -- Read off the canonical densities and reduce to the general MLR theorem.
  set p : ℝ → 𝓧 → ℝ :=
    fun θ x => Real.exp (ηmap θ * E.stat x - E.logPartition (ηmap θ)) with hpdef
  have hp : ∀ θ, HasDensity E.base (p θ) (P θ) := by
    intro θ
    refine ⟨(((E.stat_meas.const_mul (ηmap θ)).sub_const _).exp), fun x => (Real.exp_pos _).le, ?_⟩
    rw [hrepr θ, E.P_eq_withDensity (hnat θ)]
    refine withDensity_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hpdef, real_inner_mul]
  exact isUMP_oneSided E.base P p hp E.stat E.stat_meas (hasMLR_expFamily E hη) θ₀ hα

end StatLean.HypothesisTesting
