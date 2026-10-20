module
public import StatLean.HypothesisTesting.MLR.OneSided
public import StatLean.HypothesisTesting.Tests.Confidence

@[expose] public section

/-!
# Uniformly most accurate one-sided confidence bounds under a monotone likelihood ratio

Inverting the uniformly most powerful one-sided tests of `H(θ₀) : θ ≤ θ₀` turns their
optimality into optimality of a confidence bound: the resulting lower bound `θ̲` covers
every false value `θ₀ < θ` with the smallest possible probability, uniformly. When the
distribution function of the statistic is continuous in each variable separately, the bound
is the solution of
$$ F_\theta\bigl(T(x)\bigr) \;=\; 1 - \alpha , $$
and that solution, when it exists, is unique.

Contents:
* `exists_uma_lowerBound` — existence of a uniformly most accurate lower confidence bound
  at every confidence level `1 - α`, together with its characterization as the root of the
  displayed equation.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.5 (Confidence Bounds), Corollary 3.5.1 (uniformly most accurate one-sided
confidence bounds under a monotone likelihood ratio). (`TSH4 §3.5 Cor 3.5.1`.)

**Proof formalization notes.**
* The optimality predicates `IsConfidenceFamily` and `IsUMAConfidence` come from the
  test/confidence-set duality development; this file consumes them and adds nothing to the
  data model. A lower bound `θ̲` is presented as the confidence family `x ↦ [θ̲(x), ∞)`,
  and the false-value set attached to `θ₀` is `(θ₀, ∞)`: the statement "`θ̲(X) ≤ θ₀`" is
  wrong exactly when the true parameter exceeds `θ₀`.
* The single application below reads `IsUMAConfidence P K S (1 - α)`, with `K θ₀` the set
  of parameter values against which the coverage statement `θ₀ ∈ S(x)` is false. Note the
  last argument of that predicate is the *confidence* level, so the significance level `α`
  used everywhere else in this file enters as `1 - α`.
* The distribution function of the statistic is written `(P θ {y | T y ≤ t}).toReal`, and
  the printed hypothesis — continuity in each of `t` and `θ` when the other is held fixed —
  is transcribed as two separate continuity assumptions. Joint continuity is *not*
  assumed, and is not needed. In fact only continuity in `t` is consumed: `hcont_θ` is kept
  because it is a printed hypothesis, but the proof below never uses it (see `hsolvable`).
* The parameter set is the whole real line rather than a general `Ω ⊆ ℝ`; the printed
  statement quantifies over `θ ∈ Ω`, and restricting to a subset would require carrying
  `Ω` through the confidence-set predicates as well.
* **Repair of the printed statement (`hsolvable`).** As printed the theorem is FALSE; the
  counterexample and the minimal repair are recorded on `exists_uma_lowerBound` itself.
* The optimality transfer needs the *most powerful* property of the inverted one-sided test
  against the single null value `θ₀` — a competitor confidence family only controls its
  coverage at `θ₀`. The public one-sided theorems of `MLR/OneSided` state optimality against
  the larger null `(-∞, θ₀]`, whose competitor class is smaller, so the separating-multiplier
  step is redone here (`cb_exists_sep_const`, `cb_hasNPShape`, `cb_isMostPowerful`) in the
  same way as there; the file already carries local copies of several `MLR/OneSided`
  privates for the same reason.

**Bibliographic comments.** Confidence sets, their coverage requirement, and the accuracy
criterion are due to J. Neyman ("Outline of a theory of statistical estimation based on the
classical theory of probability," *Phil. Trans. R. Soc. Lond. A* **236** (1937), 333–380);
optimal one-sided bounds for families with monotone likelihood ratio follow from the
optimality theory of S. Karlin and H. Rubin ("The theory of decision procedures for
distributions with monotone likelihood ratio," *Ann. Math. Statist.* **27** (1956),
272–299).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-! ### The distribution function of the statistic -/

/-- The distribution function `θ ↦ (P θ {y | T y ≤ t}).toReal` is antitone under a
monotone likelihood ratio (stochastic monotonicity). It needs only `HasMLR`, no
non-degeneracy. -/
private lemma cdf_antitone
    (μ : Measure 𝓧) [SigmaFinite μ] (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T) (t : ℝ) :
    Antitone fun θ : ℝ => (P θ {y | T y ≤ t}).toReal := by
  -- `ψ = -1_{T ≤ t}` is nondecreasing along `T`; apply `integral_mono_of_hasMLR`.
  have hset : MeasurableSet {y : 𝓧 | T y ≤ t} := measurableSet_le hT measurable_const
  set ψ : 𝓧 → ℝ := fun x => -({y : 𝓧 | T y ≤ t}.indicator (1 : 𝓧 → ℝ) x) with hψdef
  have hψmeas : Measurable ψ := (measurable_const.indicator hset).neg
  have hmono : ∀ x y, T x ≤ T y → ψ x ≤ ψ y := by
    intro x y hxy
    simp only [hψdef, neg_le_neg_iff]
    by_cases hy : y ∈ {y : 𝓧 | T y ≤ t}
    · have hx : x ∈ {y : 𝓧 | T y ≤ t} := le_trans hxy hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; simp
    · rw [Set.indicator_of_notMem hy]
      by_cases hx : x ∈ {y : 𝓧 | T y ≤ t}
      · rw [Set.indicator_of_mem hx]; exact zero_le_one
      · rw [Set.indicator_of_notMem hx]
  have hint : ∀ θ : ℝ, Integrable ψ (P θ) :=
    fun θ => ((integrable_const (1 : ℝ)).indicator hset).neg
  have hM := integral_mono_of_hasMLR μ P p hp T hT hMLR ψ hψmeas hmono hint
  have hval : ∀ θ : ℝ, (∫ x, ψ x ∂(P θ)) = -(P θ {y | T y ≤ t}).toReal := by
    intro θ
    rw [show (fun x => ψ x) = fun x => -({y : 𝓧 | T y ≤ t}.indicator (1 : 𝓧 → ℝ) x) from rfl,
      integral_neg, integral_indicator_one hset]
    simp only [measureReal_def]
  intro θ θ' hθθ'
  have hle := hM hθθ'
  simp only [hval θ, hval θ'] at hle
  linarith

/-- The distribution function is nondecreasing in the argument. -/
private lemma cdf_monotone (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (T : 𝓧 → ℝ) (θ : ℝ) : Monotone fun t : ℝ => (P θ {y | T y ≤ t}).toReal := by
  intro s t hst
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun y hy => le_trans hy hst)

/-- **The threshold at a prescribed distribution-function value.** For a continuous
distribution function and a value `β ∈ (0,1)` the sublevel set `{t | F t ≤ β}` is exactly a
closed lower ray `(-∞, C]`, and `F C = β`. -/
private lemma cb_exists_threshold {P : ℝ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {T : 𝓧 → ℝ} (hT : Measurable T) (θ : ℝ)
    (hcont : Continuous fun t : ℝ => (P θ {y | T y ≤ t}).toReal)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, (P θ {y | T y ≤ C}).toReal = β ∧
      ∀ t : ℝ, ((P θ {y | T y ≤ t}).toReal ≤ β ↔ t ≤ C) := by
  set F : ℝ → ℝ := fun t => (P θ {y | T y ≤ t}).toReal with hFdef
  have hmeasT : ∀ t : ℝ, MeasurableSet {y : 𝓧 | T y ≤ t} := fun t =>
    measurableSet_le hT measurable_const
  have hFmono : Monotone F := cdf_monotone P T θ
  -- Upward: the sets exhaust `𝓧`, so `F` exceeds `β` somewhere.
  have hunion : (⋃ n : ℕ, {y : 𝓧 | T y ≤ (n : ℝ)}) = Set.univ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge (T y)
    exact ⟨n, hn⟩
  have hmonoU : Monotone fun n : ℕ => {y : 𝓧 | T y ≤ (n : ℝ)} := by
    intro m n hmn y hy
    have hy' : T y ≤ (m : ℝ) := hy
    exact le_trans hy' (Nat.cast_le.mpr hmn)
  have hFsup : ∃ b : ℝ, β < F b := by
    by_contra hcon
    push_neg at hcon
    have hle : ∀ n : ℕ, P θ {y : 𝓧 | T y ≤ (n : ℝ)} ≤ ENNReal.ofReal β := by
      intro n
      calc P θ {y : 𝓧 | T y ≤ (n : ℝ)}
          = ENNReal.ofReal (F ((n : ℝ))) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
        _ ≤ ENNReal.ofReal β := ENNReal.ofReal_le_ofReal (hcon _)
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal β := by
      have huniv : P θ Set.univ = 1 := measure_univ
      rw [← huniv, ← hunion, hmonoU.measure_iUnion]
      exact iSup_le hle
    rw [ENNReal.one_le_ofReal] at h1
    linarith
  -- Downward: the sets shrink to `∅`, so `F` falls below `β` somewhere.
  have hinter : (⋂ n : ℕ, {y : 𝓧 | T y ≤ -(n : ℝ)}) = (∅ : Set 𝓧) := by
    ext y
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    obtain ⟨n, hn⟩ := exists_nat_gt (-(T y))
    exact absurd (h n) (by push_neg; linarith)
  have hantiI : Antitone fun n : ℕ => {y : 𝓧 | T y ≤ -(n : ℝ)} := by
    intro m n hmn y hy
    have hy' : T y ≤ -(n : ℝ) := hy
    exact le_trans hy' (neg_le_neg (Nat.cast_le.mpr hmn))
  have hFinf : ∃ a : ℝ, F a ≤ β := by
    by_contra hcon
    push_neg at hcon
    have hge : ∀ n : ℕ, ENNReal.ofReal β ≤ P θ {y : 𝓧 | T y ≤ -(n : ℝ)} := by
      intro n
      calc ENNReal.ofReal β ≤ ENNReal.ofReal (F (-(n : ℝ))) :=
            ENNReal.ofReal_le_ofReal (hcon _).le
        _ = P θ {y : 𝓧 | T y ≤ -(n : ℝ)} := ENNReal.ofReal_toReal (measure_ne_top _ _)
    have h0 : ENNReal.ofReal β ≤ (0 : ℝ≥0∞) := by
      have hI := hantiI.measure_iInter (μ := P θ)
        (fun n : ℕ => (hmeasT (-(n : ℝ))).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
      rw [hinter, measure_empty] at hI
      rw [hI]
      exact le_iInf hge
    rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h0
    linarith
  obtain ⟨b, hb⟩ := hFsup
  obtain ⟨a, ha⟩ := hFinf
  set S : Set ℝ := {t : ℝ | F t ≤ β} with hSdef
  have hSne : S.Nonempty := ⟨a, ha⟩
  have hSbdd : BddAbove S := by
    refine ⟨b, fun t ht => ?_⟩
    by_contra hcon
    push_neg at hcon
    exact absurd (le_trans (hFmono hcon.le) ht) (not_le.mpr hb)
  have hSclosed : IsClosed S := isClosed_le hcont continuous_const
  set C := sSup S with hCdef
  have hCmem : C ∈ S := hSclosed.csSup_mem hSne hSbdd
  have hCle : F C ≤ β := hCmem
  have hCeq : F C = β := by
    rcases eq_or_lt_of_le hCle with h | h
    · exact h
    · exfalso
      have hmem : F ⁻¹' Set.Iio β ∈ nhds C :=
        hcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds h)
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
      have hin : C + ε / 2 ∈ Metric.ball C ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        rw [show C + ε / 2 - C = ε / 2 by ring, abs_of_pos (by linarith)]
        linarith
      have : F (C + ε / 2) ≤ β := (hball hin).le
      have := le_csSup hSbdd (show C + ε / 2 ∈ S from this)
      linarith
  refine ⟨C, hCeq, fun t => ⟨fun ht => le_csSup hSbdd ht, fun ht => ?_⟩⟩
  exact le_trans (hFmono ht) hCle

/-! ### The one-sided test at a threshold, as an acceptance region -/

omit [MeasurableSpace 𝓧] in
/-- The non-randomized one-sided test is the indicator of the rejection region. -/
private lemma cb_oneSidedTest_zero {T : 𝓧 → ℝ} (C : ℝ) :
    oneSidedTest T C 0 = Set.indicator {x : 𝓧 | C < T x} (1 : 𝓧 → ℝ) := by
  funext x
  simp only [oneSidedTest, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  by_cases h : C < T x
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    split_ifs <;> rfl

/-- The acceptance test of the lower ray `{T ≤ C}` *is* the non-randomized one-sided test. -/
private lemma cb_acceptanceTest_eq {T : 𝓧 → ℝ} (C : ℝ) :
    acceptanceTest {x : 𝓧 | T x ≤ C} = oneSidedTest T C 0 := by
  rw [cb_oneSidedTest_zero]
  unfold acceptanceTest
  congr 1
  ext x
  simp [not_le]

/-- The power of the non-randomized one-sided test is the upper tail. -/
private lemma cb_power_oneSided {P : ℝ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {T : 𝓧 → ℝ} (hT : Measurable T) (C θ : ℝ) :
    power P (oneSidedTest T C 0) θ = 1 - (P θ {y : 𝓧 | T y ≤ C}).toReal := by
  have hR : {x : 𝓧 | C < T x} = {y : 𝓧 | T y ≤ C}ᶜ := by ext x; simp [not_le]
  have hmeas : MeasurableSet {y : 𝓧 | T y ≤ C} := measurableSet_le hT measurable_const
  unfold power
  rw [cb_oneSidedTest_zero, integral_indicator_one (measurableSet_lt measurable_const hT),
    measureReal_def, hR, prob_compl_eq_one_sub hmeas,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

/-! ### Most powerful, against a single null value

The public one-sided theorems of `MLR/OneSided` compare against competitors that are level
`α` on the whole null ray `(-∞, θ₀]`. Inverting a competitor confidence family only produces
a test of level `α` at the single value `θ₀`, so the Karlin–Rubin separation is redone here
for that (larger) competitor class. -/

/-- **Existence of the separating multiplier** (local copy of the `MLR/OneSided` private
lemma). Given the monotone likelihood ratio, a threshold `C`, and one point of positive
`θ`-density with `T ≥ C`, there is a real `k ≥ 0` with `p_{θ'} ≤ k·p_θ` where `T ≤ C` and
`k·p_θ ≤ p_{θ'}` where `T ≥ C`. -/
private lemma cb_exists_sep_const {μ : Measure 𝓧} {P : ℝ → Measure 𝓧} {p : ℝ → 𝓧 → ℝ}
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
    · have hkey := hMLR hlt x z₀ (le_trans hxC hz₀C)
      rw [← hpx, zero_mul] at hkey
      have hle0 : p θ' x * p θ z₀ ≤ 0 := hkey
      have hpx'0 : p θ' x = 0 :=
        le_antisymm (nonpos_of_mul_nonpos_left hle0 hz₀pos) (hnn' x)
      rw [hpx'0, ← hpx, mul_zero]
    · have hmem : p θ' x / p θ x ∈ insert (0 : ℝ) S :=
        Set.mem_insert_iff.mpr (Or.inr ⟨x, hxC, hpx, rfl⟩)
      have hle : p θ' x / p θ x ≤ k := le_csSup hbdd hmem
      rw [div_le_iff₀ hpx] at hle
      linarith [hle]
  · intro x hxC
    rcases eq_or_lt_of_le (hnn x) with hpx | hpx
    · rw [← hpx, mul_zero]; exact hnn' x
    · have hUBx : ∀ r ∈ insert (0 : ℝ) S, r ≤ p θ' x / p θ x := by
        intro r hr
        rcases hr with hr0 | ⟨y, hyC, hypos, hyeq⟩
        · exact hr0 ▸ div_nonneg (hnn' x) hpx.le
        · rw [hyeq, div_le_div_iff₀ hypos hpx]
          have := hMLR hlt y x (le_trans hyC hxC)
          nlinarith [this]
      have hle : k ≤ p θ' x / p θ x := csSup_le hne hUBx
      rw [le_div_iff₀ hpx] at hle
      linarith [hle]

/-- The non-randomized one-sided test has Neyman–Pearson shape (local copy). -/
private lemma cb_hasNPShape {μ : Measure 𝓧} {P : ℝ → Measure 𝓧} {p : ℝ → 𝓧 → ℝ}
    (hp : ∀ θ, HasDensity μ (p θ) (P θ)) {T : 𝓧 → ℝ} (hMLR : HasMLR p T)
    {θ θ' : ℝ} (hlt : θ < θ') {C : ℝ} (hz : ∃ z, C ≤ T z ∧ 0 < p θ z) :
    ∃ K : ℝ≥0∞, HasNPShape μ (p θ) (p θ') K (oneSidedTest T C 0) := by
  obtain ⟨k, hk0, hle, hge⟩ := cb_exists_sep_const hp hMLR hlt hz
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
    change oneSidedTest T C 0 x = 1
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
    change oneSidedTest T C 0 x = 0
    unfold oneSidedTest; rw [if_neg (not_lt.mpr hTC.le), if_neg (ne_of_lt hTC)]

/-- The non-randomized one-sided test is a critical function. -/
private lemma cb_isCriticalFn {T : 𝓧 → ℝ} (hT : Measurable T) (C : ℝ) :
    IsCriticalFn (oneSidedTest T C 0) := by
  rw [← cb_acceptanceTest_eq]
  exact isCriticalFn_acceptanceTest (measurableSet_le hT measurable_const)

/-- **Most powerful against a single alternative** (local copy). -/
private lemma cb_isMostPowerful {μ : Measure 𝓧} [SigmaFinite μ] {P : ℝ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {p : ℝ → 𝓧 → ℝ} (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    {T : 𝓧 → ℝ} (hT : Measurable T) (hMLR : HasMLR p T) {θ θ' : ℝ} (hlt : θ < θ')
    {C : ℝ} (hz : ∃ z, C ≤ T z ∧ 0 < p θ z) :
    IsMostPowerful (P θ) (P θ') (power P (oneSidedTest T C 0) θ) (oneSidedTest T C 0) := by
  obtain ⟨K, hshape⟩ := cb_hasNPShape hp hMLR hlt hz
  exact isMostPowerful_of_npShape μ (P θ) (P θ') (hp θ) (hp θ')
    (cb_isCriticalFn hT C) rfl hshape

/-- Positive upper-tail mass produces a point of positive density above the threshold. -/
private lemma cb_exists_pos_density {μ : Measure 𝓧} {P : ℝ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {p : ℝ → 𝓧 → ℝ} (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    {T : 𝓧 → ℝ} (hT : Measurable T) {C θ : ℝ}
    (hpow : 0 < power P (oneSidedTest T C 0) θ) : ∃ z, C ≤ T z ∧ 0 < p θ z := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hmeas, hnn, hPeq⟩ := hp θ
  have hnull : (P θ) {x | C ≤ T x} = 0 := by
    rw [hPeq, withDensity_apply _ (measurableSet_le measurable_const hT)]
    refine setLIntegral_eq_zero (measurableSet_le measurable_const hT) fun x hx => ?_
    simp only [Set.mem_setOf_eq] at hx
    have hle : p θ x ≤ 0 := hcon x hx
    simp [le_antisymm hle (hnn x)]
  have hRle : (P θ) {x | C < T x} = 0 :=
    measure_mono_null (Set.setOf_subset_setOf.2 fun x hx => le_of_lt hx) hnull
  rw [power] at hpow
  rw [cb_oneSidedTest_zero,
    integral_indicator_one (measurableSet_lt measurable_const hT), measureReal_def, hRle] at hpow
  simp at hpow

/-! ### The uniformly most accurate lower bound -/

/-- **Uniformly most accurate lower confidence bounds.** For a family with monotone
likelihood ratio in `T` whose statistic has a distribution function continuous in each
variable separately, there is, at every confidence level `1 - α`, a lower confidence bound
that is uniformly most accurate; and wherever the equation `F_θ(T(x)) = 1 - α` is solvable
its solution is unique and equals the bound.

The confidence family is `x ↦ [θ̲(x), ∞)` and the false values attached to `θ₀` are
`(θ₀, ∞)`.

**Repaired statement.** As printed — i.e. without `hsolvable` — the theorem is FALSE, and
the repair below is the minimal one.

*Counterexample to the printed form.* `𝓧 = ℝ`, `μ = volume`, `T = id`,
`P θ = 𝒩(arctan θ, 1)`, i.e. `p θ x = ϕ(x − arctan θ)`. This is a one-parameter exponential
family in `T = id` read through the strictly increasing `η = arctan`, so `hMLR` holds
(`hasMLR_expFamily`); `F_θ(t) = Φ(t − arctan θ)` is continuous in each variable, giving
`hcont_t`/`hcont_θ`; and `arctan` is injective, giving `hdist`. Fix `α ∈ (0,1)` and put
`z = Φ⁻¹(1 − α)`. The inverted UMP family is `S(x) = {θ : x ≤ arctan θ + z}`, with exact
coverage `P θ {x : x ≤ arctan θ + z} = Φ(z) = 1 − α` and measurable slices
`Iic (arctan θ₀ + z)`, so `S` is a legitimate competitor in the optimality clause. Since
`arctan` has range `(−π/2, π/2)`, `S(x) = ∅` for `x ≥ z + π/2` — a set of positive
`P θ`-probability for every `θ` — which no `Ici (θ̲(x))` can match. Concretely, if
`θ̲ : 𝓧 → ℝ` were measurable and satisfied the conclusion, testing optimality against `S`
at `θ₀ = j`, `θ = j + 1` gives
`P_{j+1} {x : θ̲ x ≤ j} ≤ Φ(arctan j + z − arctan (j+1)) → Φ(z) = 1 − α`, so
`P_{j+1}(B_j) ≥ α − o(1)` for `B_j = {x : θ̲ x > j}`; but `θ̲` is real-valued, so `B_j ↓ ∅`
and `N(B_j) → 0` for `N = 𝒩(π/2, 1)`, while `dTV(P_{j+1}, N) → 0` because
`arctan (j+1) → π/2`, whence `P_{j+1}(B_j) → 0` — contradicting `α > 0`.

*Repair.* Assume the defining equation is solvable, `hsolvable`. This is exactly the
equation displayed in the theorem's own conclusion, so it adds no new notion; it is what
rules out the vacuous (`S(x) = ∅`) and total (`S(x) = ℝ`) confidence sets that a
real-valued lower bound cannot express, and it holds automatically for genuine location
families such as `P θ = 𝒩(θ,1)`. It is not implied by the printed hypotheses: in the
counterexample `F_θ(t) = Φ(t − arctan θ)` never reaches `1 − α` once `t ≥ z + π/2`. -/
theorem exists_uma_lowerBound
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model, a family of probability measures on a real parameter
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: its densities with respect to `μ`
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic in which the likelihood ratio is monotone
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T)
    -- USER-INPUT: the distribution function of `T` is continuous in `t` for each fixed `θ`
    (hcont_t : ∀ θ : ℝ, Continuous fun t : ℝ => (P θ {y | T y ≤ t}).toReal)
    -- USER-INPUT: … and continuous in `θ` for each fixed `t`; separate continuity in each
    -- variable is the printed hypothesis, joint continuity is not assumed. Only `hcont_t`
    -- is consumed below
    (hcont_θ : ∀ t : ℝ, Continuous fun θ : ℝ => (P θ {y | T y ≤ t}).toReal)
    -- USER-INPUT: the family is non-degenerate — distinct parameters give distinct laws. This
    -- is part of the classical monotone-likelihood-ratio definition and is required for the
    -- uniqueness conjunct: without it `θ ↦ F_θ(T x)` is antitone but not STRICTLY antitone, so
    -- the confidence-bound root need not be unique. `power_strictMono_oneSided` carries the
    -- same hypothesis for the same reason.
    (hdist : ∀ θ θ' : ℝ, θ < θ' → P θ ≠ P θ')
    -- USER-INPUT: the level, nondegenerate
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    -- REPAIR (see the docstring): the defining equation `F_θ(t) = 1 − α` is solvable at
    -- every level of the statistic. Without it the printed statement is FALSE, because a
    -- real-valued lower bound cannot express an empty inverted confidence set
    (hsolvable : ∀ t : ℝ, ∃ θ : ℝ, (P θ {y | T y ≤ t}).toReal = 1 - α) :
    ∃ θlow : 𝓧 → ℝ, Measurable θlow ∧
      IsUMAConfidence P (fun θ₀ : ℝ => Set.Ioi θ₀) (fun x => Set.Ici (θlow x)) (1 - α) ∧
      ∀ (x : 𝓧) (θhat : ℝ), (P θhat {y | T y ≤ T x}).toReal = 1 - α →
        (∀ θ' : ℝ, (P θ' {y | T y ≤ T x}).toReal = 1 - α → θ' = θhat) ∧ θlow x = θhat := by
  classical
  -- The threshold of the size-`α` one-sided test at each null value.
  have hCex : ∀ θ₀ : ℝ, ∃ C : ℝ, (P θ₀ {y | T y ≤ C}).toReal = 1 - α ∧
      ∀ t : ℝ, ((P θ₀ {y | T y ≤ t}).toReal ≤ 1 - α ↔ t ≤ C) :=
    fun θ₀ => cb_exists_threshold hT θ₀ (hcont_t θ₀) (by linarith) (by linarith)
  choose C hCval hCiff using hCex
  -- The lower bound: the root of `F_θ(T x) = 1 − α`.
  choose θlow hθlow using fun x : 𝓧 => hsolvable (T x)
  -- Two distinct parameters cannot both solve the equation at the same level.
  have hkey : ∀ t θ θ' : ℝ, θ < θ' → (P θ {y | T y ≤ t}).toReal = 1 - α →
      (P θ' {y | T y ≤ t}).toReal = 1 - α → False := by
    intro t ϑ ϑ' hlt h1 h2
    have hp1 : power P (oneSidedTest T t 0) ϑ = α := by
      rw [cb_power_oneSided hT t ϑ, h1]; ring
    have hp2 : power P (oneSidedTest T t 0) ϑ' = α := by
      rw [cb_power_oneSided hT t ϑ', h2]; ring
    have hstrict := power_strictMono_oneSided μ P p hp T hT hMLR hdist
      (C := t) (γ := 0) ⟨le_refl 0, zero_le_one⟩ ϑ ϑ' hlt
      (by rw [hp1]; exact hα₀) (by rw [hp1]; exact hα₁)
      (by rw [hp2]; exact hα₀) (by rw [hp2]; exact hα₁)
    rw [hp1, hp2] at hstrict
    exact lt_irrefl α hstrict
  -- The acceptance regions are exactly the events `{θ̲ ≤ θ₀}`.
  have hAeq : ∀ θ₀ : ℝ, {x : 𝓧 | θlow x ≤ θ₀} = {x : 𝓧 | T x ≤ C θ₀} := by
    intro θ₀
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx
      rw [← hCiff θ₀ (T x)]
      have hmono : (P θ₀ {y | T y ≤ T x}).toReal ≤ (P (θlow x) {y | T y ≤ T x}).toReal :=
        cdf_antitone μ P p hp T hT hMLR (T x) hx
      rw [hθlow x] at hmono
      exact hmono
    · intro hx
      by_contra hcon
      push_neg at hcon
      have h1 : (P θ₀ {y | T y ≤ T x}).toReal ≤ 1 - α := (hCiff θ₀ (T x)).mpr hx
      have h2 : (P (θlow x) {y | T y ≤ T x}).toReal ≤ (P θ₀ {y | T y ≤ T x}).toReal :=
        cdf_antitone μ P p hp T hT hMLR (T x) hcon.le
      rw [hθlow x] at h2
      exact hkey (T x) θ₀ (θlow x) hcon (le_antisymm h1 h2) (hθlow x)
  have hmeasA : ∀ θ₀ : ℝ, MeasurableSet {x : 𝓧 | T x ≤ C θ₀} := fun θ₀ =>
    measurableSet_le hT measurable_const
  have hmeasθlow : Measurable θlow := by
    refine measurable_of_Iic fun θ₀ => ?_
    have : θlow ⁻¹' Set.Iic θ₀ = {x : 𝓧 | T x ≤ C θ₀} := by
      rw [← hAeq θ₀]; rfl
    rw [this]
    exact hmeasA θ₀
  -- Each acceptance test is UMP against the single null value `θ₀`.
  have hUMP : ∀ θ₀ : ℝ,
      IsUMP P {θ₀} (Set.Ioi θ₀) α (acceptanceTest {x : 𝓧 | T x ≤ C θ₀}) := by
    intro θ₀
    rw [cb_acceptanceTest_eq]
    have hsize : power P (oneSidedTest T (C θ₀) 0) θ₀ = α := by
      rw [cb_power_oneSided hT (C θ₀) θ₀, hCval θ₀]; ring
    have hz : ∃ z, C θ₀ ≤ T z ∧ 0 < p θ₀ z :=
      cb_exists_pos_density hp hT (by rw [hsize]; exact hα₀)
    refine ⟨cb_isCriticalFn hT (C θ₀), ?_, ?_⟩
    · intro ϑ hϑ
      rw [Set.mem_singleton_iff] at hϑ
      subst hϑ
      exact hsize.le
    · intro ψ hψ hψlevel ϑ hϑ
      have hlt : θ₀ < ϑ := Set.mem_Ioi.mp hϑ
      have hMP := cb_isMostPowerful hp hT hMLR hlt hz
      have hlevel0 : powerAgainst (P θ₀) ψ ≤ power P (oneSidedTest T (C θ₀) 0) θ₀ := by
        rw [hsize]; exact hψlevel θ₀ rfl
      exact hMP.2.2 ψ hψ hlevel0
  -- Inversion.
  have hconfeq : confidenceSet (fun θ₀ : ℝ => {x : 𝓧 | T x ≤ C θ₀})
      = fun x => Set.Ici (θlow x) := by
    funext x
    ext θ₀
    simp only [confidenceSet, Set.mem_setOf_eq, Set.mem_Ici]
    constructor
    · intro h
      have : x ∈ {x : 𝓧 | θlow x ≤ θ₀} := by rw [hAeq θ₀]; exact h
      exact this
    · intro h
      have : x ∈ {x : 𝓧 | T x ≤ C θ₀} := by rw [← hAeq θ₀]; exact h
      exact this
  refine ⟨θlow, hmeasθlow, ?_, ?_⟩
  · have huma := isUMA_of_UMP P (α := α) (K := fun θ₀ : ℝ => Set.Ioi θ₀)
      hα₀.le hα₁.le hmeasA hUMP
    rwa [hconfeq] at huma
  · intro x θhat hθhat
    have huniq : ∀ θ' : ℝ, (P θ' {y | T y ≤ T x}).toReal = 1 - α → θ' = θhat := by
      intro θ' hθ'
      rcases lt_trichotomy θ' θhat with h | h | h
      · exact (hkey (T x) θ' θhat h hθ' hθhat).elim
      · exact h
      · exact (hkey (T x) θhat θ' h hθhat hθ').elim
    exact ⟨huniq, huniq (θlow x) (hθlow x)⟩

end StatLean.HypothesisTesting
