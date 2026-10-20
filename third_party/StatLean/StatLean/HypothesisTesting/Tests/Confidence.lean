module
public import StatLean.HypothesisTesting.Tests.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Tests and confidence sets: the duality

Testing a hypothesis for every parameter value at once *is* a confidence statement. If, for
each `θ`, `A θ ⊆ 𝓧` is the acceptance region of a level-`α` test of the simple hypothesis
`H(θ)`, then
$$ S(x) \;=\; \{\theta : x \in A(\theta)\} $$
is a family of confidence sets at confidence level `1 − α`, and conversely every confidence
family arises this way ("test inversion"). Optimality transfers as well: if each `A θ₀` comes
from a test that is uniformly most powerful against the alternatives `K(θ₀)`, then `S`
minimizes the probability of covering each *false* value `θ₀`, uniformly over `θ ∈ K(θ₀)` —
it is **uniformly most accurate**.

This file fixes:

* `confidenceSet A` — the inverted family `S(x) = {θ : x ∈ A θ}`;
* `IsConfidenceFamily P S γ` — coverage at level `γ`, `P_θ{θ ∈ S(X)} ≥ γ` for every `θ`;
* `IsUMAConfidence P K S γ` — uniformly most accurate at level `γ` against `K`;
* `acceptanceTest A` — the nonrandomized test with acceptance region `A`;

and states the two directions of the duality together with the optimality transfer.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.5 (Confidence Bounds), Theorem 3.5.1 (the duality between families of
tests and confidence sets). (`TSH4 §3.5 Thm 3.5.1`.)

**Proof formalization notes.**
* `IsConfidenceFamily` compares in `ℝ≥0∞` (`ENNReal.ofReal γ ≤ P θ {x | θ ∈ S x}`), which
  keeps the definition free of `toReal` side conditions and makes a negative `γ` vacuous
  rather than junk.
* `IsUMAConfidence` quantifies over competitor families whose slices `{x | θ ∈ S' x}` are
  measurable. The restriction is a Lean-side necessity, not a weakening of the classical
  statement: the argument inverts the competitor into a genuine test, and a critical function
  must be measurable. Coverage of a non-measurable family is not a probability statement in
  the first place.
* Tests are the critical functions of the area's data model, so the acceptance region `A`
  enters through the nonrandomized test `acceptanceTest A = 1_{Aᶜ}`; the level condition of
  the book is then `IsLevel P {θ} (acceptanceTest (A θ)) α`, and `power_acceptanceTest`
  converts it into the measure statement `P_θ(A(θ)ᶜ) ≤ α` used in the proofs.
* Only the one-sided framing of the optimality transfer is stated: for each null value `θ₀`
  the competitor class is the tests of `H(θ₀)` against `K(θ₀)`, and the conclusion compares
  false-coverage probabilities at parameter points of `K(θ₀)`. The lower/upper confidence
  *bound* specialization (`S(x)` an interval determined by a monotone family) is a separate
  statement and is not derived here.

**Bibliographic comments.** Confidence sets, the confidence level, and the inversion of tests
are due to J. Neyman ("Outline of a theory of statistical estimation based on the classical
theory of probability," *Phil. Trans. R. Soc. A* **236** (1937), 333–380); the accuracy
criterion and its link with the power of the underlying tests appear there and in
J. Neyman and E. S. Pearson's optimality program ("On the problem of the most efficient tests
of statistical hypotheses," *Phil. Trans. R. Soc. A* **231** (1933), 289–337).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **inverted family of confidence sets** of a family of acceptance regions:
`S(x) = {θ : x ∈ A θ}`, the parameter values not rejected on observing `x`. -/
def confidenceSet (A : Θ → Set 𝓧) (x : 𝓧) : Set Θ :=
  {θ | x ∈ A θ}

/-- A **family of confidence sets at confidence level `γ`**: the random set `S(X)` covers the
true parameter with probability at least `γ`, whatever the true parameter is. -/
def IsConfidenceFamily (P : Θ → Measure 𝓧) (S : 𝓧 → Set Θ) (γ : ℝ) : Prop :=
  ∀ θ, ENNReal.ofReal γ ≤ P θ {x | θ ∈ S x}

/-- A **uniformly most accurate** family of confidence sets at level `γ` against the
alternatives `K`: it has level `γ`, and for every false value `θ₀` it covers `θ₀` with the
smallest possible probability, uniformly over the parameters `θ ∈ K θ₀` at which `θ₀` is
false, among all level-`γ` competitors (with measurable slices; see the file header). -/
def IsUMAConfidence (P : Θ → Measure 𝓧) (K : Θ → Set Θ) (S : 𝓧 → Set Θ) (γ : ℝ) : Prop :=
  IsConfidenceFamily P S γ ∧
    ∀ S' : 𝓧 → Set Θ, (∀ θ, MeasurableSet {x | θ ∈ S' x}) → IsConfidenceFamily P S' γ →
      ∀ θ₀ : Θ, ∀ θ ∈ K θ₀, P θ {x | θ₀ ∈ S x} ≤ P θ {x | θ₀ ∈ S' x}

/-- The **nonrandomized test with acceptance region `A`**: it rejects exactly off `A`. -/
noncomputable def acceptanceTest (A : Set 𝓧) : 𝓧 → ℝ :=
  Set.indicator Aᶜ (1 : 𝓧 → ℝ)

/-- Test inversion, pointwise: `θ` is in the confidence set at `x` exactly when `x` is accepted
by the test of `H(θ)`. -/
theorem mem_confidenceSet_iff (A : Θ → Set 𝓧) (x : 𝓧) (θ : Θ) :
    θ ∈ confidenceSet A x ↔ x ∈ A θ := Iff.rfl

/-- The test with a measurable acceptance region is a critical function. -/
theorem isCriticalFn_acceptanceTest {A : Set 𝓧}
    -- LEAN-ONLY: measurability of the acceptance region; a test must be measurable
    (hA : MeasurableSet A) :
    IsCriticalFn (acceptanceTest A) := by
  refine ⟨measurable_const.indicator hA.compl, fun x => ?_⟩
  rw [acceptanceTest]
  by_cases h : x ∈ Aᶜ
  · rw [Set.indicator_of_mem h]; simp [Set.mem_Icc]
  · rw [Set.indicator_of_notMem h]; simp [Set.mem_Icc]

/-- The power of a nonrandomized test is the probability of its rejection region. -/
theorem power_acceptanceTest (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {A : Set 𝓧}
    -- LEAN-ONLY: measurability of the acceptance region; needed to integrate the indicator
    (hA : MeasurableSet A) (θ : Θ) :
    power P (acceptanceTest A) θ = (P θ Aᶜ).toReal := by
  unfold power acceptanceTest
  rw [integral_indicator_one hA.compl]
  rfl

/-- **Test inversion produces confidence sets**: inverting a family of level-`α` tests gives a
family of confidence sets at confidence level `1 − α`. -/
theorem isConfidenceFamily_of_acceptance (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] {A : Θ → Set 𝓧} {α : ℝ}
    -- USER-INPUT: a nonnegative significance level; classical
    (hα : 0 ≤ α)
    -- LEAN-ONLY: measurability of the acceptance regions; a test must be measurable
    (hmeas : ∀ θ, MeasurableSet (A θ))
    -- USER-INPUT: each `A θ` accepts `H(θ)` with a level-`α` test; Neyman (1937)
    (hlevel : ∀ θ, IsLevel P {θ} (acceptanceTest (A θ)) α) :
    IsConfidenceFamily P (confidenceSet A) (1 - α) := by
  intro θ
  have hset : {x : 𝓧 | θ ∈ confidenceSet A x} = A θ :=
    Set.ext (fun x => mem_confidenceSet_iff A x θ)
  rw [hset]
  have hp : (P θ (A θ)ᶜ).toReal ≤ α := by
    have := hlevel θ θ rfl
    rwa [power_acceptanceTest P (hmeas θ) θ] at this
  have hp' : 1 - (P θ (A θ)).toReal ≤ α := by
    rw [← ENNReal.toReal_one, ← ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ← prob_compl_eq_one_sub (hmeas θ)]
    exact hp
  calc ENNReal.ofReal (1 - α) ≤ ENNReal.ofReal ((P θ (A θ)).toReal) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = P θ (A θ) := ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- **Confidence sets produce tests** (the converse inversion): the slices of a confidence
family at level `γ` are acceptance regions of level-`(1 − γ)` tests. -/
theorem isLevel_acceptanceTest_of_isConfidenceFamily (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] {S : 𝓧 → Set Θ} {γ : ℝ}
    -- USER-INPUT: a confidence level in `[0,1]`; classical
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    -- LEAN-ONLY: measurability of the slices; a test must be measurable
    (hmeas : ∀ θ, MeasurableSet {x : 𝓧 | θ ∈ S x})
    -- USER-INPUT: the family has confidence level `γ`; Neyman (1937)
    (hS : IsConfidenceFamily P S γ) (θ : Θ) :
    IsLevel P {θ} (acceptanceTest {x : 𝓧 | θ ∈ S x}) (1 - γ) := by
  intro θ' hθ'
  rw [Set.mem_singleton_iff] at hθ'
  subst hθ'
  rw [power_acceptanceTest P (hmeas θ') θ', prob_compl_eq_one_sub (hmeas θ'),
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  have hg : γ ≤ (P θ' {x : 𝓧 | θ' ∈ S x}).toReal := by
    have := ENNReal.toReal_mono (measure_ne_top (P θ') _) (hS θ')
    rwa [ENNReal.toReal_ofReal hγ0] at this
  linarith

/-- **Optimality transfers along the duality**: inverting a family of uniformly most powerful
level-`α` tests — that of `H(θ₀)` against `K(θ₀)`, for each `θ₀` — gives a uniformly most
accurate family of confidence sets at level `1 − α`. -/
theorem isUMA_of_UMP (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {A : Θ → Set 𝓧} {K : Θ → Set Θ} {α : ℝ}
    -- USER-INPUT: a significance level in `[0,1]`; classical
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    -- LEAN-ONLY: measurability of the acceptance regions; a test must be measurable
    (hmeas : ∀ θ, MeasurableSet (A θ))
    -- USER-INPUT: for each null value, the test of `H(θ₀)` against `K(θ₀)` is UMP at level
    -- `α`; Neyman–Pearson (1933)
    (hUMP : ∀ θ₀ : Θ, IsUMP P {θ₀} (K θ₀) α (acceptanceTest (A θ₀))) :
    IsUMAConfidence P K (confidenceSet A) (1 - α) := by
  refine ⟨isConfidenceFamily_of_acceptance P hα0 hmeas (fun θ => (hUMP θ).2.1), ?_⟩
  intro S' hS'meas hS'conf θ₀ θ hθ
  -- The inverted competitor test of `H(θ₀)`.
  have hψlevel : IsLevel P {θ₀} (acceptanceTest {x : 𝓧 | θ₀ ∈ S' x}) α := by
    have h := isLevel_acceptanceTest_of_isConfidenceFamily P (by linarith) (by linarith)
      hS'meas hS'conf θ₀
    rwa [show (1 : ℝ) - (1 - α) = α by ring] at h
  have hpow := (hUMP θ₀).2.2 (acceptanceTest {x : 𝓧 | θ₀ ∈ S' x})
    (isCriticalFn_acceptanceTest (hS'meas θ₀)) hψlevel θ hθ
  rw [power_acceptanceTest P (hS'meas θ₀) θ, power_acceptanceTest P (hmeas θ₀) θ] at hpow
  have hcov : (P θ (A θ₀)).toReal ≤ (P θ {x : 𝓧 | θ₀ ∈ S' x}).toReal := by
    have hc1 : (P θ (A θ₀)ᶜ).toReal = 1 - (P θ (A θ₀)).toReal := by
      rw [prob_compl_eq_one_sub (hmeas θ₀), ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
        ENNReal.toReal_one]
    have hc2 : (P θ {x : 𝓧 | θ₀ ∈ S' x}ᶜ).toReal
        = 1 - (P θ {x : 𝓧 | θ₀ ∈ S' x}).toReal := by
      rw [prob_compl_eq_one_sub (hS'meas θ₀),
        ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
    rw [hc1, hc2] at hpow
    linarith
  have hset : {x : 𝓧 | θ₀ ∈ confidenceSet A x} = A θ₀ :=
    Set.ext (fun x => mem_confidenceSet_iff A x θ₀)
  calc P θ {x : 𝓧 | θ₀ ∈ confidenceSet A x}
      = P θ (A θ₀) := by rw [hset]
    _ = ENNReal.ofReal ((P θ (A θ₀)).toReal) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ((P θ {x : 𝓧 | θ₀ ∈ S' x}).toReal) := ENNReal.ofReal_le_ofReal hcov
    _ = P θ {x : 𝓧 | θ₀ ∈ S' x} := ENNReal.ofReal_toReal (measure_ne_top _ _)

end StatLean.HypothesisTesting
