module
public import StatLean.HypothesisTesting.Tests.Defs
public import StatLean.MultipleTesting.PValues.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# p-values from nested rejection regions

A family of rejection regions `R : ℝ → Set 𝓧` is **nested** when `R α ⊆ R α'` for `α ≤ α'`:
rejecting at a smaller significance level is a stronger verdict. For such a family the
**p-value** of an observation is the smallest level at which the hypothesis is rejected,
$$ \hat p(x) \;=\; \inf\{\alpha : x \in R_\alpha\}, $$
and the fundamental property is that a p-value built from *valid* regions is itself valid: if
each `R α` has null probability at most `α`, then `P_θ{\hat p ≤ u} ≤ u` for every null `θ` —
`\hat p` is **super-uniform**, the standing null assumption of the multiple-testing area.

The converse direction is recorded too: the test that rejects when `\hat p ≤ α` is a level-`α`
test.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.3 (p-values), Lemma 3.3.1 (super-uniformity of the p-value obtained from a
nested family of rejection regions). (`TSH4 §3.3 Lem 3.3.1`.)

**Proof formalization notes.**
* `nestedPValue` is the literal infimum, with the usual `Real.sInf` junk conventions (empty or
  unbounded-below set ↦ `0`). Both junk corners are genuinely dangerous here — an `x` that no
  region ever rejects would get p-value `0` and destroy super-uniformity (take `R ≡ ∅`) — so
  the two non-degeneracy hypotheses `hR_neg` ("no rejection at a negative level", which makes
  the set bounded below) and `hR_exh` ("every point is rejected at some level below one",
  which makes it nonempty) appear explicitly wherever the value of `nestedPValue` is used.
  They are properties of a genuine family of rejection regions, not regularity fat.
* Measurability of the regions is *not* assumed for super-uniformity: the argument only
  compares the measures of nested sets, `P_θ{\hat p ≤ u} ≤ P_θ(R v)` for `v > u`, and
  monotonicity of a measure needs no measurability. It reappears exactly where an integral is
  formed, as the measurability of the rejection event in `isLevel_pValueTest`.
* Super-uniformity is stated through the multiple-testing area's `SuperUniform` predicate, so
  that p-values produced here feed the FDR/FWER results unchanged. For `t > 1` the bound is
  trivial (probability measures), so the content is the range `0 ≤ t ≤ 1` of the classical
  statement.
* Only the inequality direction is formalized here. Under exact validity of the regions
  (`P_θ(R α) = α`) the same argument returns the exact-uniform conclusion; that strengthening
  is left to the consumer that needs it.

**Bibliographic comments.** Significance levels attained by the data go back to R. A. Fisher
(*Statistical Methods for Research Workers*, Oliver & Boyd, 1925); the systematic treatment of
the p-value as a random variable, and of its null distribution, is due to R. R. Bahadur
("Stochastic comparison of tests," *Ann. Math. Statist.* **31** (1960), 276–295). The validity
condition itself is folklore with no single seminal source. The underlying family of rejection
regions is the Neyman–Pearson construction ("On the problem of the most efficient tests of
statistical hypotheses," *Phil. Trans. R. Soc. A* **231** (1933), 289–337).
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace StatLean.HypothesisTesting

open StatLean.MultipleTesting (SuperUniform)

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **p-value of a nested family of rejection regions**: the smallest significance level at
which `x` is rejected, `p̂(x) = inf {α : x ∈ R α}`.

Junk conventions (`Real.sInf`): if no level rejects `x` the value is `0`, and so is the value
when the set of rejecting levels is unbounded below. Both corners are excluded by the
hypotheses `hR_exh` and `hR_neg` of the theorems below. -/
noncomputable def nestedPValue (R : ℝ → Set 𝓧) (x : 𝓧) : ℝ :=
  sInf {α : ℝ | x ∈ R α}

/-- The p-value is nonnegative as soon as no negative level rejects. -/
theorem nestedPValue_nonneg {R : ℝ → Set 𝓧}
    -- USER-INPUT: no rejection at a negative significance level; classical
    (hR_neg : ∀ α : ℝ, α < 0 → R α = ∅)
    (x : 𝓧) :
    0 ≤ nestedPValue R x := by
  rcases Set.eq_empty_or_nonempty {α : ℝ | x ∈ R α} with h | h
  · show 0 ≤ sInf {α : ℝ | x ∈ R α}
    rw [h, Real.sInf_empty]
  · apply le_csInf h
    intro α hα
    simp only [Set.mem_setOf_eq] at hα
    by_contra hlt
    push_neg at hlt
    rw [hR_neg α hlt] at hα
    exact absurd hα (Set.notMem_empty x)

/-- The p-value is at most one as soon as every point is rejected at some level below one. -/
theorem nestedPValue_le_one {R : ℝ → Set 𝓧}
    -- USER-INPUT: no rejection at a negative significance level; classical
    (hR_neg : ∀ α : ℝ, α < 0 → R α = ∅)
    -- USER-INPUT: every observation is rejected at some level below one; classical
    (hR_exh : ∀ x : 𝓧, ∃ α < 1, x ∈ R α)
    (x : 𝓧) :
    nestedPValue R x ≤ 1 := by
  obtain ⟨α, hα1, hαx⟩ := hR_exh x
  have hbdd : BddBelow {β : ℝ | x ∈ R β} := by
    refine ⟨0, fun β hβ => ?_⟩
    simp only [Set.mem_setOf_eq] at hβ
    by_contra h
    push_neg at h
    rw [hR_neg β h] at hβ
    exact absurd hβ (Set.notMem_empty x)
  have : nestedPValue R x ≤ α := csInf_le hbdd hαx
  linarith

/-- **Validity of the p-value of a nested family of valid rejection regions**: if the regions
are nested and each has null probability at most its level, the induced p-value is
super-uniform under every null distribution. -/
theorem superUniform_nestedPValue (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (Θ₀ : Set Θ) {R : ℝ → Set 𝓧}
    -- USER-INPUT: the rejection regions are nested in the significance level; classical
    (hmono : Monotone R)
    -- USER-INPUT: no rejection at a negative significance level; classical
    (hR_neg : ∀ α : ℝ, α < 0 → R α = ∅)
    -- USER-INPUT: every observation is rejected at some level below one; classical
    (hR_exh : ∀ x : 𝓧, ∃ α < 1, x ∈ R α)
    -- USER-INPUT: each region is valid at its own level, uniformly over the null; classical
    (hvalid : ∀ α : ℝ, 0 < α → α < 1 → ∀ θ ∈ Θ₀, P θ (R α) ≤ ENNReal.ofReal α) :
    ∀ θ ∈ Θ₀, SuperUniform (nestedPValue R) (P θ) := by
  intro θ hθ t ht
  by_cases htlt : t < 1
  · refine ge_of_tendsto (a := ENNReal.ofReal t)
      ((ENNReal.continuous_ofReal.tendsto t).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi t))) ?_
    have hv1 : ∀ᶠ v in 𝓝[>] t, v < 1 :=
      Filter.eventually_of_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htlt))
        (fun v hv => Set.mem_Iio.mp hv)
    filter_upwards [self_mem_nhdsWithin, hv1] with v hv hv1'
    rw [Set.mem_Ioi] at hv
    have hsub : {x : 𝓧 | nestedPValue R x ≤ t} ⊆ R v := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      have hnonempty : {α : ℝ | x ∈ R α}.Nonempty := by
        obtain ⟨β, _, hβx⟩ := hR_exh x; exact ⟨β, hβx⟩
      have hbdd : BddBelow {α : ℝ | x ∈ R α} := by
        refine ⟨0, fun α hα => ?_⟩
        simp only [Set.mem_setOf_eq] at hα
        by_contra h
        push_neg at h
        rw [hR_neg α h] at hα
        exact absurd hα (Set.notMem_empty x)
      have hlt : sInf {α : ℝ | x ∈ R α} < v := lt_of_le_of_lt hx hv
      obtain ⟨α, hαmem, hαv⟩ := exists_lt_of_csInf_lt hnonempty hlt
      exact hmono (le_of_lt hαv) hαmem
    calc P θ {x : 𝓧 | nestedPValue R x ≤ t}
        ≤ P θ (R v) := measure_mono hsub
      _ ≤ ENNReal.ofReal v := hvalid v (by linarith) hv1' θ hθ
  · push_neg at htlt
    calc P θ {x : 𝓧 | nestedPValue R x ≤ t}
        ≤ P θ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal t := ENNReal.one_le_ofReal.mpr htlt

/-- **The p-value test has level `α`**: rejecting when the p-value is at most `α` is a
level-`α` test, for any super-uniform p-value. -/
theorem isLevel_pValueTest (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (Θ₀ : Set Θ) (R : ℝ → Set 𝓧) {α : ℝ}
    -- USER-INPUT: a nonnegative significance level; classical
    (hα : 0 ≤ α)
    -- LEAN-ONLY: measurability of the rejection event; needed to integrate its indicator
    (hmeas : MeasurableSet {x : 𝓧 | nestedPValue R x ≤ α})
    -- USER-INPUT: the p-value is valid under every null distribution; classical
    (hsu : ∀ θ ∈ Θ₀, SuperUniform (nestedPValue R) (P θ)) :
    IsLevel P Θ₀ (Set.indicator {x : 𝓧 | nestedPValue R x ≤ α} (1 : 𝓧 → ℝ)) α := by
  intro θ hθ
  unfold power
  rw [integral_indicator_one hmeas]
  calc (P θ {x : 𝓧 | nestedPValue R x ≤ α}).toReal
      ≤ (ENNReal.ofReal α).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hsu θ hθ α hα)
    _ = α := ENNReal.toReal_ofReal hα

end StatLean.HypothesisTesting
