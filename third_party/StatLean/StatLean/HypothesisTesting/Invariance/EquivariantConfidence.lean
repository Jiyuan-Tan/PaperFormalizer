module
public import StatLean.HypothesisTesting.Invariance.Defs
public import StatLean.HypothesisTesting.Tests.Confidence

@[expose] public section

/-!
# Equivariant confidence sets and uniformly most accurate equivariance

The duality between tests and confidence sets — `θ ∈ S(x)` exactly when `x ∈ A(θ)` — is
independent of what the parameter is: real, vector-valued, or a label for an unknown
distribution. This file carries the invariance reduction across that duality.

A group acting on the data induces an action on the parameter space and hence on *sets* of
parameters, `g^*S = {ḡθ : θ ∈ S}`. A confidence family is **equivariant** when
`g^*S(x) = S(g·x)`: re-expressing the data in transformed coordinates transforms the
confidence statement in the matching way, so the statement does not depend on the
coordinate system. (The older name "invariant" is misleading — the sets do move.)

The dictionary is exact. A confidence family is equivariant precisely when its dual
acceptance-region family is equivariant, `A(ḡθ) = g·A(θ)`. Specializing to group elements
that *fix* `θ` — the transformations under which the hypothesis `θ' = θ` is itself
invariant — an equivariant confidence family has acceptance regions invariant under each
stabilizer. The optimality transfer follows: if for every `θ` the acceptance region is the
UMP invariant test of `θ' = θ` at level `α`, then every competing equivariant confidence
family at level `1 − α` yields invariant tests that are no more powerful, hence covers
every false parameter value at least as often. The original family is therefore uniformly
most accurate among equivariant families.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 6 (Invariance), §6.11
(Equivariant Confidence Sets), Lemma 6.11.1 (equivariant confidence sets correspond to
invariant acceptance regions). (`TSH4 §6.11 Lem 6.11.1`.)

**Main results.**
* `IsEquivariantConfidence`, `IsUMAEquivariant` — equivariance and uniform accuracy;
* `isEquivariantConfidence_iff_acceptance_equivariant` — the dictionary, both directions;
* `acceptance_invariant_of_equivariantConfidence` — equivariant confidence sets have
  stabilizer-invariant acceptance regions;
* `isUMAEquivariant_of_isUMPInvariant` — UMP invariant acceptance regions give uniformly
  most accurate equivariant confidence sets.

**Dependency note.** `confidenceSet`, `IsConfidenceFamily`, `acceptanceTest` and the two
bridge lemmas `isCriticalFn_acceptanceTest` / `power_acceptanceTest` come from the sibling
`Tests/Confidence.lean` (work item `ht/test-foundations`), which carries the
test–confidence-set duality and is itself `sorry`-free; the optimality transfer below is
proved through those bridges.

**Proof formalization notes.**
* The induced action on parameter sets is the image `(g • ·) '' S`, so equivariance reads
  `(g • ·) '' S x = S (g • x)`.
* The source's group `G_θ` is *any* group of transformations leaving the hypothesis
  `θ' = θ` invariant; the only property its proof uses is `ḡθ = θ`. The statements below
  are therefore given for the **stabilizer** of `θ`, which is the largest such group — so
  they specialize to every `G_θ` the source allows.
* Part (i) of the source's lemma follows from the dictionary; the dictionary itself is the
  honest two-directional statement, since stabilizer-invariance of the acceptance regions
  alone is *not* enough to recover equivariance of the confidence family (full
  equivariance `A(ḡθ) = g·A(θ)` is).
* Acceptance regions enter the optimality statement through the nonrandomized test
  rejecting off `A θ`, i.e. the indicator of `(A θ)ᶜ`.
* Uniform accuracy is stated as the source defines it: minimizing the probability of
  covering each *false* value `θ' ≠ θ`.
* **Definition amendment (documented deviation).** `IsUMAEquivariant` quantifies its
  competitors over families with **measurable slices**, matching `IsUMAConfidence` in
  `Tests/Confidence.lean`. Without it the optimality transfer is not even expressible: the
  argument inverts the competitor `S'` into the test `1_{Bᶜ}` with `B = {x | θ' ∈ S' x}`,
  which must be a critical function, and `P θ B` on the right-hand side of the conclusion
  is not a probability unless `B` is measurable. This is the standing convention of the
  sibling file, not a weakening special to this one.

**Bibliographic comments.** The duality between families of tests and confidence sets is
due to J. Neyman ("Outline of a theory of statistical estimation based on the classical
theory of probability," *Phil. Trans. R. Soc. A* **236** (1937), 333–380). Equivariance of
confidence sets and the transfer of invariance optimality across the duality belong to the
invariance program of G. A. Hunt and C. Stein ("Most stringent tests of statistical
hypotheses," unpublished manuscript, 1946) and C. Stein ("Some problems in multivariate
analysis, Part I," Technical Report 6, Department of Statistics, Stanford University,
1956), as developed in E. L. Lehmann's lecture tradition of the 1950s; the relation
between invariance and sufficiency in this setting is treated by W. J. Hall,
R. A. Wijsman and J. K. Ghosh ("The relationship between sufficiency and invariance with
applications in sequential analysis," *Ann. Math. Statist.* **36** (1965), 575–614).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {G Θ 𝓧 : Type*} [Group G] [MeasurableSpace 𝓧] [MulAction G 𝓧] [MulAction G Θ]

/-- **Equivariant confidence family**: applying the induced parameter action to the
confidence set computed from `x` gives the confidence set computed from `g·x`. -/
def IsEquivariantConfidence (G : Type*) [Group G] [MulAction G 𝓧] [MulAction G Θ]
    (S : 𝓧 → Set Θ) : Prop :=
  ∀ (g : G) (x : 𝓧), (fun θ => g • θ) '' S x = S (g • x)

/-- **Uniformly most accurate equivariant** at confidence level `lvl`: an equivariant
confidence family at that level which, among all such families, minimizes the probability
of covering every false parameter value.

Competitors are quantified with **measurable slices** `{x | θ ∈ S' x}`, exactly as in
`IsUMAConfidence` in `Tests/Confidence.lean`. This is a Lean-side necessity, not a
weakening of the classical statement: the argument inverts the competitor into a genuine
test, and a critical function must be measurable — and the coverage of a family with
non-measurable slices is not a probability statement in the first place. -/
def IsUMAEquivariant (G : Type*) [Group G] [MulAction G 𝓧] [MulAction G Θ]
    (P : Θ → Measure 𝓧) (lvl : ℝ) (S : 𝓧 → Set Θ) : Prop :=
  IsEquivariantConfidence G S ∧ IsConfidenceFamily P S lvl ∧
    ∀ S' : 𝓧 → Set Θ, IsEquivariantConfidence G S' → (∀ θ, MeasurableSet {x | θ ∈ S' x}) →
      IsConfidenceFamily P S' lvl →
      ∀ (θ θ' : Θ), θ' ≠ θ → P θ {x | θ' ∈ S x} ≤ P θ {x | θ' ∈ S' x}

/-- **The dictionary between equivariant confidence sets and equivariant acceptance
regions.** A confidence family obtained by dualizing a family of acceptance regions is
equivariant exactly when the acceptance regions themselves are equivariant. -/
theorem isEquivariantConfidence_iff_acceptance_equivariant {A : Θ → Set 𝓧} :
    IsEquivariantConfidence G (confidenceSet A) ↔
      ∀ (g : G) (θ : Θ), A (g • θ) = (fun x => g • x) '' A θ := by
  have hinj : ∀ (g : G) (a b : Θ), g • a = g • b → a = b := fun g a b h => by
    have := congrArg (g⁻¹ • ·) h; simpa only [inv_smul_smul] using this
  constructor
  · -- equivariance of the confidence family ⇒ equivariance of the acceptance regions
    intro hEq g θ
    ext y
    constructor
    · intro hy
      refine ⟨g⁻¹ • y, ?_, smul_inv_smul g y⟩
      have hx := Set.ext_iff.mp (hEq g (g⁻¹ • y)) (g • θ)
      simp only [confidenceSet, smul_inv_smul, Set.mem_image, Set.mem_setOf_eq] at hx
      obtain ⟨θ', hθ', hθ'eq⟩ := hx.mpr hy
      rwa [hinj g θ' θ hθ'eq] at hθ'
    · rintro ⟨x, hx, rfl⟩
      have hx2 := Set.ext_iff.mp (hEq g x) (g • θ)
      simp only [confidenceSet, Set.mem_image, Set.mem_setOf_eq] at hx2
      exact hx2.mp ⟨θ, hx, rfl⟩
  · -- equivariance of the acceptance regions ⇒ equivariance of the confidence family
    intro hA g x
    ext θ'
    simp only [confidenceSet, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      rw [hA g θ]; exact ⟨x, hθ, rfl⟩
    · intro h
      refine ⟨g⁻¹ • θ', ?_, smul_inv_smul g θ'⟩
      have hAe : A θ' = (fun x => g • x) '' A (g⁻¹ • θ') := by
        have := hA g (g⁻¹ • θ'); rwa [smul_inv_smul] at this
      rw [hAe, Set.mem_image] at h
      obtain ⟨a, ha, hae⟩ := h
      have hax : a = x := by
        have := congrArg (g⁻¹ • ·) hae; simpa only [inv_smul_smul] using this
      rwa [hax] at ha

/-- **Equivariant confidence sets have stabilizer-invariant acceptance regions** (part (i)
of the source's lemma). For each parameter value, the acceptance region of the hypothesis
`θ' = θ` is invariant under every transformation fixing `θ`. -/
theorem acceptance_invariant_of_equivariantConfidence {S : 𝓧 → Set Θ}
    -- USER-INPUT: the confidence family is equivariant
    (hS : IsEquivariantConfidence G S)
    (θ : Θ) {g : G}
    -- USER-INPUT: `g` fixes `θ`, i.e. it belongs to a group leaving the hypothesis
    -- `θ' = θ` invariant
    (hg : g • θ = θ) :
    (fun x => g • x) '' {x | θ ∈ S x} = {x | θ ∈ S x} := by
  have hmem : ∀ (g : G) (x : 𝓧) (θ' : Θ), θ' ∈ S (g • x) ↔ g⁻¹ • θ' ∈ S x := by
    intro g x θ'
    rw [← hS g x]
    constructor
    · rintro ⟨θ'', hθ'', rfl⟩; rwa [inv_smul_smul]
    · intro h; exact ⟨g⁻¹ • θ', h, smul_inv_smul _ _⟩
  have hgθ : g⁻¹ • θ = θ := inv_smul_eq_iff.mpr hg.symm
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩; rw [hmem g x θ, hgθ]; exact hx
  · intro hy
    exact ⟨g⁻¹ • y, by rw [hmem g⁻¹ y θ, inv_inv, hg]; exact hy, smul_inv_smul _ _⟩

/-- **UMP invariant acceptance regions give uniformly most accurate equivariant confidence
sets** (part (ii) of the source's lemma). If the dual confidence family is equivariant and
has confidence level `1 − α`, and if for each parameter value the acceptance region is UMP
among tests invariant under the stabilizer, then the confidence family is uniformly most
accurate among equivariant families at that level. -/
theorem isUMAEquivariant_of_isUMPInvariant {P : Θ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {A : Θ → Set 𝓧} {α : ℝ}
    -- USER-INPUT: the dual confidence family is equivariant
    (hS : IsEquivariantConfidence G (confidenceSet A))
    -- USER-INPUT: the dual confidence family has confidence level `1 − α`
    (hlvl : IsConfidenceFamily P (confidenceSet A) (1 - α))
    -- LEAN-ONLY: measurability of the acceptance regions, needed to read them as tests
    (hAmeas : ∀ θ, MeasurableSet (A θ))
    -- USER-INPUT: for each `θ` the acceptance region is the UMP level-`α` test of
    -- `θ' = θ` among tests invariant under the stabilizer of `θ`
    (hUMP : ∀ θ : Θ, IsUMPInvariant ↥(MulAction.stabilizer G θ) P {θ} {θ' | θ' ≠ θ} α
      ((A θ)ᶜ.indicator fun _ => (1 : ℝ))) :
    IsUMAEquivariant G P (1 - α) (confidenceSet A) := by
  refine ⟨hS, hlvl, ?_⟩
  intro S' hS' hS'meas hS'lvl θ θ' hne
  -- The competitor's acceptance region for the hypothesis `· = θ'`.
  set B : Set 𝓧 := {x | θ' ∈ S' x} with hBdef
  have hB : MeasurableSet B := hS'meas θ'
  -- (a) it is invariant under the stabilizer of `θ'`
  have hBinv : IsInvariantTest ↥(MulAction.stabilizer G θ') (acceptanceTest B) := by
    intro g x
    have himg := acceptance_invariant_of_equivariantConfidence hS' θ'
      (MulAction.mem_stabilizer_iff.mp g.2)
    have hiff : ∀ y : 𝓧, (g : G) • y ∈ B ↔ y ∈ B := by
      intro y
      refine ⟨fun hy => ?_, fun hy => ?_⟩
      · rw [hBdef, ← himg] at hy
        obtain ⟨z, hz, hzy⟩ := hy
        have hzy2 : z = y := by
          have := congrArg (fun t => (g : G)⁻¹ • t) hzy
          simpa only [inv_smul_smul] using this
        rwa [hzy2] at hz
      · rw [hBdef, ← himg]; exact ⟨y, hy, rfl⟩
    have hmem : ((g : G) • x ∈ Bᶜ) ↔ (x ∈ Bᶜ) := by
      simp only [Set.mem_compl_iff, hiff]
    have hsm : (g • x : 𝓧) = (g : G) • x := rfl
    simp only [acceptanceTest, hsm]
    by_cases hx : x ∈ Bᶜ
    · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx]
      rfl
    · rw [Set.indicator_of_notMem (fun h => hx (hmem.mp h)), Set.indicator_of_notMem hx]
  -- (b) it has level `α`, because `S'` covers `θ'` with probability at least `1 - α`
  have hBlevel : IsLevel P {θ'} (acceptanceTest B) α := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    rw [power_acceptanceTest P hB]
    have hcovR : 1 - α ≤ (P t B).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp (hS'lvl t)
    have hcompl : (P t Bᶜ).toReal = 1 - (P t B).toReal := by
      have h := measureReal_compl (μ := P t) hB
      simpa [measureReal_def, measure_univ] using h
    rw [hcompl]; linarith
  -- (c) so the UMP invariant acceptance region of `θ'` is at least as powerful at `θ`
  have hdomin := (hUMP θ').2.2.2 (acceptanceTest B) (isCriticalFn_acceptanceTest hB) hBinv
    hBlevel θ (by exact hne.symm)
  have hAtest : ((A θ')ᶜ.indicator fun _ => (1 : ℝ)) = acceptanceTest (A θ') := rfl
  rw [hAtest, power_acceptanceTest P hB, power_acceptanceTest P (hAmeas θ')] at hdomin
  -- (d) read the two powers back as false-coverage probabilities
  have hcomplθ : ∀ C : Set 𝓧, MeasurableSet C → (P θ Cᶜ).toReal = 1 - (P θ C).toReal := by
    intro C hC
    have h := measureReal_compl (μ := P θ) hC
    simpa [measureReal_def, measure_univ] using h
  rw [hcomplθ B hB, hcomplθ (A θ') (hAmeas θ')] at hdomin
  have hle : (P θ (A θ')).toReal ≤ (P θ B).toReal := by linarith
  have hset : {x | θ' ∈ confidenceSet A x} = A θ' := rfl
  rw [hset, hBdef]
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hle

end StatLean.HypothesisTesting
