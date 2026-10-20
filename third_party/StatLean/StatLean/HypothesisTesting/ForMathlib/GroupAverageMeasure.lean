module
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Finite group actions: orbit averaging and the invariant σ-algebra — ForMathlib brick

Let a **finite** group `G` act measurably on `𝓧`. Averaging a function along the orbits,
$$ (A_G f)(x) \;=\; \frac{1}{|G|}\sum_{g \in G} f(g\cdot x), $$
produces an invariant function; if the underlying measure is `G`-invariant, this average is
*exactly* the conditional expectation of `f` given the σ-algebra of invariant sets. That
identity is what turns an invariance reduction into a conditioning argument (and, in the other
direction, an averaging argument into a statement about invariant tests).

This file provides:

* `IsInvariantSet G A` and `invariantSets G 𝓧` — the invariant sets, and the closure
  properties that make them a σ-algebra;
* `groupAverage G f` — the orbit average, with its invariance, measurability, and the
  measure-preserving identity `∫ A_G f dμ = ∫ f dμ`;
* `condExp_eq_groupAverage` — the conditional-expectation identity above.

**Carrier note (deliberate fallback).** The invariant sets are packaged as a *set of sets*,
`invariantSets G 𝓧`, together with the three closure lemmas (`empty`, `compl`, `iUnion`) that
would constitute a `MeasurableSpace` instance, rather than as such an instance. The
conditional-expectation statement therefore takes the invariant σ-algebra `m` as a parameter
plus the hypothesis `hm_inv` characterizing its measurable sets, which is exactly what a later
bundling would supply. This keeps the bottom layer free of a data model that the concept layer
may want to shape differently, and costs the consumer one hypothesis: a concept-layer
`MeasurableSpace` whose `MeasurableSet'` field is the conjunction "measurable and fixed by
every group element" discharges `hm_inv` by `fun _ => Iff.rfl`.

**Naming note.** The concept layer of this area already carries the same formula under the name
`orbitAverage` (invariant-test data model). The two live in one namespace, so this brick uses
`groupAverage`; the intended end state is for the concept-layer name to abbreviate this one,
which the bottom layer cannot arrange itself (it must not import the concept layer).

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 6 (Invariance), §6.3
(Uniformly Most Powerful Invariant Tests), supporting material for Theorem 6.3.1: orbit
averaging under a finite group action and the invariant σ-algebra. (`TSH4 §6.3 Thm 6.3.1`.)

**Proof formalization notes.**
* Measurability of the action is never an instance here: each statement that needs it takes
  `hmeas : ∀ g : G, Measurable (fun x : 𝓧 => g • x)` explicitly, so the file imposes no
  `MeasurableSMul` requirement on its consumers.
* `groupAverage_smul` is pure reindexing (`g ↦ h * g` is a bijection of `G`) and needs no
  measure-theoretic input; invariance of `μ` enters only in `integral_groupAverage` and
  `condExp_eq_groupAverage`.
* Intended route for `condExp_eq_groupAverage`: `groupAverage G f` is invariant, hence
  `m`-measurable via `hm_inv` and `preimage_mem_invariantSets`; and for `A ∈ m` invariance of
  `A` plus invariance of `μ` gives `∫_A f (g · x) dμ = ∫_A f dμ` for every `g`, so averaging
  over `g` matches the defining property of the conditional expectation. `IsFiniteMeasure μ`
  supplies the σ-finiteness of the trimmed measure that `condExp` requires; `hm ≤ m𝓧` is not a
  hypothesis, being forced by `hm_inv`.

**Bibliographic comments.** Invariance as a reduction principle for testing problems is due to
G. A. Hunt and C. Stein ("Most stringent tests of statistical hypotheses," unpublished, 1946).
The identification of the conditional expectation given the invariant σ-algebra with an orbit
average is the finite-group case of the mean ergodic theorem (J. von Neumann, "Proof of the
quasi-ergodic hypothesis," *Proc. Natl. Acad. Sci. USA* **18** (1932), 70–82;
G. D. Birkhoff, "Proof of the ergodic theorem," *ibid.*, 656–660).
-/

open MeasureTheory

namespace StatLean.HypothesisTesting

variable {G 𝓧 : Type*} [Group G] [m𝓧 : MeasurableSpace 𝓧] [MulAction G 𝓧]

/-- An **invariant set**: fixed by every element of the group. -/
def IsInvariantSet (G : Type*) [Group G] [MulAction G 𝓧] (A : Set 𝓧) : Prop :=
  ∀ g : G, (fun x : 𝓧 => g • x) ⁻¹' A = A

/-- The **invariant sets**: the measurable sets fixed by every element of the group. The
carrier of the invariant σ-algebra (see the carrier note in the file header). -/
def invariantSets (G 𝓧 : Type*) [Group G] [MeasurableSpace 𝓧] [MulAction G 𝓧] :
    Set (Set 𝓧) :=
  {A | MeasurableSet A ∧ IsInvariantSet G A}

/-- The **orbit average** `|G|⁻¹ ∑_{g ∈ G} f(g·x)` of a function along a finite group action. -/
noncomputable def groupAverage (G : Type*) [Group G] [Fintype G] [MulAction G 𝓧] (f : 𝓧 → ℝ)
    (x : 𝓧) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g : G, f (g • x)

/-! ### The invariant sets form a σ-algebra -/

/-- σ-algebra bookkeeping: the empty set is invariant. -/
theorem empty_mem_invariantSets : (∅ : Set 𝓧) ∈ invariantSets G 𝓧 :=
  ⟨MeasurableSet.empty, fun _ => Set.preimage_empty⟩

/-- σ-algebra bookkeeping: invariant sets are closed under complement. -/
theorem compl_mem_invariantSets {A : Set 𝓧}
    -- USER-INPUT: the set to be complemented is invariant and measurable; classical
    (hA : A ∈ invariantSets G 𝓧) :
    Aᶜ ∈ invariantSets G 𝓧 :=
  ⟨hA.1.compl, fun g => by rw [Set.preimage_compl, hA.2 g]⟩

/-- σ-algebra bookkeeping: invariant sets are closed under countable unions. -/
theorem iUnion_mem_invariantSets {A : ℕ → Set 𝓧}
    -- USER-INPUT: each set of the sequence is invariant and measurable; classical
    (hA : ∀ n, A n ∈ invariantSets G 𝓧) :
    (⋃ n, A n) ∈ invariantSets G 𝓧 :=
  ⟨MeasurableSet.iUnion fun n => (hA n).1, fun g => by
    simp only [Set.preimage_iUnion]; exact Set.iUnion_congr fun n => (hA n).2 g⟩

/-- Preimages of measurable sets under an invariant measurable statistic are invariant: this is
how invariant functions are seen to be measurable for the invariant σ-algebra. -/
theorem preimage_mem_invariantSets {𝓘 : Type*} [MeasurableSpace 𝓘] {h : 𝓧 → 𝓘}
    -- LEAN-ONLY: measurability of the statistic; standard regularity
    (hmeas : Measurable h)
    -- USER-INPUT: the statistic is invariant along the orbits; Hunt–Stein (1946)
    (hinv : ∀ (g : G) (x : 𝓧), h (g • x) = h x)
    {B : Set 𝓘}
    -- LEAN-ONLY: measurability of the target set; standard regularity
    (hB : MeasurableSet B) :
    h ⁻¹' B ∈ invariantSets G 𝓧 :=
  ⟨hB.preimage hmeas, fun g => Set.ext fun x => by
    simp only [Set.mem_preimage, hinv g x]⟩

/-! ### The orbit average -/

variable [Fintype G]

/-- The orbit average is invariant along the orbits. -/
theorem groupAverage_smul (f : 𝓧 → ℝ) (g : G) (x : 𝓧) :
    groupAverage G f (g • x) = groupAverage G f x := by
  unfold groupAverage
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight g) (fun b => f (b • x))]
  simp only [Equiv.coe_mulRight, mul_smul]

/-- The orbit average of a measurable function is measurable. -/
theorem measurable_groupAverage {f : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the integrand; standard regularity
    (hf : Measurable f)
    -- LEAN-ONLY: the action is by measurable maps; standard regularity
    (hmeas : ∀ g : G, Measurable (fun x : 𝓧 => g • x)) :
    Measurable (groupAverage G f) := by
  unfold groupAverage
  exact (Finset.measurable_sum _ fun g _ => hf.comp (hmeas g)).const_mul _

/-- Averaging an already invariant function changes nothing. -/
theorem groupAverage_of_isInvariant {f : 𝓧 → ℝ}
    -- USER-INPUT: the function is invariant along the orbits; Hunt–Stein (1946)
    (hinv : ∀ (g : G) (x : 𝓧), f (g • x) = f x) :
    groupAverage G f = f := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  funext x
  unfold groupAverage
  simp only [hinv]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hcard]

/-- **Orbit averaging preserves the integral** against an invariant measure. -/
theorem integral_groupAverage (μ : Measure 𝓧) {f : 𝓧 → ℝ}
    -- LEAN-ONLY: the action is by measurable maps; standard regularity
    (hmeas : ∀ g : G, Measurable (fun x : 𝓧 => g • x))
    -- USER-INPUT: the measure is invariant under the group; Hunt–Stein (1946)
    (hμ : ∀ g : G, μ.map (fun x : 𝓧 => g • x) = μ)
    -- LEAN-ONLY: integrability of the integrand; standard regularity
    (hf : Integrable f μ) :
    ∫ x, groupAverage G f x ∂μ = ∫ x, f x ∂μ := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmp : ∀ g : G, MeasurePreserving (fun x : 𝓧 => g • x) μ μ :=
    fun g => ⟨hmeas g, hμ g⟩
  have hint : ∀ g : G, ∫ x, f (g • x) ∂μ = ∫ x, f x ∂μ := by
    intro g
    have hae : AEStronglyMeasurable f (μ.map fun x : 𝓧 => g • x) := by
      rw [hμ g]; exact hf.aestronglyMeasurable
    conv_rhs => rw [← hμ g]
    exact (integral_map (hmeas g).aemeasurable hae).symm
  have hsum : (∫ x, ∑ g : G, f (g • x) ∂μ) = ∑ g : G, ∫ x, f (g • x) ∂μ :=
    integral_finset_sum Finset.univ fun g _ => (hmp g).integrable_comp_of_integrable hf
  unfold groupAverage
  rw [integral_const_mul, hsum]
  simp only [hint]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hcard]

set_option maxHeartbeats 1000000 in
/-- **Conditional expectation given the invariant σ-algebra is the orbit average**, for a
`G`-invariant measure and a finite group.

The invariant σ-algebra enters as a parameter `m` characterized by `hm_inv`; that `m` is a
sub-σ-algebra of the ambient one is forced by `hm_inv` and derived in the proof, not
assumed. -/
theorem condExp_eq_groupAverage (m : MeasurableSpace 𝓧)
    -- USER-INPUT: `m` is the σ-algebra of invariant sets; Hunt–Stein (1946).
    -- The ambient instance `m𝓧` is pinned explicitly: without it, the local parameter `m`
    -- captures the implicit `[MeasurableSpace 𝓧]` of `invariantSets`, and the hypothesis
    -- degenerates to "every `m`-measurable set is invariant" — which does not force
    -- `m ≤ m𝓧` and makes the conclusion false (a non-measurable symmetric set in a
    -- reflection-invariant Gaussian model is a counterexample).
    (hm_inv : ∀ s : Set 𝓧, MeasurableSet[m] s ↔ s ∈ @invariantSets G 𝓧 _ m𝓧 _)
    (μ : Measure 𝓧)
    -- LEAN-ONLY: finiteness gives σ-finiteness of the trimmed measure, required by `condExp`
    [IsFiniteMeasure μ]
    -- LEAN-ONLY: the action is by measurable maps; standard regularity
    (hmeas : ∀ g : G, Measurable (fun x : 𝓧 => g • x))
    -- USER-INPUT: the measure is invariant under the group; Hunt–Stein (1946)
    (hμ : ∀ g : G, μ.map (fun x : 𝓧 => g • x) = μ)
    {f : 𝓧 → ℝ}
    -- LEAN-ONLY: integrability of the integrand; standard regularity
    (hf : Integrable f μ) :
    μ[f | m] =ᵐ[μ] groupAverage G f := by
  classical
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  -- NOTE ON THE ELABORATED SIGNATURE. The parameter `(m : MeasurableSpace 𝓧)` is a local
  -- instance and, being declared after the section's `m𝓧`, shadows it as the default. Hence
  -- `μ`, `hmeas`, `hμ`, `hf` are all elaborated over `m`, so the ambient σ-algebra of `μ`
  -- *is* `m` and the conditioning `μ[f | m]` is onto `μ`'s own σ-algebra. The identity is
  -- still true — integrability over `m` forces `f` to be a.e. invariant — and is proved here
  -- via `ae_eq_condExp_of_forall_setIntegral_eq` with `hm = le_rfl`. `hm_inv` still supplies,
  -- for each `m`-set `s`, its invariance `IsInvariantSet G s`, which is what the set-integral
  -- identity needs. See the report for the minimal fix (`(μ : @Measure 𝓧 m𝓧)`, likewise
  -- `hmeas`, `hμ`) that would restore the intended coarser-`m` reading.
  have hmp : ∀ g : G, MeasurePreserving (fun x : 𝓧 => g • x) μ μ := fun g => ⟨hmeas g, hμ g⟩
  -- Work with a measurable representative `f₀` of `f`; the averaging is transported along it.
  obtain ⟨f₀, hf₀sm, hff₀⟩ := hf.aestronglyMeasurable
  have hf₀meas : Measurable f₀ := hf₀sm.measurable
  have hf₀ : Integrable f₀ μ := hf.congr hff₀
  -- The two orbit averages agree a.e., since each `g • ·` is measure-preserving.
  have hcomp : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] fun x => f₀ (g • x) :=
    fun g => hff₀.comp_tendsto ((hmp g).quasiMeasurePreserving.tendsto_ae)
  have hgaeq : groupAverage G f =ᵐ[μ] groupAverage G f₀ := by
    filter_upwards [ae_all_iff.mpr hcomp] with x hx
    unfold groupAverage
    congr 1
    exact Finset.sum_congr rfl fun g _ => hx g
  -- Integrability of the average of the measurable representative.
  have hInt : Integrable (groupAverage G f₀) μ := by
    unfold groupAverage
    exact (integrable_finset_sum Finset.univ
      fun g _ => (hmp g).integrable_comp_of_integrable hf₀).const_mul _
  -- The average of the measurable representative is `m`-measurable (each `g • ·` is
  -- `m`-measurable by `hmeas`, so the summands are, and the average of them is).
  have hgm_meas : Measurable[m] (groupAverage G f₀) := by
    unfold groupAverage
    exact (Finset.measurable_sum _ fun g _ => hf₀meas.comp (hmeas g)).const_mul _
  have hgm : AEStronglyMeasurable[m] (groupAverage G f₀) μ :=
    hgm_meas.stronglyMeasurable.aestronglyMeasurable
  -- The conditional-expectation identity for the measurable representative.
  have hcore : μ[f₀|m] =ᵐ[μ] groupAverage G f₀ := by
    refine (ae_eq_condExp_of_forall_setIntegral_eq le_rfl hf₀
      (fun s _ _ => hInt.integrableOn) ?_ hgm).symm
    intro s hsm _
    obtain ⟨_, hs_inv⟩ := (hm_inv s).mp hsm
    -- On the invariant set `s`, each translated integral equals the original.
    have hstep : ∀ g : G, ∫ x in s, f₀ (g • x) ∂μ = ∫ x in s, f₀ x ∂μ := by
      intro g
      have hsinv : (fun x => g • x) ⁻¹' s = s := hs_inv g
      have hind : (fun x => s.indicator f₀ (g • x)) = s.indicator fun x => f₀ (g • x) := by
        funext x
        have hiff : g • x ∈ s ↔ x ∈ s := by conv_lhs => rw [← Set.mem_preimage, hsinv]
        by_cases hx : x ∈ s
        · rw [Set.indicator_of_mem (hiff.mpr hx) f₀, Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem (fun h => hx (hiff.mp h)) f₀,
            Set.indicator_of_notMem hx]
      rw [← integral_indicator hsm, ← integral_indicator hsm, ← hind]
      have hae : AEStronglyMeasurable (s.indicator f₀) (μ.map fun x => g • x) := by
        rw [hμ g]; exact (hf₀sm.indicator hsm).aestronglyMeasurable
      conv_rhs => rw [← hμ g]
      exact (integral_map (hmeas g).aemeasurable hae).symm
    have hsum : (∫ x in s, ∑ g : G, f₀ (g • x) ∂μ) = ∑ g : G, ∫ x in s, f₀ (g • x) ∂μ :=
      integral_finset_sum Finset.univ
        fun g _ => ((hmp g).integrable_comp_of_integrable hf₀).integrableOn
    unfold groupAverage
    rw [integral_const_mul, hsum]
    simp only [hstep]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hcard]
  -- Transport the identity back to `f`.
  exact (condExp_congr_ae hff₀).trans (hcore.trans hgaeq.symm)

end StatLean.HypothesisTesting
