module
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.IsLUB

@[expose] public section

/-!
# The equivalent countable mixture of a dominated family

The measure-theoretic lemma underlying every treatment of sufficiency for dominated families:
if a family `P : Θ → Measure 𝓧` of probability measures is dominated by a σ-finite `μ`, then
some **countable** mixture `λ = ∑ᵢ cᵢ · P_{θᵢ}` of members of the family is already
*equivalent* to the whole family — every `P θ` is absolutely continuous with respect to `λ`,
and a set is `λ`-null exactly when it is `P θ`-null for every `θ`.

The point is that `λ` is built **from the family itself**, so a `λ`-density is automatically a
legitimate statistical object; densities against an arbitrary dominating `μ` are not. Every
later step — the factorization criterion, minimal sufficiency, the likelihood-ratio
construction — is run against this `λ`.

* `exists_equivalent_countable_mixture` — the existence statement.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 2 (The Probability
Background), §2.6 (Sufficient Statistics), supporting material for Theorem 2.6.2: every
dominated family admits an equivalent countable mixture. (`TSH4 Thm 2.6.2`.)

**Proof formalization notes.**
* **Route.** Reduce to a finite dominating measure (`μ` σ-finite admits an equivalent finite
  measure). Consider the collection of all countable mixtures `ν` of members of the family,
  and their densities `dν/dμ`; take a sequence `νₙ` whose supports `{dνₙ/dμ > 0}` have
  `μ`-measure converging to the supremum of that quantity over the collection, and let `λ` be
  a strictly positive countable mixture of the `νₙ`. Maximality of the support of `dλ/dμ`
  forces `P θ ≪ λ` for every `θ`: otherwise `P θ` would charge a `λ`-null set and the mixture
  `(λ + P θ)/2` would have strictly larger support, contradicting the supremum.
* **Weights.** `c : ℕ → ℝ≥0∞` is required strictly positive and to sum to `1`, so `λ` is a
  probability measure; the index type is `ℕ` throughout, and `[Nonempty Θ]` lets a genuinely
  finite selection be padded by repetition (repeating an index only merges into a larger
  weight for the same member, which changes neither the null sets nor absolute continuity).
* **The null-set equivalence is stated for an ARBITRARY set `A`,** with no `MeasurableSet`
  hypothesis. This is safe *and* strictly stronger at this pin: `Measure.sum_apply_eq_zero`
  holds for a countable index without measurability, and `Measure.AbsolutelyContinuous` is
  itself defined by an implication between outer-measure values of arbitrary sets. Callers
  that only have a measurable set lose nothing.
* Domination is phrased as `∀ θ, P θ ≪ μ` with `μ` an explicit σ-finite argument rather than
  packaged into a structure, so that the lemma applies verbatim to families dominated by a
  measure produced elsewhere in a proof.

**Bibliographic comments.** The lemma and the equivalent-mixture device are due to
P. R. Halmos and L. J. Savage ("Application of the Radon–Nikodym theorem to the theory of
sufficient statistics," *Ann. Math. Statist.* **20** (1949), 225–241), where they are used to
prove the factorization criterion for dominated families.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

/-- **Halmos–Savage equivalent-mixture lemma.** A family of probability measures dominated by
a σ-finite measure admits an equivalent countable mixture of its own members: there are
indices `θs : ℕ → Θ` and strictly positive weights `c` summing to `1` such that the mixture
`λ = ∑ᵢ cᵢ · P (θs i)` dominates every member of the family and has exactly the common null
sets of the family. -/
theorem exists_equivalent_countable_mixture {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]
    -- LEAN-ONLY: the index type is inhabited; needed to pad a finite selection by repetition
    -- into a genuine `ℕ`-indexed sequence. No scope change: an empty family is vacuous.
    [Nonempty Θ]
    -- USER-INPUT: the statistical model; genuine external data
    (P : Θ → Measure 𝓧)
    -- USER-INPUT: each member is a probability measure; part of "statistical model"
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: a dominating measure; free choice of reference measure
    (μ : Measure 𝓧)
    -- USER-INPUT: σ-finiteness of the reference measure; the standing regularity of the
    -- dominated-family setting, and false without it (the lemma fails for wild `μ`)
    [SigmaFinite μ]
    -- USER-INPUT: the family is dominated by `μ`; the definition of "dominated family"
    (hdom : ∀ θ, P θ ≪ μ) :
    ∃ (θs : ℕ → Θ) (c : ℕ → ℝ≥0∞) (lam : Measure 𝓧),
      lam = Measure.sum (fun i => c i • P (θs i)) ∧
      (∀ i, 0 < c i) ∧ (∑' i, c i) = 1 ∧
      (∀ θ, P θ ≪ lam) ∧
      ∀ A : Set 𝓧, (∀ θ, P θ A = 0) ↔ lam A = 0 := by
  -- Reduce to a finite reference measure equivalent to `μ`.
  obtain ⟨ν₀, hν₀fin, hμν₀, -⟩ := exists_isFiniteMeasure_absolutelyContinuous μ
  haveI : IsFiniteMeasure ν₀ := hν₀fin
  have hPν₀ : ∀ θ, P θ ≪ ν₀ := fun θ => (hdom θ).trans hμν₀
  -- The `ν₀`-support of each member, via its Radon–Nikodym derivative.
  set supp : Θ → Set 𝓧 := fun θ => {x | (P θ).rnDeriv ν₀ x ≠ 0} with hsupp
  have hsupp_meas : ∀ θ, MeasurableSet (supp θ) := fun θ =>
    (Measure.measurable_rnDeriv (P θ) ν₀ (measurableSet_singleton 0)).compl
  -- `P θ A = 0` is detected by the `ν₀`-measure of `A ∩ supp θ`.
  have hchar : ∀ θ (A : Set 𝓧), MeasurableSet A →
      ((P θ) A = 0 ↔ ν₀ (A ∩ supp θ) = 0) := by
    intro θ A hA
    have hPA : (P θ) A = ∫⁻ x in A, (P θ).rnDeriv ν₀ x ∂ν₀ := by
      conv_lhs => rw [← Measure.withDensity_rnDeriv_eq (P θ) ν₀ (hPν₀ θ), withDensity_apply _ hA]
    have hset : {x : 𝓧 | ¬(x ∈ A → (P θ).rnDeriv ν₀ x = 0)} = A ∩ supp θ := by
      rw [hsupp]; ext x
      simp only [Set.mem_setOf_eq, Classical.not_imp, Set.mem_inter_iff, ne_eq]
    rw [hPA, setLIntegral_eq_zero_iff hA (Measure.measurable_rnDeriv _ _), ae_iff]
    exact iff_of_eq (by rw [hset])
  -- Maximise the `ν₀`-measure of the support-union over countable subfamilies.
  have hSne : (Set.range (fun J : ℕ → Θ => ν₀ (⋃ i, supp (J i)))).Nonempty :=
    Set.range_nonempty _
  have hSbdd : BddAbove (Set.range (fun J : ℕ → Θ => ν₀ (⋃ i, supp (J i)))) := by
    refine ⟨ν₀ Set.univ, ?_⟩
    rintro x ⟨J, rfl⟩
    exact measure_mono (Set.subset_univ _)
  obtain ⟨u, -, hu_tend, hu_mem⟩ := exists_seq_tendsto_sSup hSne hSbdd
  set Jseq : ℕ → ℕ → Θ := fun n => (hu_mem n).choose with hJseq
  have hJval : ∀ n, ν₀ (⋃ i, supp (Jseq n i)) = u n := fun n => (hu_mem n).choose_spec
  -- Merge all the `Jseq n` into a single sequence via `Nat.unpair`.
  set θs : ℕ → Θ := fun k => Jseq (Nat.unpair k).1 (Nat.unpair k).2 with hθs
  set U : Set 𝓧 := ⋃ i, supp (θs i) with hU
  have hU_meas : MeasurableSet U := by
    rw [hU]; exact MeasurableSet.iUnion fun k => hsupp_meas (θs k)
  have hUsup : ∀ n, (⋃ i, supp (Jseq n i)) ⊆ U := by
    intro n
    rw [hU]
    refine Set.iUnion_subset fun i => ?_
    refine Set.subset_iUnion_of_subset (Nat.pair n i) (le_of_eq ?_)
    show supp (Jseq n i) = supp (θs (Nat.pair n i))
    rw [show θs (Nat.pair n i) = Jseq n i by simp only [hθs, Nat.unpair_pair]]
  have hval_le : ∀ n, u n ≤ ν₀ U := fun n => hJval n ▸ measure_mono (hUsup n)
  have hβle : sSup (Set.range (fun J : ℕ → Θ => ν₀ (⋃ i, supp (J i)))) ≤ ν₀ U :=
    le_of_tendsto hu_tend (Filter.Eventually.of_forall hval_le)
  -- Maximality: every member's support is `ν₀`-essentially inside `U`.
  have hmax : ∀ θ, ν₀ (supp θ \ U) = 0 := by
    intro θ
    set θs' : ℕ → Θ := fun k => Nat.casesOn k θ θs with hθs'
    have hU' : (⋃ k, supp (θs' k)) = supp θ ∪ U := by
      rw [hU]; ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨k, hk⟩
        cases k with
        | zero => exact Or.inl hk
        | succ n => exact Or.inr ⟨n, hk⟩
      · rintro (hx | ⟨n, hn⟩)
        · exact ⟨0, hx⟩
        · exact ⟨n + 1, hn⟩
    have hmem' : ν₀ (supp θ ∪ U) ∈
        Set.range (fun J : ℕ → Θ => ν₀ (⋃ i, supp (J i))) :=
      ⟨θs', by change ν₀ (⋃ i, supp (θs' i)) = ν₀ (supp θ ∪ U); rw [hU']⟩
    have hle1 : ν₀ (supp θ ∪ U) ≤ ν₀ U := (le_csSup hSbdd hmem').trans hβle
    have hge : ν₀ U ≤ ν₀ (supp θ ∪ U) := measure_mono Set.subset_union_right
    have heq : ν₀ (supp θ ∪ U) = ν₀ U := le_antisymm hle1 hge
    have hkey : ν₀ (supp θ ∪ U) = ν₀ U + ν₀ (supp θ \ U) := by
      rw [Set.union_comm (supp θ) U, ← Set.union_diff_self,
          measure_union disjoint_sdiff_self_right ((hsupp_meas θ).diff hU_meas)]
    have hcancel : ν₀ U + 0 = ν₀ U + ν₀ (supp θ \ U) := by
      rw [add_zero]; exact heq.symm.trans hkey
    exact ((ENNReal.add_right_inj (measure_ne_top ν₀ U)).mp hcancel).symm
  -- Weights, and the mixture.
  set c : ℕ → ℝ≥0∞ := fun i => 2⁻¹ ^ (i + 1) with hc
  have hc_pos : ∀ i, 0 < c i := fun i =>
    ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) (i + 1)
  have hc_sum : (∑' i, c i) = 1 := by
    simp only [hc]
    rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv,
        ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  -- Domination of every member by the mixture.
  have hdom_lam : ∀ θ, P θ ≪ Measure.sum (fun i => c i • P (θs i)) := by
    intro θ
    refine Measure.AbsolutelyContinuous.mk (fun A hA hlamA => ?_)
    have hzero : ∀ i, (P (θs i)) A = 0 := by
      intro i
      have hi := (Measure.sum_apply_eq_zero.mp hlamA) i
      rw [Measure.smul_apply, smul_eq_mul] at hi
      exact (mul_eq_zero.mp hi).resolve_left (hc_pos i).ne'
    have hAU : ν₀ (A ∩ U) = 0 := by
      rw [hU, Set.inter_iUnion]
      exact measure_iUnion_null fun i => (hchar (θs i) A hA).mp (hzero i)
    have hAsupp : ν₀ (A ∩ supp θ) = 0 := by
      have hsub : A ∩ supp θ ⊆ (A ∩ U) ∪ (supp θ \ U) := by
        rintro x ⟨hxA, hxs⟩
        by_cases hxU : x ∈ U
        · exact Or.inl ⟨hxA, hxU⟩
        · exact Or.inr ⟨hxs, hxU⟩
      refine le_antisymm ?_ (zero_le)
      calc ν₀ (A ∩ supp θ) ≤ ν₀ ((A ∩ U) ∪ (supp θ \ U)) := measure_mono hsub
        _ ≤ ν₀ (A ∩ U) + ν₀ (supp θ \ U) := measure_union_le _ _
        _ = 0 := by rw [hAU, hmax θ, add_zero]
    exact (hchar θ A hA).mpr hAsupp
  -- The null-set equivalence, for an arbitrary set.
  have hiff : ∀ A : Set 𝓧,
      (∀ θ, (P θ) A = 0) ↔ Measure.sum (fun i => c i • P (θs i)) A = 0 := by
    intro A
    constructor
    · intro hall
      rw [Measure.sum_apply_eq_zero]
      intro i
      rw [Measure.smul_apply, smul_eq_mul, hall (θs i), mul_zero]
    · intro h0 θ
      exact hdom_lam θ h0
  exact ⟨θs, c, Measure.sum (fun i => c i • P (θs i)), rfl, hc_pos, hc_sum, hdom_lam, hiff⟩

end StatLean.PointEstimation
