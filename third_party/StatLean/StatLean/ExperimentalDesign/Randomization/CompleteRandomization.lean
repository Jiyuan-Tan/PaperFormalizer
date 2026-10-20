module
public import Mathlib.GroupTheory.Perm.Basic
public import StatLean.ExperimentalDesign.Core.Design
public import StatLean.ExperimentalDesign.ForMathlib.PMFExpectation

@[expose] public section

/-!
# The completely randomised design

Fix a replication pattern `r : T → ℕ` with `∑ₜ r t = N = |U|`.  The **completely
randomised design** draws an allocation uniformly at random from the allocations whose
arm sizes are exactly `r`:
$$\mathcal A_r = \{a : U → T \mid |\{i : a(i) = t\}| = r_t \ \forall t\}, \qquad
  D_r = \operatorname{Uniform}(\mathcal A_r).$$
This file constructs `D_r` and proves the exact first- and second-order assignment
probabilities of randomisation theory:
$$P(A_i = t) = \frac{r_t}{N}, \qquad
  P(A_i = t, A_j = t) = \frac{r_t (r_t - 1)}{N (N-1)}, \qquad
  P(A_i = t, A_j = s) = \frac{r_t\, r_s}{N (N-1)} \quad (s \ne t),$$
for distinct units `i ≠ j`, together with the indicator variance
`r_t (N − r_t) / N²` and the negative indicator covariance
`− r_t (N − r_t) / (N² (N−1))`.  These are the atomic ingredients of every exact
randomisation-based moment (arm means, randomization tests, Neyman-style causal
variance formulas).

## Main results

* `validAllocations`, `validAllocations_nonempty`, `completeRandomization` — the
  design.
* `mem_support_completeRandomization`, `card_arm_of_mem_validAllocations` — support.
* `completeRandomization_map_precomp` — permutation invariance (the randomisation
  symmetry).
* `expect_armIndicator` — first-order assignment probability `r_t / N`.
* `expect_armIndicator_pair_same`, `expect_armIndicator_pair_distinct` — second-order
  assignment probabilities.
* `var_armIndicator`, `cov_armIndicator_of_ne` — indicator variance and covariance.

**Reference.** R. Mead, *The Design of Experiments*, Cambridge University Press,
1988: the completely randomised design with replications `n₁, …, n_t`, §6.2; the
requirement that each unit be equally likely to receive each treatment and the
allocation probabilities `n_A/∑n, …, n_T/∑n`, §9.2 and §9.6; the indicator moment
calculus (`E δ`, `E δδ'` patterns), §9.4.  (`Mead §6.2`, `Mead §9.2`, `Mead §9.4`,
`Mead §9.6`.)

**Proof formalization notes.**
* Intended proof route for the moments — *symmetry, not counting*.  No cardinality of
  `𝒜_r` is ever computed:
  1. `completeRandomization_map_precomp`: precomposition with a permutation `σ` of the
     units is a bijection of `𝒜_r` (arms pull back along `σ`, preserving their sizes),
     and the pushforward of a uniform law under a bijection preserving its support
     finset is itself.
  2. Marginals: by (1) with a transposition, `E[χ_{t,i}]` is the same for all units
     `i`; summing `card_arm_eq_sum_indicator` over the support gives
     `∑_i E[χ_{t,i}] = r_t`, hence each equals `r_t / N`.
  3. Pairs: for fixed `i`, transpositions fixing `i` show `E[χ_{t,i} χ_{t,j}]` is the
     same for all `j ≠ i`; then
     `(N−1) E[χ_{t,i} χ_{t,j}] = E[χ_{t,i} (∑_{j ≠ i} χ_{t,j})]
        = E[χ_{t,i} (r_t − χ_{t,i})] = (r_t − 1) r_t / N`
     using idempotency of indicators on the support.  The distinct-treatment case is
     the same computation with `E[χ_{t,i} χ_{s,i}] = 0` (exclusivity).
* Degenerate denominators are vacuous: a hypothesis `i ≠ j` forces `N ≥ 2`, and a
  unit argument `i : U` forces `N ≥ 1`, so the real-division formulas never actually
  divide by zero.
* The variance/covariance forms follow from the pair probabilities by pure algebra
  via `pmfVar_eq_expect_sq_sub_sq` / `pmfCov_eq_expect_mul_sub_mul`.
-/

open scoped ENNReal

namespace StatLean.ExperimentalDesign

variable {U T : Type*} [Fintype U] [DecidableEq U] [Fintype T] [DecidableEq T]

/-- The **valid allocations** of the replication pattern `r`: allocations whose arm
sizes are exactly `r` (`Mead §6.2`). -/
def validAllocations (r : T → ℕ) : Finset (Allocation U T) :=
  Finset.univ.filter fun a => ∀ t, (arm t a).card = r t

theorem mem_validAllocations {r : T → ℕ} {a : Allocation U T} :
    a ∈ validAllocations (U := U) r ↔ ∀ t, (arm t a).card = r t := by
  simp [validAllocations]

/-- Existence of an allocation with prescribed fibre sizes, in the form needed for the
induction: over a finset `s` of treatments and a finset `V` of available units whose
sizes match, one can assign each unit of `V` a treatment from `s` realising the fibre
sizes `r`.  Units outside `V` receive an arbitrary treatment. -/
private theorem exists_allocation_aux [Nonempty T] (r : T → ℕ) :
    ∀ (s : Finset T) (V : Finset U), ∑ t ∈ s, r t = V.card →
      ∃ f : U → T, (∀ i ∈ V, f i ∈ s) ∧
        ∀ t ∈ s, (V.filter fun i => f i = t).card = r t := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro V hV
      rw [Finset.sum_empty] at hV
      have hVe : V = ∅ := Finset.card_eq_zero.mp hV.symm
      refine ⟨fun _ => Classical.arbitrary T, ?_, ?_⟩
      · intro i hi
        rw [hVe] at hi
        exact absurd hi (Finset.notMem_empty i)
      · intro t ht
        exact absurd ht (Finset.notMem_empty t)
  | insert t₀ s' ht₀ ih =>
      intro V hV
      rw [Finset.sum_insert ht₀] at hV
      have hle : r t₀ ≤ V.card := by omega
      obtain ⟨W, hWV, hWcard⟩ := Finset.exists_subset_card_eq hle
      have hVW : ∑ t ∈ s', r t = (V \ W).card := by
        rw [Finset.card_sdiff_of_subset hWV, hWcard]; omega
      obtain ⟨f', hf'mem, hf'card⟩ := ih (V \ W) hVW
      refine ⟨fun i => if i ∈ W then t₀ else f' i, ?_, ?_⟩
      · intro i hi
        by_cases hiW : i ∈ W
        · simp [hiW]
        · simp only [hiW, if_false]
          exact Finset.mem_insert_of_mem (hf'mem i (Finset.mem_sdiff.mpr ⟨hi, hiW⟩))
      · intro t ht
        rcases Finset.mem_insert.mp ht with heq | hts'
        · rw [heq]
          have hfil : (V.filter fun i => (if i ∈ W then t₀ else f' i) = t₀) = W := by
            ext i
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hiV, hi⟩
              by_contra hiW
              rw [if_neg hiW] at hi
              exact ht₀ (hi ▸ hf'mem i (Finset.mem_sdiff.mpr ⟨hiV, hiW⟩))
            · intro hiW
              exact ⟨hWV hiW, by rw [if_pos hiW]⟩
          rw [hfil, hWcard]
        · have hne : t ≠ t₀ := fun h => ht₀ (h ▸ hts')
          have hfil : (V.filter fun i => (if i ∈ W then t₀ else f' i) = t)
              = (V \ W).filter fun i => f' i = t := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            constructor
            · rintro ⟨hiV, hi⟩
              by_cases hiW : i ∈ W
              · rw [if_pos hiW] at hi
                exact absurd hi.symm hne
              · rw [if_neg hiW] at hi
                exact ⟨⟨hiV, hiW⟩, hi⟩
            · rintro ⟨⟨hiV, hiW⟩, hi⟩
              exact ⟨hiV, by rw [if_neg hiW]; exact hi⟩
          rw [hfil]
          exact hf'card t hts'

/-- A replication pattern summing to the population size admits a valid allocation. -/
theorem validAllocations_nonempty (r : T → ℕ)
    -- USER-INPUT: the replications exhaust the units; Mead §6.2
    (hr : ∑ t, r t = Fintype.card U) :
    (validAllocations (U := U) r).Nonempty := by
  rcases isEmpty_or_nonempty T with hT | hT
  · haveI := hT
    have hU : Fintype.card U = 0 := by
      rw [← hr]; simp
    haveI : IsEmpty U := Fintype.card_eq_zero_iff.mp hU
    refine ⟨fun i => isEmptyElim i, ?_⟩
    rw [mem_validAllocations]
    exact fun t => isEmptyElim t
  · haveI := hT
    obtain ⟨f, -, hf⟩ :=
      exists_allocation_aux (U := U) r Finset.univ Finset.univ
        (by rw [Finset.card_univ]; exact hr)
    refine ⟨f, ?_⟩
    rw [mem_validAllocations]
    intro t
    exact hf t (Finset.mem_univ t)

/-- The **completely randomised design** with replication pattern `r`: the uniform
distribution on the valid allocations (`Mead §6.2`, `Mead §9.2`). -/
noncomputable def completeRandomization (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) : RandomizationDesign U T :=
  PMF.uniformOfFinset (validAllocations r) (validAllocations_nonempty r hr)

theorem mem_support_completeRandomization {r : T → ℕ}
    {hr : ∑ t, r t = Fintype.card U} {a : Allocation U T} :
    a ∈ (completeRandomization r hr).support ↔ ∀ t, (arm t a).card = r t :=
  (PMF.mem_support_uniformOfFinset_iff _ a).trans mem_validAllocations

/-- On the support of the design, arm sizes are the prescribed replications. -/
theorem card_arm_of_mem_validAllocations {r : T → ℕ} {a : Allocation U T}
    (ha : a ∈ validAllocations (U := U) r) (t : T) :
    (arm t a).card = r t :=
  mem_validAllocations.mp ha t

/-- Every replication is at most the population size. -/
theorem replication_le_card (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) (t : T) :
    r t ≤ Fintype.card U := by
  rw [← hr]
  exact Finset.single_le_sum (f := r) (fun i _ => Nat.zero_le (r i)) (Finset.mem_univ t)

/-! ### Permutation symmetry of the support

Precomposition with a permutation `σ` of the units pulls arms back along `σ`, hence
preserves arm sizes and so acts on `validAllocations r`.  This is ingredient (B) of the
moment calculus: every sum over the support is invariant under it. -/

/-- Arms pull back along a relabelling of the units. -/
private theorem arm_precomp (t : T) (a : Allocation U T) (σ : Equiv.Perm U) :
    arm t (fun i => a (σ i)) = Finset.image σ.symm (arm t a) := by
  ext i
  simp only [mem_arm_iff, Finset.mem_image]
  constructor
  · exact fun h => ⟨σ i, h, σ.symm_apply_apply i⟩
  · rintro ⟨j, hj, rfl⟩
    simpa using hj

/-- Relabelling the units preserves arm sizes. -/
private theorem card_arm_precomp (t : T) (a : Allocation U T) (σ : Equiv.Perm U) :
    (arm t (fun i => a (σ i))).card = (arm t a).card := by
  rw [arm_precomp, Finset.card_image_of_injective _ σ.symm.injective]

/-- Relabelling the units acts on the valid allocations. -/
private theorem precomp_mem_validAllocations {r : T → ℕ} {a : Allocation U T}
    (ha : a ∈ validAllocations (U := U) r) (σ : Equiv.Perm U) :
    (fun i => a (σ i)) ∈ validAllocations (U := U) r := by
  rw [mem_validAllocations]
  intro t
  rw [card_arm_precomp]
  exact card_arm_of_mem_validAllocations ha t

/-- Membership in the valid allocations is invariant under relabelling. -/
private theorem precomp_mem_validAllocations_iff {r : T → ℕ} (a : Allocation U T)
    (σ : Equiv.Perm U) :
    (fun i => a (σ i)) ∈ validAllocations (U := U) r ↔ a ∈ validAllocations (U := U) r := by
  refine ⟨fun h => ?_, fun h => precomp_mem_validAllocations h σ⟩
  simpa using precomp_mem_validAllocations h σ.symm

/-- **Reindexing a sum over the support by a permutation of the units** — ingredient (B)
of the symmetry route. -/
private theorem sum_validAllocations_precomp (r : T → ℕ) (σ : Equiv.Perm U)
    (g : Allocation U T → ℝ) :
    ∑ a ∈ validAllocations (U := U) r, g a
      = ∑ a ∈ validAllocations (U := U) r, g (fun i => a (σ i)) := by
  refine Finset.sum_nbij' (i := fun a => fun i => a (σ.symm i))
    (j := fun a => fun i => a (σ i)) ?_ ?_ ?_ ?_ ?_
  · exact fun a ha => precomp_mem_validAllocations ha σ.symm
  · exact fun a ha => precomp_mem_validAllocations ha σ
  · intro a _; funext i; simp
  · intro a _; funext i; simp
  · intro a _; simp

/-- The assignment indicator transported along a relabelling. -/
private theorem armIndicator_precomp (t : T) (i : U) (a : Allocation U T) (σ : Equiv.Perm U) :
    armIndicator t i (fun k => a (σ k)) = armIndicator t (σ i) a := rfl

/-- **Randomisation symmetry**: the completely randomised design is invariant under
relabelling the units by any permutation (`Mead §9.2`: every unit is treated
symmetrically by the random allocation). -/
theorem completeRandomization_map_precomp (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) (σ : Equiv.Perm U) :
    (completeRandomization r hr).map (fun a => fun i => a (σ i))
      = completeRandomization r hr := by
  ext b
  rw [PMF.map_apply, tsum_eq_single (fun i => b (σ.symm i))]
  · have hb : (fun i => (fun k => b (σ.symm k)) (σ i)) = b := by
      funext i; simp
    rw [if_pos hb.symm]
    simp only [completeRandomization]
    by_cases hmem : b ∈ validAllocations (U := U) r
    · rw [PMF.uniformOfFinset_apply_of_mem _ hmem,
        PMF.uniformOfFinset_apply_of_mem _
          ((precomp_mem_validAllocations_iff (r := r) b σ.symm).mpr hmem)]
    · rw [PMF.uniformOfFinset_apply_of_notMem _ hmem,
        PMF.uniformOfFinset_apply_of_notMem _
          (fun h => hmem ((precomp_mem_validAllocations_iff (r := r) b σ.symm).mp h))]
  · intro a ha
    refine if_neg fun h => ha ?_
    subst h
    funext i
    simp

/-! ### The moment calculus

Every expectation below is the support average `(|𝒜_r|)⁻¹ ∑_{a ∈ 𝒜_r}` of
`pmfExpect_uniformOfFinset`; the sums are evaluated by the permutation symmetry (B)
together with the arm-size identity (C) `∑_i χ_{t,i}(a) = r_t` on the support. -/

/-- Ingredient (A): the design expectation is the average over the valid allocations. -/
private theorem expect_completeRandomization (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) (f : Allocation U T → ℝ) :
    pmfExpect (completeRandomization r hr) f
      = ((validAllocations (U := U) r).card : ℝ)⁻¹
          * ∑ a ∈ validAllocations (U := U) r, f a :=
  pmfExpect_uniformOfFinset _ _ f

/-- The support of a completely randomised design is nonempty, so its cardinality is
an invertible real. -/
private theorem card_validAllocations_ne_zero (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) :
    ((validAllocations (U := U) r).card : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Finset.card_pos.mpr (validAllocations_nonempty r hr)).ne'

/-- Ingredient (C): on the support, the assignment indicators of treatment `t` sum to
the replication `r t`. -/
private theorem sum_armIndicator_of_mem {r : T → ℕ} {a : Allocation U T}
    (ha : a ∈ validAllocations (U := U) r) (t : T) :
    ∑ i : U, armIndicator t i a = (r t : ℝ) := by
  rw [← card_arm_eq_sum_indicator, card_arm_of_mem_validAllocations ha]

/-- The support sum of a single assignment indicator does not depend on the unit. -/
private theorem sum_armIndicator_const (r : T → ℕ) (t : T) (i j : U) :
    ∑ a ∈ validAllocations (U := U) r, armIndicator t i a
      = ∑ a ∈ validAllocations (U := U) r, armIndicator t j a := by
  refine (sum_validAllocations_precomp r (Equiv.swap i j) (armIndicator t i)).trans ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [armIndicator_precomp, Equiv.swap_apply_left]

/-- The marginal support sum, in cleared-denominator form:
`N · ∑_{a} χ_{t,i}(a) = |𝒜_r| · r_t`. -/
private theorem card_mul_sum_armIndicator (r : T → ℕ) (t : T) (i : U) :
    (Fintype.card U : ℝ) * ∑ a ∈ validAllocations (U := U) r, armIndicator t i a
      = ((validAllocations (U := U) r).card : ℝ) * (r t : ℝ) := by
  have key : ∑ _j : U, ∑ a ∈ validAllocations (U := U) r, armIndicator t i a
      = ((validAllocations (U := U) r).card : ℝ) * (r t : ℝ) := by
    rw [Finset.sum_congr rfl fun j (_ : j ∈ (Finset.univ : Finset U)) =>
      sum_armIndicator_const r t i j, Finset.sum_comm,
      Finset.sum_congr rfl fun a ha => sum_armIndicator_of_mem ha t,
      Finset.sum_const, nsmul_eq_mul]
  rw [← key, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- **First-order assignment probability**: each unit receives treatment `t` with
probability `r_t / N` (`Mead §9.6`, allocation probabilities `n_A/∑n`). -/
theorem expect_armIndicator (r : T → ℕ) (hr : ∑ t, r t = Fintype.card U)
    (i : U) (t : T) :
    pmfExpect (completeRandomization r hr) (armIndicator t i)
      = (r t : ℝ) / (Fintype.card U : ℝ) := by
  haveI : Nonempty U := ⟨i⟩
  have hN : (Fintype.card U : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hK := card_validAllocations_ne_zero (U := U) r hr
  have key := card_mul_sum_armIndicator r t i
  rw [expect_completeRandomization]
  field_simp
  linarith [key]

/-- The support sum of a product of two assignment indicators does not depend on the
second unit, as long as it stays distinct from the first. -/
private theorem sum_pair_const (r : T → ℕ) (t s : T) (i : U) {j j' : U}
    (hj : j ≠ i) (hj' : j' ≠ i) :
    ∑ a ∈ validAllocations (U := U) r, armIndicator t i a * armIndicator s j a
      = ∑ a ∈ validAllocations (U := U) r, armIndicator t i a * armIndicator s j' a := by
  refine (sum_validAllocations_precomp r (Equiv.swap j j')
    (fun a => armIndicator t i a * armIndicator s j a)).trans ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [armIndicator_precomp, Equiv.swap_apply_of_ne_of_ne hj.symm hj'.symm,
    Equiv.swap_apply_left]

/-- Summing the pair sums over the second unit collapses by ingredient (C). -/
private theorem sum_pair_erase (r : T → ℕ) (t s : T) (i : U) :
    ∑ j ∈ Finset.univ.erase i,
        (∑ a ∈ validAllocations (U := U) r, armIndicator t i a * armIndicator s j a)
      = ∑ a ∈ validAllocations (U := U) r,
          armIndicator t i a * ((r s : ℝ) - armIndicator s i a) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ i),
    sum_armIndicator_of_mem ha s]

/-- The same sum, evaluated by constancy: `N − 1` equal terms. -/
private theorem sum_pair_card_erase (r : T → ℕ) (t s : T) (i : U) {j : U} (hj : j ≠ i) :
    ∑ j' ∈ Finset.univ.erase i,
        (∑ a ∈ validAllocations (U := U) r, armIndicator t i a * armIndicator s j' a)
      = ((Fintype.card U : ℝ) - 1)
          * ∑ a ∈ validAllocations (U := U) r, armIndicator t i a * armIndicator s j a := by
  have hc : ∀ j' ∈ Finset.univ.erase i,
      (∑ a ∈ validAllocations (U := U) r, armIndicator t i a * armIndicator s j' a)
        = ∑ a ∈ validAllocations (U := U) r, armIndicator t i a * armIndicator s j a :=
    fun j' hj' => sum_pair_const r t s i (Finset.ne_of_mem_erase hj') hj
  have h1 : 1 ≤ Fintype.card U := Fintype.card_pos_iff.mpr ⟨i⟩
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Nat.cast_sub h1, Nat.cast_one]

/-- **Second-order assignment probability, same treatment**: distinct units both
receive `t` with probability `r_t (r_t − 1) / (N (N−1))` (`Mead §9.4`, the
`E[δ δ']` pattern). -/
theorem expect_armIndicator_pair_same (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) {i j : U}
    -- LEAN-ONLY: distinct units; the same-unit case is the idempotency identity
    (hij : i ≠ j) (t : T) :
    pmfExpect (completeRandomization r hr)
        (fun a => armIndicator t i a * armIndicator t j a)
      = (r t : ℝ) * ((r t : ℝ) - 1)
          / ((Fintype.card U : ℝ) * ((Fintype.card U : ℝ) - 1)) := by
  haveI : Nonempty U := ⟨i⟩
  have h2 : 2 ≤ Fintype.card U := Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩
  have hN : (Fintype.card U : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hN1 : (Fintype.card U : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast h2
    linarith
  have hK := card_validAllocations_ne_zero (U := U) r hr
  have hmarg := card_mul_sum_armIndicator r t i
  have hrhs : ∑ a ∈ validAllocations (U := U) r,
        armIndicator t i a * ((r t : ℝ) - armIndicator t i a)
      = ((r t : ℝ) - 1) * ∑ a ∈ validAllocations (U := U) r, armIndicator t i a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_sub, armIndicator_mul_self]
    ring
  have herase := sum_pair_erase r t t i
  rw [sum_pair_card_erase r t t i hij.symm, hrhs] at herase
  have hkey : ((Fintype.card U : ℝ) * ((Fintype.card U : ℝ) - 1))
        * ∑ a ∈ validAllocations (U := U) r, armIndicator t i a * armIndicator t j a
      = ((validAllocations (U := U) r).card : ℝ) * ((r t : ℝ) * ((r t : ℝ) - 1)) := by
    linear_combination (Fintype.card U : ℝ) * herase + ((r t : ℝ) - 1) * hmarg
  rw [expect_completeRandomization]
  field_simp
  linarith [hkey]

/-- **Second-order assignment probability, distinct treatments**: distinct units
receive `t` and `s ≠ t` with probability `r_t r_s / (N (N−1))` (`Mead §9.4`). -/
theorem expect_armIndicator_pair_distinct (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) {i j : U}
    -- LEAN-ONLY: distinct units; same-unit exclusivity gives probability zero
    (hij : i ≠ j) {t s : T}
    -- LEAN-ONLY: distinct treatments; the same-treatment case is the lemma above
    (hts : t ≠ s) :
    pmfExpect (completeRandomization r hr)
        (fun a => armIndicator t i a * armIndicator s j a)
      = (r t : ℝ) * (r s : ℝ)
          / ((Fintype.card U : ℝ) * ((Fintype.card U : ℝ) - 1)) := by
  haveI : Nonempty U := ⟨i⟩
  have h2 : 2 ≤ Fintype.card U := Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩
  have hN : (Fintype.card U : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hN1 : (Fintype.card U : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast h2
    linarith
  have hK := card_validAllocations_ne_zero (U := U) r hr
  have hmarg := card_mul_sum_armIndicator r t i
  have hrhs : ∑ a ∈ validAllocations (U := U) r,
        armIndicator t i a * ((r s : ℝ) - armIndicator s i a)
      = (r s : ℝ) * ∑ a ∈ validAllocations (U := U) r, armIndicator t i a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_sub, armIndicator_mul_armIndicator_of_ne hts i a]
    ring
  have herase := sum_pair_erase r t s i
  rw [sum_pair_card_erase r t s i hij.symm, hrhs] at herase
  have hkey : ((Fintype.card U : ℝ) * ((Fintype.card U : ℝ) - 1))
        * ∑ a ∈ validAllocations (U := U) r, armIndicator t i a * armIndicator s j a
      = ((validAllocations (U := U) r).card : ℝ) * ((r t : ℝ) * (r s : ℝ)) := by
    linear_combination (Fintype.card U : ℝ) * herase + (r s : ℝ) * hmarg
  rw [expect_completeRandomization]
  field_simp
  linarith [hkey]

/-- **Indicator variance**: `Var(χ_{t,i}) = r_t (N − r_t) / N²` — the Bernoulli
variance of the assignment (`Mead §9.4`). -/
theorem var_armIndicator (r : T → ℕ) (hr : ∑ t, r t = Fintype.card U)
    (i : U) (t : T) :
    pmfVar (completeRandomization r hr) (armIndicator t i)
      = (r t : ℝ) * ((Fintype.card U : ℝ) - (r t : ℝ)) / (Fintype.card U : ℝ) ^ 2 := by
  haveI : Nonempty U := ⟨i⟩
  have hN : (Fintype.card U : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsq : (fun a => armIndicator t i a ^ 2) = armIndicator t i := by
    funext a
    rw [sq, armIndicator_mul_self]
  rw [pmfVar_eq_expect_sq_sub_sq, hsq, expect_armIndicator]
  field_simp

/-- **Negative indicator covariance across units**:
`Cov(χ_{t,i}, χ_{t,j}) = − r_t (N − r_t) / (N² (N−1))` for `i ≠ j` — the fixed arm
sizes make assignments negatively dependent (`Mead §9.4`). -/
theorem cov_armIndicator_of_ne (r : T → ℕ) (hr : ∑ t, r t = Fintype.card U)
    {i j : U}
    -- LEAN-ONLY: distinct units; the same-unit case is `var_armIndicator`
    (hij : i ≠ j) (t : T) :
    pmfCov (completeRandomization r hr) (armIndicator t i) (armIndicator t j)
      = -((r t : ℝ) * ((Fintype.card U : ℝ) - (r t : ℝ)))
          / ((Fintype.card U : ℝ) ^ 2 * ((Fintype.card U : ℝ) - 1)) := by
  haveI : Nonempty U := ⟨i⟩
  have h2 : 2 ≤ Fintype.card U := Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩
  have hN : (Fintype.card U : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hN1 : (Fintype.card U : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast h2
    linarith
  rw [pmfCov_eq_expect_mul_sub_mul, expect_armIndicator_pair_same r hr hij t,
    expect_armIndicator, expect_armIndicator]
  field_simp
  ring

end StatLean.ExperimentalDesign
