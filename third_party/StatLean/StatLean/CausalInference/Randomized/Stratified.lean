module
public import StatLean.CausalInference.Randomized.CompleteRandomization
public import StatLean.CausalInference.Core.FinitePopulation

@[expose] public section

/-!
# Stratified randomized experiments — the design and unbiasedness

In a stratified randomized experiment (SRE) the units are grouped by a discrete covariate
into `K` strata and an independent complete randomization is run inside each stratum, with
`m k` treated units in stratum `k`. The stratified estimator is the size-weighted average
of the within-stratum difference in means,

$$\hat\tau_S=\sum_k \frac{n_{[k]}}{n}\,\hat\tau_{[k]},$$

and it is unbiased for the finite-population average causal effect.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Definition 5.1 (§5.1, p. 60: the SRE as `K`
independent CREs); §5.3.1 (pp. 66–67: the stratified estimator, its unbiasedness and its
variance — stated in the running text, with no theorem number); §5.4 with eq. (5.5)
(pp. 72–75: a CRE conditioned on the within-stratum treated counts *is* an SRE, the basis
of post-stratification). (`Ding Definition 5.1; §5.3.1; §5.4 eq. (5.5)`.) Stratified
randomized experiments are ch. 9 of G. W. Imbens and D. B. Rubin, *Causal Inference for
Statistics, Social, and Biomedical Sciences*, Cambridge University Press, 2015.
(`IR ch. 9`.)

**Scope.** Formalized here: the design, the conditioning relation to complete
randomization (eq. (5.5)'s combinatorial content, `stratifiedSupport_subset_completeSupport`),
the within-stratum inclusion probabilities, and **unbiasedness** of the stratified
estimator. The exact stratified *variance* `∑ π²_[k] Var(τ̂_[k])` is **not** formalized in
this release: it needs the full product-design factorization across strata (each stratum's
assignment independent of the others), which is a substantially larger piece of
combinatorial infrastructure than everything else in this file, and Ding himself states it
by applying Theorem 4.1 stratum-wise rather than proving it afresh. The per-stratum
variance identity is already available as `Neyman.differenceInMeans_variance`.

**Proof formalization notes.** The unbiasedness proof deliberately avoids the product
structure. It uses only two facts: (i) on the SRE support, the number of treated units in
stratum `k` is constant (`= m k`) — true by definition of the support; and (ii) the design
is invariant under transpositions of two units *within* a stratum, so the inclusion
probability `E[Zᵢ]` is the same for all `i` in a stratum. Summing (ii) over the stratum and
using (i) forces `E[Zᵢ] = m k / n_k`. That is the whole argument, and it is exactly why
stratification preserves unbiasedness whatever the allocation.

**Bibliographic comments.** Stratification (blocking) in experimental design goes back to
R. A. Fisher, *The Design of Experiments*, Oliver & Boyd, 1935.
-/

namespace StatLean.CausalInference

variable {n K : ℕ}

/-- The set of units in stratum `k`. -/
def stratum (g : Fin n → Fin K) (k : Fin K) : Finset (Fin n) :=
  Finset.univ.filter fun i => g i = k

/-! ### LEAN-ONLY private helpers

Bookkeeping only: intersecting a set of units with an arm is filtering it, the two arms
partition any set of units, `Design.expect` is linear, and transposing two units is an
involution of the assignment vectors. -/

/-- Intersecting with an arm is filtering. -/
private lemma inter_armIdx_eq_filter (A : Finset (Fin n)) (z : Assignment n) (a : Bool) :
    A ∩ armIdx z a = A.filter fun i => z i = a := by
  ext l; simp [armIdx]

/-- The two arms partition any set of units. -/
private lemma card_inter_true_add_false (A : Finset (Fin n)) (z : Assignment n) :
    (A ∩ armIdx z true).card + (A ∩ armIdx z false).card = A.card := by
  rw [inter_armIdx_eq_filter, inter_armIdx_eq_filter]
  have := Finset.card_filter_add_card_filter_not (s := A) (p := fun i => z i = true)
  simpa [Bool.not_eq_true] using this

/-- Summing the treatment indicator over a set of units counts its treated members. -/
private lemma sum_ind_card (A : Finset (Fin n)) (z : Assignment n) :
    ∑ l ∈ A, ind (z l) = ((A ∩ armIdx z true).card : ℝ) := by
  rw [inter_armIdx_eq_filter, Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl fun l _ => by cases z l <;> simp [ind]

/-- The observed outcomes of the treated members of `A`, as a `Z`-weighted sum over `A`. -/
private lemma sum_obs_inter_true (S : ScienceTable n) (A : Finset (Fin n)) (z : Assignment n) :
    ∑ l ∈ A ∩ armIdx z true, S.observed z l = ∑ l ∈ A, S.y1 l * ind (z l) := by
  rw [inter_armIdx_eq_filter, Finset.sum_filter]
  exact Finset.sum_congr rfl fun l _ => by
    cases hzl : z l <;> simp [ind, ScienceTable.observed, hzl]

/-- The observed outcomes of the control members of `A`, as a `(1-Z)`-weighted sum. -/
private lemma sum_obs_inter_false (S : ScienceTable n) (A : Finset (Fin n)) (z : Assignment n) :
    ∑ l ∈ A ∩ armIdx z false, S.observed z l = ∑ l ∈ A, S.y0 l * (1 - ind (z l)) := by
  rw [inter_armIdx_eq_filter, Finset.sum_filter]
  exact Finset.sum_congr rfl fun l _ => by
    cases hzl : z l <;> simp [ind, ScienceTable.observed, hzl]

/-- `Design.expect` respects pointwise equality on the support. -/
private lemma expect_congr {D : Design n} {f₁ f₂ : Assignment n → ℝ}
    (h : ∀ z ∈ D.support, f₁ z = f₂ z) : D.expect f₁ = D.expect f₂ := by
  simp only [Design.expect, Finset.sum_congr rfl h]

/-- `Design.expect` of a constant. -/
private lemma expect_const (D : Design n) (c : ℝ) : D.expect (fun _ => c) = c := by
  have hc : ((D.support.card : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr D.support_nonempty).ne'
  simp only [Design.expect, Finset.sum_const, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- `Design.expect` pulls out scalars. -/
private lemma expect_const_mul (D : Design n) (c : ℝ) (f : Assignment n → ℝ) :
    D.expect (fun z => c * f z) = c * D.expect f := by
  simp only [Design.expect, ← Finset.mul_sum]
  ring

/-- `Design.expect` is subtractive. -/
private lemma expect_sub (D : Design n) (f g : Assignment n → ℝ) :
    D.expect (fun z => f z - g z) = D.expect f - D.expect g := by
  simp only [Design.expect, Finset.sum_sub_distrib]
  ring

/-- `Design.expect` commutes with finite sums. -/
private lemma expect_sum (D : Design n) {ι : Type*} (s : Finset ι)
    (f : ι → Assignment n → ℝ) :
    D.expect (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, D.expect (f i) := by
  simp only [Design.expect]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- The expectation of a within-stratum difference in means, once the arm sums have been
written as weighted sums over the whole stratum: everything reduces to the inclusion
probabilities `E[Zₗ]`. -/
private lemma expect_arm_affine (D : Design n) (A : Finset (Fin n)) (c d : ℝ)
    (u v : Fin n → ℝ) :
    D.expect (fun z => c * (∑ l ∈ A, u l * ind (z l))
        - d * (∑ l ∈ A, v l * (1 - ind (z l))))
      = c * (∑ l ∈ A, u l * D.expect (fun z => ind (z l)))
        - d * (∑ l ∈ A, v l * (1 - D.expect (fun z => ind (z l)))) := by
  have hsplit : D.expect (fun z => c * (∑ l ∈ A, u l * ind (z l))
        - d * (∑ l ∈ A, v l * (1 - ind (z l))))
      = D.expect (fun z => c * (∑ l ∈ A, u l * ind (z l)))
        - D.expect (fun z => d * (∑ l ∈ A, v l * (1 - ind (z l)))) :=
    expect_sub D (fun z => c * (∑ l ∈ A, u l * ind (z l)))
      (fun z => d * (∑ l ∈ A, v l * (1 - ind (z l))))
  rw [hsplit, expect_const_mul D c (fun z => ∑ l ∈ A, u l * ind (z l)),
    expect_const_mul D d (fun z => ∑ l ∈ A, v l * (1 - ind (z l))),
    expect_sum D A (fun l z => u l * ind (z l)),
    expect_sum D A (fun l z => v l * (1 - ind (z l)))]
  congr 2
  · exact Finset.sum_congr rfl fun l _ => expect_const_mul D (u l) (fun z => ind (z l))
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [expect_const_mul D (v l) (fun z => 1 - ind (z l))]
    have hs : D.expect (fun z => (1 : ℝ) - ind (z l))
        = D.expect (fun _ => (1 : ℝ)) - D.expect (fun z => ind (z l)) :=
      expect_sub D (fun _ => (1 : ℝ)) (fun z => ind (z l))
    rw [hs, expect_const]

/-- The **transposition of two units** in an assignment vector. -/
private def swapA (i j : Fin n) (z : Assignment n) : Assignment n :=
  fun l => z (Equiv.swap i j l)

/-- Transposition is an involution. -/
private lemma swapA_swapA (i j : Fin n) (z : Assignment n) : swapA i j (swapA i j z) = z := by
  funext l; simp [swapA]

/-- A transposition inside a stratum preserves the stratum map. -/
private lemma g_swap {g : Fin n → Fin K} {i j : Fin n} (hij : g i = g j) (l : Fin n) :
    g (Equiv.swap i j l) = g l := by
  rcases eq_or_ne l i with rfl | hli
  · rw [Equiv.swap_apply_left]; exact hij.symm
  · rcases eq_or_ne l j with rfl | hlj
    · rw [Equiv.swap_apply_right]; exact hij
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]

/-- A transposition inside a stratum moves each stratum's treated set bijectively. -/
private lemma stratum_inter_swapA {g : Fin n → Fin K} {i j : Fin n} (hij : g i = g j)
    (z : Assignment n) (k : Fin K) :
    stratum g k ∩ armIdx (swapA i j z) true
      = (stratum g k ∩ armIdx z true).map (Equiv.swap i j).toEmbedding := by
  ext l
  rw [Finset.mem_map_equiv]
  simp only [Finset.mem_inter, stratum, armIdx, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.symm_swap, g_swap hij]
  simp only [swapA]

/-- The support of a **stratified randomized experiment**: assignments treating exactly
`m k` units inside each stratum `k` (Ding Definition 5.1). -/
def stratifiedSupport (g : Fin n → Fin K) (mk : Fin K → ℕ) : Finset (Assignment n) :=
  Finset.univ.filter fun z => ∀ k, ((stratum g k) ∩ armIdx z true).card = mk k

/-- Membership in the stratified support, unfolded. -/
private lemma mem_stratifiedSupport_iff {g : Fin n → Fin K} {mk : Fin K → ℕ}
    {z : Assignment n} :
    z ∈ stratifiedSupport g mk ↔ ∀ k, ((stratum g k) ∩ armIdx z true).card = mk k := by
  simp [stratifiedSupport]

/-- The support is invariant under a transposition inside a stratum. -/
private lemma swapA_mem_stratifiedSupport {g : Fin n → Fin K} {mk : Fin K → ℕ} {i j : Fin n}
    (hij : g i = g j) {z : Assignment n} (hz : z ∈ stratifiedSupport g mk) :
    swapA i j z ∈ stratifiedSupport g mk := by
  refine mem_stratifiedSupport_iff.mpr fun k => ?_
  rw [stratum_inter_swapA hij z k, Finset.card_map]
  exact mem_stratifiedSupport_iff.mp hz k

/-- The stratified support is nonempty when each stratum can supply its treated units. -/
theorem stratifiedSupport_nonempty {g : Fin n → Fin K} {mk : Fin K → ℕ}
    -- USER-INPUT: each stratum is large enough for its allocation; Ding Definition 5.1
    (h : ∀ k, mk k ≤ (stratum g k).card) :
    (stratifiedSupport g mk).Nonempty := by
  classical
  -- pick the treated units of each stratum separately; the strata are disjoint, so the
  -- union treats exactly `mk k` units of stratum `k`
  choose t hts htc using fun k => Finset.exists_subset_card_eq (h k)
  have hmem : ∀ (k' : Fin K) (l : Fin n), l ∈ t k' → g l = k' := by
    intro k' l hl
    simpa [stratum] using hts k' hl
  refine ⟨fun l => decide (l ∈ Finset.univ.biUnion t), mem_stratifiedSupport_iff.mpr fun k => ?_⟩
  have harm : armIdx (fun l => decide (l ∈ Finset.univ.biUnion t)) true
      = Finset.univ.biUnion t := by
    ext l; simp [armIdx]
  rw [harm]
  have hkey : stratum g k ∩ Finset.univ.biUnion t = t k := by
    ext l
    constructor
    · intro hl
      obtain ⟨hl1, hl2⟩ := Finset.mem_inter.mp hl
      have hgl : g l = k := by simpa [stratum] using hl1
      obtain ⟨k', -, hk'⟩ := Finset.mem_biUnion.mp hl2
      have hkk : k' = k := by rw [← hmem k' l hk', hgl]
      rwa [hkk] at hk'
    · intro hl
      refine Finset.mem_inter.mpr ⟨?_, Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hl⟩⟩
      simpa [stratum] using hmem k l hl
  rw [hkey, htc k]

/-- The **stratified randomized experiment** as a design (Ding Definition 5.1). -/
noncomputable def stratifiedDesign (g : Fin n → Fin K) (mk : Fin K → ℕ)
    (h : ∀ k, mk k ≤ (stratum g k).card) : Design n :=
  ⟨stratifiedSupport g mk, stratifiedSupport_nonempty h⟩

/-- **A stratified assignment is a completely randomized assignment with the given total**
(Ding §5.4, eq. (5.5)): the SRE support sits inside the CRE support with `n₁ = ∑ₖ m k`.
Conditioning a CRE on the within-stratum counts is what produces the SRE. -/
theorem stratifiedSupport_subset_completeSupport {g : Fin n → Fin K} {mk : Fin K → ℕ}
    {z : Assignment n} (hz : z ∈ stratifiedSupport g mk) :
    z ∈ completeSupport n (∑ k, mk k) := by
  classical
  have hz' := mem_stratifiedSupport_iff.mp hz
  rw [completeSupport, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [numTreated, Finset.card_eq_sum_card_fiberwise (f := g) (t := (Finset.univ : Finset (Fin K)))
    (fun l _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hz' k]
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_inter, stratum, armIdx, Finset.mem_univ, true_and]
  tauto

/-- **Within-stratum exchangeability**: the stratified design is invariant under swapping
two units of the same stratum, so their inclusion probabilities agree. -/
theorem stratifiedDesign_expect_ind_eq {g : Fin n → Fin K} {mk : Fin K → ℕ}
    (h : ∀ k, mk k ≤ (stratum g k).card) {i j : Fin n}
    -- USER-INPUT: two units of the same stratum; Ding Definition 5.1
    (hij : g i = g j) :
    (stratifiedDesign g mk h).expect (fun z => ind (z i))
      = (stratifiedDesign g mk h).expect (fun z => ind (z j)) := by
  simp only [Design.expect]
  congr 1
  refine Finset.sum_nbij' (fun z => swapA i j z) (fun z => swapA i j z) ?_ ?_ ?_ ?_ ?_
  · exact fun z hz => swapA_mem_stratifiedSupport hij hz
  · exact fun z hz => swapA_mem_stratifiedSupport hij hz
  · exact fun z _ => swapA_swapA i j z
  · exact fun z _ => swapA_swapA i j z
  · intro z _
    simp [swapA]

/-- **The within-stratum inclusion probability** (Ding Definition 5.1): a unit of stratum
`k` is treated with probability `m k / n_k`. -/
theorem stratifiedDesign_expect_ind {g : Fin n → Fin K} {mk : Fin K → ℕ}
    (h : ∀ k, mk k ≤ (stratum g k).card) (i : Fin n)
    -- LEAN-ONLY: the unit's stratum is nonempty (it contains `i`), stated for the divisor
    (hne : 0 < (stratum g (g i)).card) :
    (stratifiedDesign g mk h).expect (fun z => ind (z i))
      = (mk (g i) : ℝ) / ((stratum g (g i)).card : ℝ) := by
  classical
  -- on the support the stratum's indicators sum to `mk (g i)` …
  have hpt : ∀ z ∈ (stratifiedDesign g mk h).support,
      ∑ l ∈ stratum g (g i), ind (z l) = (mk (g i) : ℝ) := by
    intro z hz
    rw [sum_ind_card, mem_stratifiedSupport_iff.mp hz (g i)]
  have hE := expect_congr (D := stratifiedDesign g mk h) hpt
  rw [expect_const] at hE
  have hsum2 : (stratifiedDesign g mk h).expect (fun z => ∑ l ∈ stratum g (g i), ind (z l))
      = ∑ l ∈ stratum g (g i), (stratifiedDesign g mk h).expect (fun z => ind (z l)) :=
    expect_sum _ _ (fun l z => ind (z l))
  rw [hsum2] at hE
  -- … and by within-stratum exchangeability all of them are equal
  have hall : ∀ l ∈ stratum g (g i),
      (stratifiedDesign g mk h).expect (fun z => ind (z l))
        = (stratifiedDesign g mk h).expect (fun z => ind (z i)) := by
    intro l hl
    have hgl : g l = g i := by simpa [stratum] using hl
    exact stratifiedDesign_expect_ind_eq h hgl
  rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul] at hE
  have hc : (((stratum g (g i)).card : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hne.ne'
  rw [eq_div_iff hc]
  linear_combination hE

/-- The **within-stratum difference in means** `τ̂_[k]`. Junk value `0` if an arm of the
stratum is empty. -/
noncomputable def stratumDiffInMeans (S : ScienceTable n) (g : Fin n → Fin K) (k : Fin K)
    (z : Assignment n) : ℝ :=
  (((stratum g k ∩ armIdx z true).card : ℝ)⁻¹
      * ∑ i ∈ stratum g k ∩ armIdx z true, S.observed z i)
  - (((stratum g k ∩ armIdx z false).card : ℝ)⁻¹
      * ∑ i ∈ stratum g k ∩ armIdx z false, S.observed z i)

/-- The **stratified estimator** `τ̂_S = ∑ₖ (n_[k]/n) τ̂_[k]` (Ding §5.3.1). -/
noncomputable def stratifiedEstimator (S : ScienceTable n) (g : Fin n → Fin K)
    (z : Assignment n) : ℝ :=
  ∑ k, (((stratum g k).card : ℝ) / (n : ℝ)) * stratumDiffInMeans S g k z

/-- The **within-stratum average causal effect** `τ_[k]`. -/
noncomputable def stratumATE (S : ScienceTable n) (g : Fin n → Fin K) (k : Fin K) : ℝ :=
  ((stratum g k).card : ℝ)⁻¹ * ∑ i ∈ stratum g k, S.unitEffect i

/-- **The within-stratum estimator is unbiased for the within-stratum effect**
(Ding §5.3.1, from Theorem 4.1 applied inside the stratum). -/
theorem stratumDiffInMeans_unbiased (S : ScienceTable n) {g : Fin n → Fin K} {mk : Fin K → ℕ}
    (h : ∀ k, mk k ≤ (stratum g k).card) (k : Fin K)
    -- USER-INPUT: both arms of the stratum are nonempty; Ding Definition 5.1
    (h1 : 0 < mk k) (h0 : mk k < (stratum g k).card) :
    (stratifiedDesign g mk h).expect (stratumDiffInMeans S g k) = stratumATE S g k := by
  classical
  have hNpos : 0 < (stratum g k).card := lt_of_le_of_lt (Nat.zero_le _) h0
  have hN : (((stratum g k).card : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  have hm1 : ((mk k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr h1.ne'
  have hcast : (((stratum g k).card - mk k : ℕ) : ℝ)
      = ((stratum g k).card : ℝ) - (mk k : ℝ) := Nat.cast_sub h0.le
  have hm0 : ((stratum g k).card : ℝ) - (mk k : ℝ) ≠ 0 := by
    have : (mk k : ℝ) < ((stratum g k).card : ℝ) := by exact_mod_cast h0
    linarith
  -- on the support the arm sizes are `mk k` and `n_k - mk k`, and the arm sums are the
  -- weighted sums of the potential outcomes over the whole stratum
  have hpt : ∀ z ∈ (stratifiedDesign g mk h).support, stratumDiffInMeans S g k z
      = (mk k : ℝ)⁻¹ * (∑ l ∈ stratum g k, S.y1 l * ind (z l))
        - (((stratum g k).card : ℝ) - (mk k : ℝ))⁻¹
            * (∑ l ∈ stratum g k, S.y0 l * (1 - ind (z l))) := by
    intro z hz
    have hct : ((stratum g k) ∩ armIdx z true).card = mk k :=
      mem_stratifiedSupport_iff.mp hz k
    have hcf : ((stratum g k) ∩ armIdx z false).card = (stratum g k).card - mk k := by
      have := card_inter_true_add_false (stratum g k) z
      omega
    rw [stratumDiffInMeans, hct, hcf, hcast, sum_obs_inter_true, sum_obs_inter_false]
  change (stratifiedDesign g mk h).expect (fun z => stratumDiffInMeans S g k z)
    = stratumATE S g k
  rw [expect_congr hpt, expect_arm_affine]
  -- every unit of the stratum has inclusion probability `mk k / n_k`
  have hEl : ∀ l ∈ stratum g k, (stratifiedDesign g mk h).expect (fun z => ind (z l))
      = (mk k : ℝ) / ((stratum g k).card : ℝ) := by
    intro l hl
    have hgl : g l = k := by simpa [stratum] using hl
    have hkey := stratifiedDesign_expect_ind h l (by rw [hgl]; exact hNpos)
    rwa [hgl] at hkey
  have hs1 : ∑ l ∈ stratum g k, S.y1 l * (stratifiedDesign g mk h).expect (fun z => ind (z l))
      = ∑ l ∈ stratum g k, S.y1 l * ((mk k : ℝ) / ((stratum g k).card : ℝ)) :=
    Finset.sum_congr rfl fun l hl => by rw [hEl l hl]
  have hs0 : ∑ l ∈ stratum g k,
        S.y0 l * (1 - (stratifiedDesign g mk h).expect (fun z => ind (z l)))
      = ∑ l ∈ stratum g k, S.y0 l * (1 - (mk k : ℝ) / ((stratum g k).card : ℝ)) :=
    Finset.sum_congr rfl fun l hl => by rw [hEl l hl]
  rw [hs1, hs0, ← Finset.sum_mul, ← Finset.sum_mul, stratumATE]
  have hy : ∑ l ∈ stratum g k, S.unitEffect l
      = (∑ l ∈ stratum g k, S.y1 l) - ∑ l ∈ stratum g k, S.y0 l := by
    simp [ScienceTable.unitEffect, Finset.sum_sub_distrib]
  rw [hy]
  field_simp

/-- **Unbiasedness of the stratified estimator** (Ding §5.3.1, p. 66): stratification
preserves unbiasedness for any allocation. -/
theorem stratifiedEstimator_unbiased (S : ScienceTable n) {g : Fin n → Fin K} {mk : Fin K → ℕ}
    (h : ∀ k, mk k ≤ (stratum g k).card)
    -- USER-INPUT: every stratum has units in both arms; Ding Definition 5.1
    (h1 : ∀ k, 0 < mk k) (h0 : ∀ k, mk k < (stratum g k).card)
    -- LEAN-ONLY: a nonempty population, so that `n⁻¹` is not a junk value
    (hn : 0 < n) :
    (stratifiedDesign g mk h).expect (stratifiedEstimator S g) = S.finiteATE := by
  have hdec : S.finiteATE
      = ∑ k, (((stratum g k).card : ℝ) / (n : ℝ)) * stratumATE S g k :=
    finiteATE_eq_sum_subgroupATE S g hn
  have hexp : (stratifiedDesign g mk h).expect (stratifiedEstimator S g)
      = (stratifiedDesign g mk h).expect
          (fun z => ∑ k, (((stratum g k).card : ℝ) / (n : ℝ)) * stratumDiffInMeans S g k z) :=
    rfl
  rw [hexp, expect_sum _ Finset.univ
    (fun k z => (((stratum g k).card : ℝ) / (n : ℝ)) * stratumDiffInMeans S g k z), hdec]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expect_const_mul _ _ (fun z => stratumDiffInMeans S g k z)]
  congr 1
  exact stratumDiffInMeans_unbiased S h k (h1 k) (h0 k)

/-- The population effect is the stratum-size-weighted average of the stratum effects — the
identity that makes the stratified estimator target `τ` (Ding §5.3.1). -/
theorem finiteATE_eq_sum_stratumATE (S : ScienceTable n) (g : Fin n → Fin K)
    (hn : 0 < n) :
    S.finiteATE = ∑ k, (((stratum g k).card : ℝ) / (n : ℝ)) * stratumATE S g k :=
  finiteATE_eq_sum_subgroupATE S g hn

end StatLean.CausalInference
