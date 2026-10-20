module
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Prod

@[expose] public section

/-!
# One- and two-coordinate marginals of a uniform random permutation

A permutation test relabels the pooled data by a uniform random permutation `σ` of the `N`
observations, so every statistic it computes is an average over `Perm (Fin N)` of a function
of finitely many *relabelled coordinates*. The whole first- and second-moment calculus of
such statistics rests on two facts, which is what this file records: under a uniform `σ`,

* a single coordinate is uniform on the `N` items,
  $$ |\mathbf{S}_N|^{-1} \sum_\sigma h(\sigma u) = N^{-1} \sum_l h(l) ; $$
* a pair of *distinct* coordinates is uniform on the `N(N-1)` ordered pairs of distinct
  items,
  $$ |\mathbf{S}_N|^{-1} \sum_\sigma h(\sigma u, \sigma v)
     = \bigl(N(N-1)\bigr)^{-1} \sum_{l \ne l'} h(l, l') \qquad (u \ne v) . $$

Both are proved by the same two-step argument: all fibres of `σ ↦ σ u` (resp.
`σ ↦ (σ u, σ v)`) have the same cardinality, because right multiplication by a
transposition (resp. by any permutation carrying one pair to the other) maps one fibre
bijectively onto another; and the fibres partition the group, which pins the common
cardinality down without ever computing a factorial.

The headline consequence, `avg_perm_blockAvg_sq_le`, is the variance bound that drives the
permutation central limit theorem and the consistency of studentized permutation scales: for
a *centred* coefficient vector `d`,
$$ |\mathbf{S}_N|^{-1} \sum_\sigma \Bigl(\frac 1m \sum_{i<m} d(\sigma(a_i))\Bigr)^2
   \;=\; \frac 1m \cdot \frac{N-m}{N-1} \cdot \frac 1N \sum_l d(l)^2
   \;\le\; \frac 1m \cdot \frac 1N \sum_l d(l)^2 , $$
the finite-population correction `(N-m)/(N-1) ≤ 1` being discarded.

## Main results

* `avg_perm_apply` — the one-coordinate marginal is uniform.
* `avg_perm_apply_pair` — the two-coordinate marginal is uniform on the off-diagonal.
* `avg_perm_blockAvg_sq_le` — the `O(1/m)` variance bound for a block average.
* `perm_avg_indicator_blockAvg_le` — the Chebyshev step: the group average of the
  deviation indicator, in the shape in which randomization distributions are defined.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 12 (Extensions of the
CLT to Sums of Dependent Random Variables), §12.2 (Random Sampling Without Replacement from a
Finite Population). (`TSH4 §12.2`.)

**Proof formalization notes.**
* This is the *permutation* model of sampling without replacement, whereas
  `ForMathlib/HypergeometricMoments` uses the equivalent *subset* model
  (`SubsetsOfCard N m` with the uniform average `expect`). Neither is derivable from the
  other without a bridge — the pushforward of the uniform law on `Perm (Fin N)` along
  `σ ↦ σ⁻¹ '' (block)` is uniform on `m`-subsets — and the permutation model is the one in
  which randomization distributions are *defined* (`randDist` averages over the group), so
  the moments are recorded here directly rather than transported.
* No factorial is ever computed: the fibre cardinality `C` is left as an unknown, and the
  partition identity `|Perm α| = N · C` (resp. `N(N-1) · C`) is what cancels it. This keeps
  every statement free of `Nat.factorial` and of the `m > n` edge conventions.
* `avg_perm_blockAvg_sq_le` assumes `2 ≤ N`, which is exactly what the exact identity needs
  (the factor `N - 1` is a denominator). It is not a restriction in practice: the bound is
  applied with `N = m + n` and both sample sizes tending to infinity.
* Centring (`∑ l, d l = 0`) is a hypothesis rather than built into the statement, because the
  applications supply already-centred coefficients (`d = c - c̄`) and the uncentred form
  would carry a `(∑ d)²/(N(N-1))` term that is only ever cancelled again.

**Bibliographic comments.** The moment computations for sampling without replacement, and
the combinatorial central limit theorem they support, are due to A. Wald and J. Wolfowitz,
"Statistical tests based on permutations of the observations," *Ann. Math. Statist.* **15**
(1944), 358–372, and W. Hoeffding, "A combinatorial central limit theorem," *Ann. Math.
Statist.* **22** (1951), 558–566. The randomization model itself goes back to R. A. Fisher,
*The Design of Experiments*, Oliver & Boyd, 1935, and E. J. G. Pitman, "Significance tests
which may be applied to samples from any populations," *Suppl. J. Roy. Statist. Soc.* **4**
(1937), 119–130.
-/

namespace StatLean.HypothesisTesting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### One coordinate -/

/-- All fibres of `σ ↦ σ u` have the same cardinality: right multiplication by the
transposition `(l l')` carries one onto another. -/
private lemma card_fiber_perm_apply (u l l' : α) :
    (Finset.univ.filter fun σ : Equiv.Perm α => σ u = l).card
      = (Finset.univ.filter fun σ : Equiv.Perm α => σ u = l').card := by
  classical
  refine Finset.card_bij' (fun σ _ => Equiv.swap l l' * σ) (fun σ _ => Equiv.swap l l' * σ)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    simp [hσ, Equiv.swap_apply_left]
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    simp [hσ, Equiv.swap_apply_right]
  · intro σ _
    change Equiv.swap l l' * (Equiv.swap l l' * σ) = σ
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  · intro σ _
    change Equiv.swap l l' * (Equiv.swap l l' * σ) = σ
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]

/-- **The one-coordinate marginal of a uniform random permutation is uniform.** -/
theorem avg_perm_apply (u : α) (h : α → ℝ) :
    (Fintype.card (Equiv.Perm α) : ℝ)⁻¹ * ∑ σ : Equiv.Perm α, h (σ u)
      = (Fintype.card α : ℝ)⁻¹ * ∑ l, h l := by
  classical
  set C : ℕ := (Finset.univ.filter fun σ : Equiv.Perm α => σ u = u).card with hC
  have hCpos : 0 < C := by
    rw [hC, Finset.card_pos]
    exact ⟨1, by simp⟩
  have hfib : ∀ l : α, (Finset.univ.filter fun σ : Equiv.Perm α => σ u = l).card = C :=
    fun l => card_fiber_perm_apply u l u
  have hmaps : ∀ σ : Equiv.Perm α, σ ∈ (Finset.univ : Finset (Equiv.Perm α)) →
      σ u ∈ (Finset.univ : Finset α) := fun σ _ => Finset.mem_univ _
  -- the group is the disjoint union of the fibres
  have hcard : Fintype.card (Equiv.Perm α) = Fintype.card α * C := by
    have h1 := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.sum_congr rfl fun l _ => hfib l, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h1
    simpa [Finset.card_univ] using h1
  -- the sum, computed fibrewise
  have hsum : ∑ σ : Equiv.Perm α, h (σ u) = (C : ℝ) * ∑ l, h l := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun σ => h (σ u)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hinner : (∑ σ ∈ Finset.univ.filter fun σ : Equiv.Perm α => σ u = l, h (σ u))
        = ∑ _σ ∈ Finset.univ.filter fun σ : Equiv.Perm α => σ u = l, h l :=
      Finset.sum_congr rfl fun σ hσ => by
        rw [(Finset.mem_filter.1 hσ).2]
    rw [hinner, Finset.sum_const, hfib l, nsmul_eq_mul]
  have hNpos : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨u⟩
  have hCR : (C : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hCpos.ne'
  have hNR : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
  rw [hsum, hcard, Nat.cast_mul]
  field_simp

/-! ### Two distinct coordinates -/

omit [Fintype α] [DecidableEq α] in
/-- Two prescribed values can be realised by a permutation: for `l ≠ l'` and `p ≠ p'` there
is a `ρ` with `ρ l = p` and `ρ l' = p'`. -/
private lemma exists_perm_apply_apply {l l' p p' : α} (hl : l ≠ l') (hp : p ≠ p') :
    ∃ ρ : Equiv.Perm α, ρ l = p ∧ ρ l' = p' := by
  classical
  set q : α := Equiv.swap l p l' with hq
  have hqp : q ≠ p := by
    rw [hq]
    intro hcon
    have h1 : Equiv.swap l p l' = Equiv.swap l p l := by rw [hcon, Equiv.swap_apply_left]
    exact hl ((Equiv.swap l p).injective h1).symm
  refine ⟨Equiv.swap q p' * Equiv.swap l p, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hqp) hp]
  · rw [Equiv.Perm.mul_apply, ← hq, Equiv.swap_apply_left]

/-- All fibres of `σ ↦ (σ u, σ v)` over the off-diagonal have the same cardinality. -/
private lemma card_fiber_perm_apply_pair (u v : α) {l l' p p' : α}
    (hl : l ≠ l') (hp : p ≠ p') :
    (Finset.univ.filter fun σ : Equiv.Perm α => σ u = l ∧ σ v = l').card
      = (Finset.univ.filter fun σ : Equiv.Perm α => σ u = p ∧ σ v = p').card := by
  classical
  obtain ⟨ρ, hρ1, hρ2⟩ := exists_perm_apply_apply hl hp
  refine Finset.card_bij' (fun σ _ => ρ * σ) (fun σ _ => ρ⁻¹ * σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact ⟨by simp [hσ.1, hρ1], by simp [hσ.2, hρ2]⟩
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    refine ⟨?_, ?_⟩
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hσ.1, ← hρ1]
      simp
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hσ.2, ← hρ2]
      simp
  · intro σ _
    change ρ⁻¹ * (ρ * σ) = σ
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  · intro σ _
    change ρ * (ρ⁻¹ * σ) = σ
    rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- **The two-coordinate marginal of a uniform random permutation is uniform on the ordered
pairs of distinct items.** -/
theorem avg_perm_apply_pair {u v : α} (huv : u ≠ v) (h : α → α → ℝ) :
    (Fintype.card (Equiv.Perm α) : ℝ)⁻¹ * ∑ σ : Equiv.Perm α, h (σ u) (σ v)
      = ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))⁻¹ *
        ∑ p ∈ (Finset.univ : Finset α).offDiag, h p.1 p.2 := by
  classical
  have hN2 : 2 ≤ Fintype.card α := Fintype.one_lt_card_iff_nontrivial.2 ⟨⟨u, v, huv⟩⟩
  have hNR : (2 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hN2
  set t : Finset (α × α) := (Finset.univ : Finset α).offDiag with ht
  have htcard : t.card = Fintype.card α * Fintype.card α - Fintype.card α := by
    rw [ht, Finset.offDiag_card, Finset.card_univ]
  have htcardR : (t.card : ℝ) = (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) := by
    rw [htcard, Nat.cast_sub (Nat.le_mul_of_pos_left _ (Fintype.card_pos_iff.2 ⟨u⟩)),
      Nat.cast_mul]
    ring
  have hmem : ∀ p ∈ t, p.1 ≠ p.2 := fun p hp => (Finset.mem_offDiag.1 (ht ▸ hp)).2.2
  have hmaps : ∀ σ : Equiv.Perm α, σ ∈ (Finset.univ : Finset (Equiv.Perm α)) →
      (σ u, σ v) ∈ t := by
    intro σ _
    rw [ht, Finset.mem_offDiag]
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, fun hcon => huv (σ.injective hcon)⟩
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : α × α, p₀ ∈ t := ⟨(u, v), hmaps 1 (Finset.mem_univ _)⟩
  -- the fibrewise sums use the `Prod`-equality form of the fibre
  have hpr : ∀ p : α × α, (Finset.univ.filter fun σ : Equiv.Perm α => (σ u, σ v) = p)
      = (Finset.univ.filter fun σ : Equiv.Perm α => σ u = p.1 ∧ σ v = p.2) := by
    intro p
    refine Finset.filter_congr fun σ _ => ?_
    simp [Prod.ext_iff]
  set C : ℕ := (Finset.univ.filter fun σ : Equiv.Perm α => (σ u, σ v) = p₀).card with hC
  have hfib : ∀ p ∈ t,
      (Finset.univ.filter fun σ : Equiv.Perm α => (σ u, σ v) = p).card = C := by
    intro p hp
    rw [hpr p, hC, hpr p₀]
    exact card_fiber_perm_apply_pair u v (hmem p hp) (hmem p₀ hp₀)
  have hCpos : 0 < C := by
    rw [hC, hpr p₀, Finset.card_pos]
    obtain ⟨ρ, hρ1, hρ2⟩ := exists_perm_apply_apply huv (hmem p₀ hp₀)
    exact ⟨ρ, by simp [hρ1, hρ2]⟩
  have hcard : Fintype.card (Equiv.Perm α) = t.card * C := by
    have h1 := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.sum_congr rfl fun p hp => hfib p hp, Finset.sum_const, nsmul_eq_mul] at h1
    simpa [Finset.card_univ] using h1
  have hsum : ∑ σ : Equiv.Perm α, h (σ u) (σ v) = (C : ℝ) * ∑ p ∈ t, h p.1 p.2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun σ => h (σ u) (σ v)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hinner : (∑ σ ∈ Finset.univ.filter fun σ : Equiv.Perm α => (σ u, σ v) = p,
          h (σ u) (σ v))
        = ∑ _σ ∈ Finset.univ.filter fun σ : Equiv.Perm α => (σ u, σ v) = p, h p.1 p.2 :=
      Finset.sum_congr rfl fun σ hσ => by
        have hσ2 := (Finset.mem_filter.1 hσ).2
        rw [show σ u = p.1 from by rw [← hσ2], show σ v = p.2 from by rw [← hσ2]]
    rw [hinner, Finset.sum_const, hfib p hp, nsmul_eq_mul]
  have hCR : (C : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hCpos.ne'
  have htR : (t.card : ℝ) ≠ 0 := by
    rw [htcardR]
    have : (0 : ℝ) < (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) := by
      apply mul_pos <;> linarith
    exact this.ne'
  rw [hsum, hcard, Nat.cast_mul, htcardR]
  rw [htcardR] at htR
  field_simp

/-! ### The variance of a block average -/

/-- **The `O(1/m)` variance bound for a permuted block average.** For a centred coefficient
vector `d`, the average over `Perm (Fin N)` of the squared block mean is
`(1/m) · ((N-m)/(N-1)) · (N⁻¹ ∑ d²)`, hence at most `(1/m) · (N⁻¹ ∑ d²)`. This is the
estimate that makes individual summands of a permutation statistic negligible. -/
theorem avg_perm_blockAvg_sq_le {N m : ℕ} (hm : 0 < m) (hN : 2 ≤ N)
    -- USER-INPUT: the block is a set of `m` distinct positions
    (a : Fin m → Fin N) (ha : Function.Injective a)
    -- USER-INPUT: centred coefficients
    (d : Fin N → ℝ) (hd : ∑ l, d l = 0) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), ((m : ℝ)⁻¹ * ∑ i, d (σ (a i))) ^ 2
      ≤ (m : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ∑ l, d l ^ 2) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hcardpos : 0 < Fintype.card (Equiv.Perm (Fin N)) := Fintype.card_pos
  have hcardR : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin N)) := by exact_mod_cast hcardpos
  set S₂ : ℝ := ∑ l, d l ^ 2 with hS₂
  have hS₂nn : 0 ≤ S₂ := Finset.sum_nonneg fun l _ => sq_nonneg _
  -- expand the square into a double sum over block positions
  have hexpand : ∀ σ : Equiv.Perm (Fin N), ((m : ℝ)⁻¹ * ∑ i, d (σ (a i))) ^ 2
      = ((m : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, d (σ (a i)) * d (σ (a j)) := by
    intro σ
    rw [mul_pow, sq (∑ i, d (σ (a i))), Finset.sum_mul_sum]
  -- the average of each cross term is a one- or two-coordinate marginal
  have hdiag : ∀ i : Fin m, (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), d (σ (a i)) * d (σ (a i)) = (N : ℝ)⁻¹ * S₂ := by
    intro i
    have h := avg_perm_apply (a i) (fun l => d l * d l)
    rw [Fintype.card_fin] at h
    rw [h, hS₂]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [sq]
  have hoff : ∀ i j : Fin m, i ≠ j → (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), d (σ (a i)) * d (σ (a j))
      = -(((N : ℝ) * ((N : ℝ) - 1))⁻¹ * S₂) := by
    intro i j hij
    have hne : a i ≠ a j := fun hcon => hij (ha hcon)
    have h := avg_perm_apply_pair hne (fun l l' => d l * d l')
    rw [Fintype.card_fin] at h
    rw [h]
    -- the off-diagonal sum of `d l · d l'` is `(∑ d)² − ∑ d² = −∑ d²`
    have hdiagsum : ∑ l : Fin N, d l * d l = S₂ := by
      rw [hS₂]; exact Finset.sum_congr rfl fun l _ => by rw [sq]
    have hprod : ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)),
        d p.1 * d p.2 = ∑ l, ∑ l', d l * d l' := Finset.sum_product _ _ _
    have hfull : ∑ l : Fin N, ∑ l', d l * d l' = (∑ l, d l) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
    have hdecomp : ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)))
        = (Finset.univ : Finset (Fin N)).diag ∪ (Finset.univ : Finset (Fin N)).offDiag :=
      (Finset.diag_union_offDiag _).symm
    have hdisj : Disjoint ((Finset.univ : Finset (Fin N)).diag)
        ((Finset.univ : Finset (Fin N)).offDiag) := Finset.disjoint_diag_offDiag _
    rw [hdecomp, Finset.sum_union hdisj, Finset.sum_diag, hdiagsum, hfull, hd] at hprod
    have hsplit : ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, d p.1 * d p.2 = -S₂ := by
      rw [show (0 : ℝ) ^ 2 = 0 from by ring] at hprod
      linarith
    rw [hsplit]
    ring
  -- assemble: `m` diagonal terms and `m(m−1)` off-diagonal ones
  have hswap : ∑ σ : Equiv.Perm (Fin N), ((m : ℝ)⁻¹ * ∑ i, d (σ (a i))) ^ 2
      = ((m : ℝ)⁻¹) ^ 2 *
        ∑ σ : Equiv.Perm (Fin N), ∑ i : Fin m, ∑ j : Fin m, d (σ (a i)) * d (σ (a j)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => hexpand σ
  have hexch : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      (∑ σ : Equiv.Perm (Fin N), ∑ i : Fin m, ∑ j : Fin m, d (σ (a i)) * d (σ (a j)))
      = ∑ i : Fin m, ∑ j : Fin m,
          (if i = j then (N : ℝ)⁻¹ * S₂ else -(((N : ℝ) * ((N : ℝ) - 1))⁻¹ * S₂)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl]; exact hdiag i
    · rw [if_neg hij]; exact hoff i j hij
  have hkey : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), ((m : ℝ)⁻¹ * ∑ i, d (σ (a i))) ^ 2
      = ((m : ℝ)⁻¹) ^ 2 * (∑ i : Fin m, ∑ j : Fin m,
          (if i = j then (N : ℝ)⁻¹ * S₂ else -(((N : ℝ) * ((N : ℝ) - 1))⁻¹ * S₂))) := by
    rw [hswap, ← hexch]
    ring
  rw [hkey]
  -- the closed form of the double sum, then the finite-population correction
  set A : ℝ := (N : ℝ)⁻¹ * S₂ with hA
  set B : ℝ := -(((N : ℝ) * ((N : ℝ) - 1))⁻¹ * S₂) with hB
  have hrow : ∀ i : Fin m, (∑ j : Fin m, (if i = j then A else B))
      = (m : ℝ) * B + (A - B) := by
    intro i
    have hterm : ∀ j : Fin m, (if i = j then A else B) = B + (if i = j then A - B else 0) := by
      intro j; by_cases h : i = j <;> simp [h]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_eq Finset.univ i (fun _ => A - B), if_pos (Finset.mem_univ i)]
  have hcount : (∑ i : Fin m, ∑ j : Fin m, (if i = j then A else B))
      = (m : ℝ) * A + ((m : ℝ) * (m : ℝ) - (m : ℝ)) * B := by
    rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hcount, hA, hB]
  have hstep : ((m : ℝ)⁻¹) ^ 2 * ((m : ℝ) * ((N : ℝ)⁻¹ * S₂)
        + ((m : ℝ) * (m : ℝ) - (m : ℝ)) * -(((N : ℝ) * ((N : ℝ) - 1))⁻¹ * S₂))
      = (m : ℝ)⁻¹ * ((N : ℝ)⁻¹ * S₂)
        - ((m : ℝ) - 1) * S₂ / ((m : ℝ) * (N : ℝ) * ((N : ℝ) - 1)) := by
    field_simp
    ring
  rw [hstep]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hnn : 0 ≤ ((m : ℝ) - 1) * S₂ / ((m : ℝ) * (N : ℝ) * ((N : ℝ) - 1)) :=
    div_nonneg (mul_nonneg (by linarith) hS₂nn) (by positivity)
  linarith

/-- **Chebyshev over the group.** The fraction of permutations for which the block average
of a centred coefficient vector deviates by `ε` is at most `ε⁻² (1/m) (N⁻¹ ∑ d²)`. The
left-hand side is written as the group average of an indicator — the shape in which
randomization distributions are defined — so this is directly the Chebyshev step of a
permutation argument. -/
theorem perm_avg_indicator_blockAvg_le {N m : ℕ} (hm : 0 < m) (hN : 2 ≤ N)
    -- USER-INPUT: the block is a set of `m` distinct positions
    (a : Fin m → Fin N) (ha : Function.Injective a)
    -- USER-INPUT: centred coefficients
    (d : Fin N → ℝ) (hd : ∑ l, d l = 0) {ε : ℝ}
    -- USER-INPUT: a positive deviation
    (hε : 0 < ε) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N),
          (if ε ≤ |(m : ℝ)⁻¹ * ∑ i, d (σ (a i))| then (1 : ℝ) else 0)
      ≤ ε⁻¹ ^ 2 * ((m : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ∑ l, d l ^ 2)) := by
  have hcardR : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin N)) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Fin N)))
  have hinvsq : ε⁻¹ ^ 2 * ε ^ 2 = 1 := by
    field_simp
  -- pointwise: the indicator is dominated by the normalized square
  have hpt : ∀ σ : Equiv.Perm (Fin N),
      (if ε ≤ |(m : ℝ)⁻¹ * ∑ i, d (σ (a i))| then (1 : ℝ) else 0)
        ≤ ε⁻¹ ^ 2 * ((m : ℝ)⁻¹ * ∑ i, d (σ (a i))) ^ 2 := by
    intro σ
    by_cases hσ : ε ≤ |(m : ℝ)⁻¹ * ∑ i, d (σ (a i))|
    · rw [if_pos hσ]
      have habs : ε ^ 2 ≤ ((m : ℝ)⁻¹ * ∑ i, d (σ (a i))) ^ 2 := by
        have h1 : ε ^ 2 ≤ |(m : ℝ)⁻¹ * ∑ i, d (σ (a i))| ^ 2 := by
          have := mul_le_mul hσ hσ hε.le (abs_nonneg _)
          rw [← sq, ← sq] at this
          exact this
        rwa [sq_abs] at h1
      have hmul := mul_le_mul_of_nonneg_left habs (by positivity : (0 : ℝ) ≤ ε⁻¹ ^ 2)
      linarith
    · rw [if_neg hσ]
      positivity
  calc (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N),
          (if ε ≤ |(m : ℝ)⁻¹ * ∑ i, d (σ (a i))| then (1 : ℝ) else 0)
      ≤ (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin N),
          ε⁻¹ ^ 2 * ((m : ℝ)⁻¹ * ∑ i, d (σ (a i))) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hpt σ) (by positivity)
    _ = ε⁻¹ ^ 2 * ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin N),
          ((m : ℝ)⁻¹ * ∑ i, d (σ (a i))) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ε⁻¹ ^ 2 * ((m : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ∑ l, d l ^ 2)) :=
        mul_le_mul_of_nonneg_left (avg_perm_blockAvg_sq_le hm hN a ha d hd) (by positivity)

end StatLean.HypothesisTesting
