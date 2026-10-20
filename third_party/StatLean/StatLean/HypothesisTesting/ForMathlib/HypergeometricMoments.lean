module
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Moments of sampling without replacement

A two-sample split assigns `m` of `n` labelled items to the first group, all
`binom(n, m)` splits being equally likely. Writing `Wᵢ = 1{i is in the first group}`, the
weights are exchangeable Bernoulli`(m/n)` variables that are *negatively correlated* — the
constraint `∑ᵢ Wᵢ = m` makes them dependent — and every linear statistic of a two-sample
permutation test is of the form `∑ᵢ cᵢ Wᵢ` for a deterministic vector `c` built from the
pooled data. Its first two moments are therefore the arithmetic backbone of permutation
inference, and this file records them:
$$\mathbb E W_i = \frac{m}{n}, \qquad
  \mathbb E W_i W_j = \frac{m(m-1)}{n(n-1)}\ (i \ne j), \qquad
  \operatorname{Cov}(W_i, W_j) = -\frac{m(n-m)}{n^2 (n-1)} ,$$
$$\operatorname{Var}\Bigl(\sum_i c_i W_i\Bigr)
  = \frac{m(n-m)}{n(n-1)} \sum_i (c_i - \bar c)^2 ,$$
from which the group average `m⁻¹ ∑ᵢ cᵢ Wᵢ` has variance of order `1/m` times the
population dispersion of `c` — the estimate that drives the permutation central limit
theorem.

## Main results

* `SubsetsOfCard`, `weight`, `expect` — the sampling space and the uniform average.
* `expect_eq_sum_uniform` — `expect` is the expectation under the uniform law on splits.
* `expect_weight`, `expect_weight_pair`, `cov_weight` — the first and second moments.
* `var_linear` — the exact variance of a linear statistic.
* `var_mean_linear_le` — the `O(1/m)` bound on the variance of the group average.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 12 (Extensions of the
CLT to Sums of Dependent Random Variables), §12.2 (Random Sampling Without Replacement from a
Finite Population), the moments of sampling without replacement from a finite population.
(`TSH4 §12.2`.)

**Proof formalization notes.**
* Randomness is carried by the **finite-set** model: the sample space is the subtype
  `SubsetsOfCard n m = {s : Finset (Fin n) // s.card = m}` of `m`-element subsets, uniformly
  weighted. This is the form in which the moments are cleanest — every identity is a
  counting statement about how many `m`-subsets contain a given index or pair of indices —
  and it avoids the bookkeeping of the equivalent "random permutation of `Fin n`, take the
  first `m`" model.
* The uniform law is available both as a probability mass function
  (`sampleUnif = PMF.uniformOfFintype`, the least-friction Mathlib carrier: it needs no
  σ-algebra on the subtype, unlike `Measure.count` normalisation) and, for computations, as
  the normalised counting average `expect`. `expect_eq_sum_uniform` is the bridge; all
  moment statements are phrased with `expect`, so that no `Nonempty` instance argument
  pollutes them.
* Edge behaviour of `expect`: when `m > n` the sample space is empty, `Fintype.card = 0`,
  and `expect f = 0` for every `f` (Lean's `(0 : ℝ)⁻¹ = 0`). Statements that would be false
  there carry `m ≤ n`.
* Subtraction is performed in `ℝ`, never in `ℕ`: `(m : ℝ) - 1` and `(n : ℝ) - m` are the
  intended quantities, and truncated natural subtraction would silently change the
  identities at `m = 0`.
* Side conditions are kept minimal: `0 < n` is *not* assumed in `expect_weight` (an
  argument `i : Fin n` already provides it), and `2 ≤ n` is not assumed in
  `expect_weight_pair` (two distinct indices in `Fin n` already provide it). It is assumed
  in `var_linear`, where nothing else rules out the vacuous `n ≤ 1` case in which the factor
  `(n - 1)` in the denominator vanishes.
* `var_mean_linear_le` states the bound with the explicit constant `2`, obtained from the
  exact identity by `(n - m)/(n - 1) ≤ 2` for `n ≥ 2`; no attempt is made to keep the sharp
  finite-population correction factor, since consumers only need the `O(1/m)` rate.

**Bibliographic comments.** The permutation/randomization model in which these moments are
computed goes back to R. A. Fisher, *The Design of Experiments*, Oliver & Boyd, 1935, and
E. J. G. Pitman, "Significance tests which may be applied to samples from any populations,"
*Suppl. J. Roy. Statist. Soc.* **4** (1937), 119–130. The moment calculations and the
combinatorial central limit theorem they support are due to A. Wald and J. Wolfowitz,
"Statistical tests based on permutations of the observations," *Ann. Math. Statist.* **15**
(1944), 358–372, and W. Hoeffding, "A combinatorial central limit theorem," *Ann. Math.
Statist.* **22** (1951), 558–566, and "The large-sample power of tests based on permutations
of observations," *Ann. Math. Statist.* **23** (1952), 169–192.
-/

open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

/-- The sample space of a two-sample split: the `m`-element subsets of `Fin n`, i.e. the
possible first groups. Empty when `m > n`. -/
abbrev SubsetsOfCard (n m : ℕ) := {s : Finset (Fin n) // s.card = m}

/-- The **inclusion weight** of item `i` in the split `s`: `1` if `i` lands in the first
group, `0` otherwise. -/
def weight {n m : ℕ} (i : Fin n) (s : SubsetsOfCard n m) : ℝ :=
  if i ∈ s.val then 1 else 0

/-- The **uniform average** over all `m`-element splits — the expectation under the uniform
law on `SubsetsOfCard n m`.

Edge behaviour: when the sample space is empty (`m > n`) the cardinality is `0` and the
value is `0`. -/
noncomputable def expect {n m : ℕ} (f : SubsetsOfCard n m → ℝ) : ℝ :=
  (Fintype.card (SubsetsOfCard n m) : ℝ)⁻¹ * ∑ s, f s

/-- The **uniform law on splits** as a probability mass function; the probabilistic carrier
behind `expect`. Requires the split to exist (`m ≤ n`), which is what the `Nonempty`
instance argument records. -/
noncomputable def sampleUnif (n m : ℕ) [Nonempty (SubsetsOfCard n m)] :
    PMF (SubsetsOfCard n m) :=
  PMF.uniformOfFintype (SubsetsOfCard n m)

/-! ### Private helpers: cardinalities, `expect` linearity, and split counts -/

/-- The sample space has `binom(n, m)` points. -/
private lemma card_subsetsOfCard (n m : ℕ) :
    Fintype.card (SubsetsOfCard n m) = n.choose m := by
  simp

/-- `expect` of a function of the underlying finset, as a normalized sum over
`powersetCard`. -/
private lemma expect_eq_powersetCard {n m : ℕ} (F : Finset (Fin n) → ℝ) :
    expect (fun s : SubsetsOfCard n m => F s.val)
      = (n.choose m : ℝ)⁻¹ * ∑ s ∈ Finset.powersetCard m Finset.univ, F s := by
  unfold expect
  rw [card_subsetsOfCard]
  congr 1
  refine (Finset.sum_subtype (Finset.powersetCard m Finset.univ) ?_ F).symm
  intro s
  simp [Finset.mem_powersetCard]

/-- `expect` of a constant is the constant (uses `binom(n, m) > 0`, i.e. `m ≤ n`). -/
private lemma expect_const {n m : ℕ} (hm : m ≤ n) (c : ℝ) :
    expect (fun _ : SubsetsOfCard n m => c) = c := by
  have hcard : Fintype.card (SubsetsOfCard n m) ≠ 0 := by
    rw [card_subsetsOfCard]; exact (Nat.choose_pos hm).ne'
  unfold expect
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ (by exact_mod_cast hcard) c

/-- `expect` is additive. -/
private lemma expect_add {n m : ℕ} (f g : SubsetsOfCard n m → ℝ) :
    expect (fun s => f s + g s) = expect f + expect g := by
  unfold expect; rw [Finset.sum_add_distrib, mul_add]

/-- `expect` is subtractive. -/
private lemma expect_sub {n m : ℕ} (f g : SubsetsOfCard n m → ℝ) :
    expect (fun s => f s - g s) = expect f - expect g := by
  unfold expect; rw [Finset.sum_sub_distrib, mul_sub]

/-- `expect` pulls out a scalar. -/
private lemma expect_smul {n m : ℕ} (a : ℝ) (f : SubsetsOfCard n m → ℝ) :
    expect (fun s => a * f s) = a * expect f := by
  unfold expect; rw [← Finset.mul_sum]; ring

/-- `expect` commutes with a finite sum. -/
private lemma expect_sum {n m : ℕ} {ι : Type*} (t : Finset ι)
    (g : ι → SubsetsOfCard n m → ℝ) :
    expect (fun s => ∑ i ∈ t, g i s) = ∑ i ∈ t, expect (g i) := by
  unfold expect
  conv_rhs => rw [← Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The `m`-subsets of `Fin n` containing a fixed index `i` number `binom(n-1, m-1)`. -/
private lemma card_filter_one {n m : ℕ} (hm1 : 1 ≤ m) (i : Fin n) :
    ((Finset.powersetCard m (Finset.univ : Finset (Fin n))).filter
        (fun s => i ∈ s)).card = (n - 1).choose (m - 1) := by
  have hcard : (Finset.univ.erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  rw [← hcard, ← Finset.card_powersetCard (m - 1) (Finset.univ.erase i)]
  refine Finset.card_bij' (fun s _ => s.erase i) (fun t _ => insert i t) ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hs
    obtain ⟨⟨_, hsc⟩, hi⟩ := hs
    rw [Finset.mem_powersetCard]
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [Finset.mem_erase] at hx ⊢
      exact ⟨hx.1, Finset.mem_univ x⟩
    · rw [Finset.card_erase_of_mem hi, hsc]
  · intro t ht
    rw [Finset.mem_powersetCard] at ht
    obtain ⟨htsub, htc⟩ := ht
    have hint : i ∉ t := fun h => (Finset.mem_erase.mp (htsub h)).1 rfl
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.mem_insert_self i t⟩
    rw [Finset.card_insert_of_notMem hint, htc, Nat.sub_add_cancel hm1]
  · intro s hs
    rw [Finset.mem_filter] at hs
    exact Finset.insert_erase hs.2
  · intro t ht
    rw [Finset.mem_powersetCard] at ht
    have hint : i ∉ t := fun h => (Finset.mem_erase.mp (ht.1 h)).1 rfl
    exact Finset.erase_insert hint

/-- The `m`-subsets containing two fixed distinct indices number `binom(n-2, m-2)`. -/
private lemma card_filter_two {n m : ℕ} (hm2 : 2 ≤ m) {i j : Fin n} (hij : i ≠ j) :
    ((Finset.powersetCard m (Finset.univ : Finset (Fin n))).filter
        (fun s => i ∈ s ∧ j ∈ s)).card = (n - 2).choose (m - 2) := by
  have hj' : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hbase : ((Finset.univ.erase i).erase j).card = n - 2 := by
    rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin]
    omega
  rw [← hbase, ← Finset.card_powersetCard (m - 2) ((Finset.univ.erase i).erase j)]
  refine Finset.card_bij' (fun s _ => (s.erase i).erase j)
    (fun t _ => insert i (insert j t)) ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hs
    obtain ⟨⟨_, hsc⟩, hi, hjs⟩ := hs
    rw [Finset.mem_powersetCard]
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [Finset.mem_erase, Finset.mem_erase] at hx
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨hx.1, hx.2.1, Finset.mem_univ x⟩
    · rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, hjs⟩),
          Finset.card_erase_of_mem hi, hsc]
      omega
  · intro t ht
    rw [Finset.mem_powersetCard] at ht
    obtain ⟨htsub, htc⟩ := ht
    have hjt : j ∉ t := fun h => (Finset.mem_erase.mp (htsub h)).1 rfl
    have hit : i ∉ t := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp (htsub h)).2).1 rfl
    have hijt : i ∉ insert j t := by
      rw [Finset.mem_insert]; push_neg; exact ⟨hij, hit⟩
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩,
      Finset.mem_insert_self i _, Finset.mem_insert_of_mem (Finset.mem_insert_self j t)⟩
    rw [Finset.card_insert_of_notMem hijt, Finset.card_insert_of_notMem hjt, htc]
    omega
  · intro s hs
    rw [Finset.mem_filter] at hs
    obtain ⟨_, hi, hjs⟩ := hs
    simp only [Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hij, hjs⟩),
      Finset.insert_erase hi]
  · intro t ht
    rw [Finset.mem_powersetCard] at ht
    have hjt : j ∉ t := fun h => (Finset.mem_erase.mp (ht.1 h)).1 rfl
    have hit : i ∉ t := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp (ht.1 h)).2).1 rfl
    have hijt : i ∉ insert j t := by
      rw [Finset.mem_insert]; push_neg; exact ⟨hij, hit⟩
    simp only [Finset.erase_insert hijt, Finset.erase_insert hjt]

/-- `expect` is the expectation under the uniform law on splits: each of the
`binom(n, m)` splits carries mass `binom(n, m)⁻¹`. -/
lemma expect_eq_sum_uniform {n m : ℕ} [Nonempty (SubsetsOfCard n m)]
    (f : SubsetsOfCard n m → ℝ) :
    expect f = ∑ s, (sampleUnif n m s).toReal * f s := by
  unfold expect sampleUnif
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **First moment**: `E Wᵢ = m/n`. Counting: the `m`-subsets containing a fixed index are
`binom(n-1, m-1)` out of `binom(n, m)`. -/
theorem expect_weight {n m : ℕ}
    -- USER-INPUT: the split exists (for `m > n` the sample space is empty).
    (hm : m ≤ n) (i : Fin n) :
    expect (fun s : SubsetsOfCard n m => weight i s) = (m : ℝ) / n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · have h0 : (fun s : SubsetsOfCard n 0 => weight i s) = fun _ => (0 : ℝ) := by
      funext s
      have he : s.val = ∅ := Finset.card_eq_zero.mp s.2
      simp [weight, he]
    rw [h0, expect_const (Nat.zero_le n), Nat.cast_zero, zero_div]
  · have hnpos : 0 < n := lt_of_lt_of_le hm1 hm
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have hcm : (n.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
    have e1 : (n : ℝ) * ((n - 1).choose (m - 1) : ℝ) = (n.choose m : ℝ) * m := by
      obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have h := Nat.add_one_mul_choose_eq a b
      exact_mod_cast h
    rw [show (fun s : SubsetsOfCard n m => weight i s)
          = (fun s => (fun t => if i ∈ t then (1 : ℝ) else 0) s.val) from rfl,
      expect_eq_powersetCard (fun t => if i ∈ t then (1 : ℝ) else 0)]
    simp only [Finset.sum_boole, card_filter_one hm1 i]
    rw [inv_mul_eq_div, div_eq_div_iff hcm hn0]
    linear_combination e1

/-- **Second cross moment**: for `i ≠ j`, `E WᵢWⱼ = m(m-1)/(n(n-1))`. Counting: the
`m`-subsets containing two fixed indices are `binom(n-2, m-2)` out of `binom(n, m)`. -/
theorem expect_weight_pair {n m : ℕ}
    -- USER-INPUT: the split exists.
    (hm : m ≤ n) {i j : Fin n}
    -- USER-INPUT: two distinct items (this already forces `2 ≤ n`).
    (hij : i ≠ j) :
    expect (fun s : SubsetsOfCard n m => weight i s * weight j s)
      = ((m : ℝ) * ((m : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hijv : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hn2 : 2 ≤ n := by have := i.isLt; have := j.isLt; omega
  rcases lt_or_ge m 2 with hm2 | hm2
  · have h0 : (fun s : SubsetsOfCard n m => weight i s * weight j s) = fun _ => (0 : ℝ) := by
      funext s
      by_cases hi : i ∈ s.val
      · by_cases hj : j ∈ s.val
        · exfalso
          have hsub : ({i, j} : Finset (Fin n)) ⊆ s.val := by
            intro x hx
            rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> assumption
          have : 2 ≤ s.val.card := by
            rw [← Finset.card_pair hij]; exact Finset.card_le_card hsub
          rw [s.2] at this; omega
        · simp [weight, hj]
      · simp [weight, hi]
    rw [h0, expect_const hm]
    have hnum : (m : ℝ) * ((m : ℝ) - 1) = 0 := by interval_cases m <;> norm_num
    rw [hnum, zero_div]
  · have hcm : (n.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hn0 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n).ne'
    have hn1 : (n : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - 1).ne'
    have key : (n : ℝ) * ((n : ℝ) - 1) * ((n - 2).choose (m - 2) : ℝ)
        = (m : ℝ) * ((m : ℝ) - 1) * (n.choose m : ℝ) := by
      obtain ⟨a, rfl⟩ : ∃ a, n = a + 2 := ⟨n - 2, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, m = b + 2 := ⟨m - 2, by omega⟩
      simp only [Nat.add_sub_cancel]
      have h1 := Nat.add_one_mul_choose_eq (a + 1) (b + 1)
      have h2 := Nat.add_one_mul_choose_eq a b
      have h1' : ((a + 2 : ℕ) : ℝ) * ((a + 1).choose (b + 1) : ℝ)
          = ((a + 2).choose (b + 2) : ℝ) * ((b + 2 : ℕ) : ℝ) := by exact_mod_cast h1
      have h2' : ((a + 1 : ℕ) : ℝ) * (a.choose b : ℝ)
          = ((a + 1).choose (b + 1) : ℝ) * ((b + 1 : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at h1' h2' ⊢
      linear_combination ((a : ℝ) + 2) * h2' + ((b : ℝ) + 1) * h1'
    have hfun : (fun s : SubsetsOfCard n m => weight i s * weight j s)
        = fun s => (fun t => if i ∈ t ∧ j ∈ t then (1 : ℝ) else 0) s.val := by
      funext s
      simp only [weight]
      by_cases hi : i ∈ s.val <;> by_cases hj : j ∈ s.val <;> simp [hi, hj]
    rw [hfun, expect_eq_powersetCard (fun t => if i ∈ t ∧ j ∈ t then (1 : ℝ) else 0)]
    simp only [Finset.sum_boole, card_filter_two hm2 hij]
    rw [inv_mul_eq_div, div_eq_div_iff hcm (mul_ne_zero hn0 hn1)]
    linear_combination key

/-- **Negative correlation**: for `i ≠ j`,
`Cov(Wᵢ, Wⱼ) = −m(n−m)/(n²(n−1))`.
Immediate from `expect_weight` and `expect_weight_pair`; the sign reflects the constraint
`∑ᵢ Wᵢ = m`. -/
theorem cov_weight {n m : ℕ}
    -- USER-INPUT: the split exists.
    (hm : m ≤ n) {i j : Fin n}
    -- USER-INPUT: two distinct items.
    (hij : i ≠ j) :
    expect (fun s : SubsetsOfCard n m => weight i s * weight j s)
        - expect (fun s : SubsetsOfCard n m => weight i s)
          * expect (fun s : SubsetsOfCard n m => weight j s)
      = -((m : ℝ) * ((n : ℝ) - m)) / ((n : ℝ) ^ 2 * ((n : ℝ) - 1)) := by
  have hijv : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hn2 : 2 ≤ n := by have := i.isLt; have := j.isLt; omega
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n).ne'
  have hn1 : (n : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - 1).ne'
  rw [expect_weight_pair hm hij, expect_weight hm i, expect_weight hm j]
  field_simp
  ring

/-- **Exact variance of a linear statistic.** For deterministic coefficients `c` with mean
`c̄ = n⁻¹ ∑ᵢ cᵢ`,
$$\operatorname{Var}\Bigl(\sum_i c_i W_i\Bigr)
  = \frac{m(n-m)}{n(n-1)} \sum_i (c_i - \bar c)^2 .$$
Expanding the square and substituting the variance `p(1-p)` on the diagonal and
`cov_weight` off it; the cross terms reassemble into the centred sum of squares. Both
degenerate splits `m = 0` and `m = n` give variance `0`, as they must. -/
theorem var_linear {n m : ℕ}
    -- USER-INPUT: the split exists.
    (hm : m ≤ n)
    -- USER-INPUT: at least two items (the factor `n - 1` is a denominator).
    (hn : 2 ≤ n) (c : Fin n → ℝ) :
    expect (fun s : SubsetsOfCard n m =>
        ((∑ i, c i * weight i s)
          - expect (fun s' : SubsetsOfCard n m => ∑ i, c i * weight i s')) ^ 2)
      = ((m : ℝ) * ((n : ℝ) - m)) / ((n : ℝ) * ((n : ℝ) - 1))
          * ∑ i, (c i - (n : ℝ)⁻¹ * ∑ j, c j) ^ 2 := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n).ne'
  have hn1 : (n : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - 1).ne'
  -- The centred mean of `∑ cᵢWᵢ`.
  have hEY : expect (fun s' : SubsetsOfCard n m => ∑ i, c i * weight i s')
      = ∑ i, c i * ((m : ℝ) / n) := by
    rw [expect_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [expect_smul, expect_weight hm i]
  -- Expand the square of the centred statistic as a double sum.
  have hint : ∀ s : SubsetsOfCard n m,
      ((∑ i, c i * weight i s)
          - expect (fun s' : SubsetsOfCard n m => ∑ i, c i * weight i s')) ^ 2
        = ∑ i, ∑ j, (c i * (weight i s - (m : ℝ) / n)) * (c j * (weight j s - (m : ℝ) / n)) := by
    intro s
    rw [hEY, show (∑ i, c i * weight i s) - ∑ i, c i * ((m : ℝ) / n)
          = ∑ i, c i * (weight i s - (m : ℝ) / n) from by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring,
      sq, Finset.sum_mul_sum]
  -- Expectation of each cross term reduces to a pair moment.
  have hpair : ∀ i j : Fin n,
      expect (fun s : SubsetsOfCard n m =>
          (c i * (weight i s - (m : ℝ) / n)) * (c j * (weight j s - (m : ℝ) / n)))
        = c i * c j * (expect (fun s : SubsetsOfCard n m => weight i s * weight j s)
            - ((m : ℝ) / n) ^ 2) := by
    intro i j
    have hexp : (fun s : SubsetsOfCard n m =>
          (c i * (weight i s - (m : ℝ) / n)) * (c j * (weight j s - (m : ℝ) / n)))
        = fun s => c i * c j * (weight i s * weight j s)
            - c i * c j * ((m : ℝ) / n * weight i s) - c i * c j * ((m : ℝ) / n * weight j s)
            + c i * c j * ((m : ℝ) / n) ^ 2 := by
      funext s; ring
    rw [hexp]
    simp only [expect_add, expect_sub, expect_smul, expect_const hm, expect_weight hm]
    ring
  -- The paired expectations, `p` on the diagonal and `q` off it.
  have hEij : ∀ i j : Fin n, expect (fun s : SubsetsOfCard n m => weight i s * weight j s)
      = if i = j then (m : ℝ) / n
        else (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [if_pos rfl,
        show (fun s : SubsetsOfCard n m => weight i s * weight i s)
            = fun s => weight i s from by
            funext s; simp only [weight]; split_ifs <;> ring]
      exact expect_weight hm i
    · rw [if_neg h]; exact expect_weight_pair hm h
  -- The closed form of the resulting `if`-double sum.
  have hsum : ∀ p q : ℝ,
      ∑ i, ∑ j, c i * c j * ((if i = j then p else q) - p ^ 2)
        = (q - p ^ 2) * (∑ i, c i) ^ 2 + (p - q) * ∑ i, (c i) ^ 2 := by
    intro p q
    have hg : ∀ i j : Fin n, c i * c j * ((if i = j then p else q) - p ^ 2)
        = c i * c j * (q - p ^ 2) + (if i = j then c i * c j * (p - q) else 0) := by
      intro i j; by_cases h : i = j <;> simp [h] <;> ring
    have hA : ∑ i, ∑ j, c i * c j * (q - p ^ 2) = (q - p ^ 2) * (∑ i, c i) ^ 2 := by
      rw [pow_two (∑ i, c i), Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have hB : ∑ i, ∑ j : Fin n, (if i = j then c i * c j * (p - q) else 0)
        = (p - q) * ∑ i, (c i) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
      ring
    simp_rw [hg, Finset.sum_add_distrib]
    rw [hA, hB]
  -- The centred sum of squares in terms of raw power sums.
  have hVsum : ∑ i : Fin n, (c i - (n : ℝ)⁻¹ * ∑ j, c j) ^ 2
      = ∑ i, (c i) ^ 2 - (∑ i, c i) ^ 2 * (n : ℝ)⁻¹ := by
    have h1 : ∑ i : Fin n, (c i - (n : ℝ)⁻¹ * ∑ j, c j) ^ 2
        = ∑ i, ((c i) ^ 2 - 2 * ((n : ℝ)⁻¹ * ∑ j, c j) * c i + ((n : ℝ)⁻¹ * ∑ j, c j) ^ 2) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  -- Assemble.
  rw [congrArg expect (funext hint)]
  simp_rw [expect_sum, hpair, hEij]
  rw [hsum, hVsum]
  field_simp
  ring

/-- **`O(1/m)` variance bound for the group average.** With `s²_n = n⁻¹ ∑ᵢ (cᵢ - c̄)²` the
population dispersion of the coefficients,
$$\operatorname{Var}\Bigl(\frac 1m \sum_i c_i W_i\Bigr) \;\le\; \frac{2}{m}\, s^2_n .$$
From `var_linear`, since the finite-population factor `(n-m)/(n-1)` is at most `2` once
`n ≥ 2`. This is the form consumed by the permutation central limit theorem, where `s²_n`
stays bounded and the bound drives the negligibility of individual summands. -/
theorem var_mean_linear_le {n m : ℕ}
    -- USER-INPUT: a nonempty first group (the average divides by `m`).
    (hm0 : 0 < m)
    -- USER-INPUT: the split exists.
    (hm : m ≤ n)
    -- USER-INPUT: at least two items.
    (hn : 2 ≤ n) (c : Fin n → ℝ) :
    expect (fun s : SubsetsOfCard n m =>
        ((m : ℝ)⁻¹ * ((∑ i, c i * weight i s)
          - expect (fun s' : SubsetsOfCard n m => ∑ i, c i * weight i s'))) ^ 2)
      ≤ (2 / m) * ((n : ℝ)⁻¹ * ∑ i, (c i - (n : ℝ)⁻¹ * ∑ j, c j) ^ 2) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  have hnr2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := hmr.ne'
  have hn0ne : (n : ℝ) ≠ 0 := hn0.ne'
  have hn1ne : (n : ℝ) - 1 ≠ 0 := hn1.ne'
  have hV : 0 ≤ ∑ i, (c i - (n : ℝ)⁻¹ * ∑ j, c j) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  -- Pull out the `m⁻²` factor and invoke the exact variance identity.
  have hstep : expect (fun s : SubsetsOfCard n m =>
        ((m : ℝ)⁻¹ * ((∑ i, c i * weight i s)
          - expect (fun s' : SubsetsOfCard n m => ∑ i, c i * weight i s'))) ^ 2)
      = ((m : ℝ)⁻¹) ^ 2 * (((m : ℝ) * ((n : ℝ) - m) / ((n : ℝ) * ((n : ℝ) - 1)))
          * ∑ i, (c i - (n : ℝ)⁻¹ * ∑ j, c j) ^ 2) := by
    rw [show (fun s : SubsetsOfCard n m =>
            ((m : ℝ)⁻¹ * ((∑ i, c i * weight i s)
              - expect (fun s' : SubsetsOfCard n m => ∑ i, c i * weight i s'))) ^ 2)
          = (fun s => ((m : ℝ)⁻¹) ^ 2 * (((∑ i, c i * weight i s)
              - expect (fun s' : SubsetsOfCard n m => ∑ i, c i * weight i s')) ^ 2))
          from by funext s; ring,
      expect_smul, var_linear hm hn]
  rw [hstep]
  -- The finite-population factor `(n-m)/(n-1)` is at most `2`.
  have hcoef : ((m : ℝ)⁻¹) ^ 2 * ((m : ℝ) * ((n : ℝ) - m) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ (2 / m) * (n : ℝ)⁻¹ := by
    rw [show ((m : ℝ)⁻¹) ^ 2 * ((m : ℝ) * ((n : ℝ) - m) / ((n : ℝ) * ((n : ℝ) - 1)))
          = ((n : ℝ) - m) / ((m : ℝ) * ((n : ℝ) * ((n : ℝ) - 1))) from by field_simp,
      show (2 / (m : ℝ)) * (n : ℝ)⁻¹ = 2 / ((m : ℝ) * (n : ℝ)) from by field_simp,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hmr.le hn0.le)
      (show (0 : ℝ) ≤ (n : ℝ) + (m : ℝ) - 2 from by linarith)]
  calc ((m : ℝ)⁻¹) ^ 2 * (((m : ℝ) * ((n : ℝ) - m) / ((n : ℝ) * ((n : ℝ) - 1)))
          * ∑ i, (c i - (n : ℝ)⁻¹ * ∑ j, c j) ^ 2)
      = (((m : ℝ)⁻¹) ^ 2 * ((m : ℝ) * ((n : ℝ) - m) / ((n : ℝ) * ((n : ℝ) - 1))))
          * ∑ i, (c i - (n : ℝ)⁻¹ * ∑ j, c j) ^ 2 := by ring
    _ ≤ ((2 / m) * (n : ℝ)⁻¹) * ∑ i, (c i - (n : ℝ)⁻¹ * ∑ j, c j) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef hV
    _ = (2 / m) * ((n : ℝ)⁻¹ * ∑ i, (c i - (n : ℝ)⁻¹ * ∑ j, c j) ^ 2) := by ring

end StatLean.HypothesisTesting
