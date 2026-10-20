module
public import StatLean.HypothesisTesting.ForMathlib.PermutationMarginals
public import StatLean.HypothesisTesting.ForMathlib.SteinMethod
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CDF

@[expose] public section

/-!
# The combinatorial central limit theorem

Let `d : Fin N → ℝ` be a deterministic coefficient vector and let `a : Fin m → Fin N` pick out
`m` distinct positions. A uniform random permutation `σ` of `Fin N` relabels the positions,
and the **block sum**
$$ B_\sigma \;=\; \sum_{i < m} d\bigl(\sigma(a_i)\bigr) $$
is the sum of a *simple random sample of size `m` without replacement* from the finite
population `{d(1), …, d(N)}`. Every linear permutation statistic — in particular the
two-sample permutation statistic of `Randomization/TwoSamplePermutation` — is an affine
function of such a block sum.

The first two moments are elementary and are proved here from the one- and two-coordinate
marginals of `ForMathlib/PermutationMarginals`: for a **centred** population (`∑ d = 0`),
$$ \mathbb E\, B_\sigma = 0, \qquad
   \mathbb E\, B_\sigma^2 = \frac{m(N-m)}{N(N-1)} \sum_l d(l)^2 . $$
The **combinatorial central limit theorem** of Wald–Wolfowitz, Noether, Hoeffding, Erdős–Rényi
and Hájek says that the standardized block sum is asymptotically standard normal as soon as
both `m` and `N - m` tend to infinity and the population satisfies a Lindeberg-type condition;
that is `tendsto_perm_cdf_blockSum` below.

## Main results

* `sum_perm_inv` — a group average is unchanged by inverting the permutation. (The
  randomization action of `Randomization/TwoSamplePermutation` is `(σ • x) i = x (σ⁻¹ i)`,
  whereas the marginal bricks are written with `σ`; this is the bridge.)
* `avg_perm_blockSum` — the exact first moment of a block sum.
* `avg_perm_blockSum_sq` — the exact second moment of a **centred** block sum, i.e. the
  finite-population variance `m(N-m)/(N(N-1)) · ∑ d²`.
* `perm_avg_indicator_blockAvg_sub_mean_le` and its inverse-convention twin
  `perm_avg_indicator_blockAvg_inv_sub_mean_le` — the Chebyshev step for a block average of
  **uncentred** coefficients against the population mean.
* `avg_measureReal_eq_integral_avg_indicator` — Fubini for a finite group: the group average
  of deviation *probabilities* is the integral of the group average of the *indicators*.
* `blockSumScale` — the asymptotic standard deviation `√(m(N-m)/N)` used to standardize.
* `blockSet`, `SwapIndex`, `stdBlockSum`, `stdBlockSumSwap` — the **exchangeable pair** of
  Stein's method: swap one sampled position with one unsampled position.
* `sum_blockSet_mul_swap` and `stdBlockSumSwap_sub` — the increment of the pair.
* `sum_swap_exchangeable` — the pair is exchangeable.
* `sum_swapIndex_increment` and `sum_swapIndex_increment'` — the linearity condition, exactly,
  with `λ = N/(m(N-m))`.
* `sum_sq_swapIndex_increment` — the **conditional variance** of the pair, exactly:
  `∑ₖ (W' − W)² = u²(m ∑ d² + (N − 2m) A₂(σ) + 2 B(σ)²)`, which reduces the
  variance-regression defect of Stein's method to the concentration of the block sum of
  squares `A₂`; `avg_perm_blockSumSq` and `avg_perm_blockSet_sq` are the two moments that
  identity needs, and `avg_perm_sum_sq_swapIndex_increment` is its group average,
  `u² · 2m(N−m)/(N−1) · ∑ d²` — so at the Stein normalisation the variance-regression term
  is *exactly* centred at `(N−1)⁻¹ ∑ d² → 1`.
* `abs_avg_blockSum_sub_stdGaussianExpect_le` — a **Berry–Esseen-type bound at a fixed
  stage**: the group average of a bounded Lipschitz test function at a standardized block sum
  differs from its Gaussian expectation by an explicit finite-population quantity, a
  variance-regression term (second and fourth moments) plus a third-moment term.
* `tendsto_perm_avg_lipschitz` — the combinatorial CLT tested against bounded Lipschitz
  functions (the core analytic brick; proved from the previous one by truncating the
  population at Hájek's scale and letting the truncation level tend to `0`).
* `tendsto_perm_cdf_blockSum` — **the combinatorial central limit theorem**, derived from the
  previous one by the elementary ramp de-smoothing.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 12 (Extensions of the
CLT to Sums of Dependent Random Variables), §12.2 (Random Sampling Without Replacement from a
Finite Population), **Theorem 12.2.2** (Hájek's necessary and sufficient condition), and
Chapter 17 (Permutation and Randomization Tests), §17.3, where the theorem is applied to the
two-sample statistic. (`TSH4 §12.2 Thm 12.2.2`, `TSH4 §17.3`.) The fixed-stage Berry–Esseen
bound `abs_avg_blockSum_sub_stdGaussianExpect_le` is not in Lehmann–Romano: it specializes the
exchangeable-pair bound of L. H. Y. Chen, L. Goldstein and Q.-M. Shao, *Normal Approximation by
Stein's Method*, Springer, 2011, **Theorem 4.9** (loaded here from `ForMathlib/SteinMethod`), the
classical origin of combinatorial Berry–Esseen estimates being E. Bolthausen, *Z. Wahrsch. Verw.
Gebiete* **66** (1984), 379–386.

**Proof formalization notes.**
* *Which model.* Sampling without replacement has two equivalent carriers in this
  repository: the **subset** model of `ForMathlib/HypergeometricMoments` (uniform on
  `SubsetsOfCard N m`, average written `expect`) and the **permutation** model of
  `ForMathlib/PermutationMarginals` (uniform on `Equiv.Perm (Fin N)`, average written as an
  explicit normalized sum). This file uses the permutation model, because `randDist` and
  `randPairLaw` are *defined* as averages over the acting group, so no transfer lemma is
  needed at the point of use. The two moment computations below are the permutation-model
  twins of `HypergeometricMoments.expect_weight` and `HypergeometricMoments.var_linear`.
* *No factorial.* As in `PermutationMarginals`, the cardinality of the symmetric group is
  never computed; it cancels against itself through `avg_perm_apply` and
  `avg_perm_apply_pair`.
* *Standardization.* `blockSumScale N m = √(m(N-m)/N)` is the asymptotic standard deviation
  of a block sum whose population is normalized to `N⁻¹ ∑ d² → 1`; the exact standard
  deviation carries the extra finite-population factor `N/(N-1) · (N⁻¹ ∑ d²)`, which tends
  to `1` under the hypotheses of `tendsto_perm_cdf_blockSum` and would only clutter the
  statement. Both `m` and `N - m` are required to tend to infinity, which is necessary: for
  `m` bounded the block sum is a sum of boundedly many terms and has no normal limit, and the
  problem is symmetric under `m ↦ N - m` because `∑ d = 0` makes the two blocks negatives of
  each other.
* *Which Lindeberg condition.* The threshold is `ε √(min m (N-m))`, i.e. Hájek's condition,
  not `ε √N`. The two agree when `m/N` stays bounded away from `0` and `1` — which is the
  two-sample regime `m/n → λ ∈ (0, ∞)` — but Hájek's is the one that is also *necessary*, so
  it is the honest hypothesis to record.

**Bibliographic comments.** The theorem originates with A. Wald and J. Wolfowitz,
"Statistical tests based on permutations of the observations," *Ann. Math. Statist.* **15**
(1944), 358–372, who assumed all moments; G. E. Noether, "On a theorem of Pitman," *Ann.
Math. Statist.* **20** (1949), 455–458, and W. Hoeffding, "A combinatorial central limit
theorem," *Ann. Math. Statist.* **22** (1951), 558–566, reduced the hypotheses to conditions
on the fourth and second moments respectively. The definitive form — a Lindeberg condition
that is both necessary and sufficient for simple random sampling from a finite population —
is due to P. Erdős and A. Rényi, "On the central limit theorem for samples from a finite
population," *Publ. Math. Inst. Hungar. Acad. Sci.* **4** (1959), 49–61, and J. Hájek,
"Limiting distributions in simple random sampling from a finite population," *Publ. Math.
Inst. Hungar. Acad. Sci.* **5** (1960), 361–374. Modern proofs go through Stein's method for
exchangeable pairs (C. Stein, *Approximate Computation of Expectations*, IMS, 1986) or
through a coupling with the conditioned Bernoulli representation.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

/-! ### Inverting the permutation inside a group average -/

/-- A sum over a finite group is unchanged by inversion. The randomization action used by
`Randomization/TwoSamplePermutation` is `(σ • x) i = x (σ⁻¹ i)`, while the marginal bricks of
`ForMathlib/PermutationMarginals` are stated with `σ`; this lemma is the bridge, and it costs
nothing because inversion is a bijection of the group. -/
theorem sum_perm_inv {G : Type*} [Group G] [Fintype G] {M : Type*} [AddCommMonoid M]
    (f : G → M) : ∑ g : G, f g⁻¹ = ∑ g : G, f g :=
  Equiv.sum_comp (Equiv.inv G) f

/-! ### The first two moments of a block sum -/

/-- **First moment of a block sum.** Under a uniform random permutation each of the `m`
sampled positions is uniform on the `N` items, so the block sum has mean `m · N⁻¹ ∑ d`. No
injectivity of the block is needed: the first moment is additive. -/
theorem avg_perm_blockSum {N m : ℕ} (a : Fin m → Fin N) (d : Fin N → ℝ) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), ∑ i, d (σ (a i))
      = (m : ℝ) * ((N : ℝ)⁻¹ * ∑ l, d l) := by
  classical
  rw [Finset.sum_comm, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
    avg_perm_apply (a i) d]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Fintype.card_fin]

/-- **Second moment of a centred block sum** — the finite-population variance
$$ \frac1{|\mathbf S_N|}\sum_\sigma \Bigl(\sum_{i<m} d(\sigma(a_i))\Bigr)^2
   \;=\; \frac{m(N-m)}{N(N-1)} \sum_l d(l)^2 . $$
The `m` diagonal terms contribute `N⁻¹ ∑ d²` each and the `m(m-1)` off-diagonal ones
contribute `-(N(N-1))⁻¹ ∑ d²` each, by the one- and two-coordinate marginals; the negative
sign is the negative correlation forced by sampling without replacement. Both degenerate
blocks `m = 0` and `m = N` give variance `0`, as they must. -/
theorem avg_perm_blockSum_sq {N m : ℕ}
    -- USER-INPUT: at least two items (the factor `N - 1` is a denominator)
    (hN : 2 ≤ N)
    -- USER-INPUT: the block is a set of `m` distinct positions
    (a : Fin m → Fin N) (ha : Function.Injective a)
    -- USER-INPUT: centred coefficients
    (d : Fin N → ℝ) (hd : ∑ l, d l = 0) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), (∑ i, d (σ (a i))) ^ 2
      = (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * ∑ l, d l ^ 2 := by
  classical
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  set S₂ : ℝ := ∑ l, d l ^ 2 with hS₂
  -- expand the square into a double sum over block positions
  have hexpand : ∀ σ : Equiv.Perm (Fin N), (∑ i, d (σ (a i))) ^ 2
      = ∑ i : Fin m, ∑ j : Fin m, d (σ (a i)) * d (σ (a j)) := by
    intro σ
    rw [sq (∑ i, d (σ (a i))), Finset.sum_mul_sum]
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
  have hswap : ∑ σ : Equiv.Perm (Fin N), (∑ i, d (σ (a i))) ^ 2
      = ∑ σ : Equiv.Perm (Fin N), ∑ i : Fin m, ∑ j : Fin m, d (σ (a i)) * d (σ (a j)) :=
    Finset.sum_congr rfl fun σ _ => hexpand σ
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
  rw [hswap, hexch]
  -- the closed form of the double sum
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
  field_simp
  ring

/-! ### Chebyshev for a block average, with uncentred coefficients

`PermutationMarginals.perm_avg_indicator_blockAvg_le` is stated for an already-centred
coefficient vector, which is the form in which the variance identity is cleanest. Consumers,
however, arrive with a raw vector `c` — the pooled data, or a function of it — and want to
compare its block average against its *population* average `c̄ = N⁻¹ ∑ c`. Recentring is a
one-line shift, recorded here once so that the studentized-scale arguments do not each
repeat it. -/

/-- **Chebyshev for a block average against the population mean.** Under a uniform random
permutation, the fraction of permutations whose block average of `c` deviates from
`c̄ = N⁻¹ ∑ c` by `ε` is at most `ε⁻² (1/m) (N⁻¹ ∑ (c - c̄)²)` — the population dispersion
divided by the block size, exactly as for sampling with replacement, the finite-population
correction having been discarded. -/
theorem perm_avg_indicator_blockAvg_sub_mean_le {N m : ℕ}
    -- USER-INPUT: a nonempty block (the average divides by `m`)
    (hm : 0 < m)
    -- USER-INPUT: at least two items (the factor `N - 1` is a denominator upstream)
    (hN : 2 ≤ N)
    -- USER-INPUT: the block is a set of `m` distinct positions
    (a : Fin m → Fin N) (ha : Function.Injective a) (c : Fin N → ℝ) {ε : ℝ}
    -- USER-INPUT: a positive deviation
    (hε : 0 < ε) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N),
          (if ε ≤ |(m : ℝ)⁻¹ * (∑ i, c (σ (a i))) - (N : ℝ)⁻¹ * ∑ l, c l|
            then (1 : ℝ) else 0)
      ≤ ε⁻¹ ^ 2 * ((m : ℝ)⁻¹ *
          ((N : ℝ)⁻¹ * ∑ l, (c l - (N : ℝ)⁻¹ * ∑ l', c l') ^ 2)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hd : ∑ l, (c l - (N : ℝ)⁻¹ * ∑ l', c l') = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul, sub_self]
  have hshift : ∀ σ : Equiv.Perm (Fin N),
      (m : ℝ)⁻¹ * ∑ i, (c (σ (a i)) - (N : ℝ)⁻¹ * ∑ l', c l')
        = (m : ℝ)⁻¹ * (∑ i, c (σ (a i))) - (N : ℝ)⁻¹ * ∑ l, c l := by
    intro σ
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hmR.ne', one_mul]
  have h := perm_avg_indicator_blockAvg_le hm hN a ha
    (fun l => c l - (N : ℝ)⁻¹ * ∑ l', c l') hd hε
  simp only [hshift] at h
  exact h

/-- The same bound for the *inverse* convention `x ∘ σ⁻¹`, which is how the randomization
action of `Randomization/TwoSamplePermutation` relabels coordinates. -/
theorem perm_avg_indicator_blockAvg_inv_sub_mean_le {N m : ℕ} (hm : 0 < m) (hN : 2 ≤ N)
    (a : Fin m → Fin N) (ha : Function.Injective a) (c : Fin N → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N),
          (if ε ≤ |(m : ℝ)⁻¹ * (∑ i, c (σ⁻¹ (a i))) - (N : ℝ)⁻¹ * ∑ l, c l|
            then (1 : ℝ) else 0)
      ≤ ε⁻¹ ^ 2 * ((m : ℝ)⁻¹ *
          ((N : ℝ)⁻¹ * ∑ l, (c l - (N : ℝ)⁻¹ * ∑ l', c l') ^ 2)) := by
  rw [sum_perm_inv (G := Equiv.Perm (Fin N))
    (f := fun σ : Equiv.Perm (Fin N) =>
      if ε ≤ |(m : ℝ)⁻¹ * (∑ i, c (σ (a i))) - (N : ℝ)⁻¹ * ∑ l, c l| then (1 : ℝ) else 0)]
  exact perm_avg_indicator_blockAvg_sub_mean_le hm hN a ha c hε

/-! ### From permutation averages to randomization probabilities

The bounds above are pointwise in the data: they control the group average of an *indicator*
at a fixed data vector. The hypotheses consumed by the randomization theory
(`TendstoInProbRandomized`, and the `hrem` hypotheses of the Slutsky transfers) are group
averages of *probabilities*. The two are exchanged by Fubini for a finite group, which is
the following identity — the only step needed to turn `perm_avg_indicator_blockAvg_..._le`
into a statement about the data law. -/

/-- **Fubini for a finite group average of deviation probabilities.** The group average of
`P{ε ≤ A g}` is the `P`-integral of the group average of the indicators. Only measurability
of each `A g` is required; the group being finite, the sum is a finite one and no product
measure is involved. -/
theorem avg_measureReal_eq_integral_avg_indicator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (P : Measure 𝓨) [IsProbabilityMeasure P] {G : Type*} [Fintype G]
    (A : G → 𝓨 → ℝ) (hA : ∀ g, Measurable (A g)) (ε : ℝ) :
    (Fintype.card G : ℝ)⁻¹ * ∑ g : G, P.real {x | ε ≤ A g x}
      = ∫ x, (Fintype.card G : ℝ)⁻¹ * ∑ g : G, (if ε ≤ A g x then (1 : ℝ) else 0) ∂P := by
  classical
  have hset : ∀ g : G, MeasurableSet {x : 𝓨 | ε ≤ A g x} :=
    fun g => measurableSet_le measurable_const (hA g)
  have hind : ∀ g : G, (fun x => if ε ≤ A g x then (1 : ℝ) else 0)
      = Set.indicator {x | ε ≤ A g x} 1 := by
    intro g; funext x; simp [Set.indicator_apply]
  have hint : ∀ g : G, Integrable (fun x => if ε ≤ A g x then (1 : ℝ) else 0) P := by
    intro g
    rw [hind g]
    exact (integrable_const (1 : ℝ)).indicator (hset g)
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun g _ => hint g)]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hind g, integral_indicator_one (hset g)]

/-! ### The exchangeable pair of Stein's method

The modern proof of the combinatorial CLT builds an **exchangeable pair** out of a single
elementary move: pick one sampled position and one unsampled position uniformly at random and
interchange them. The three facts that Stein's method consumes — the increment formula, the
exchangeability, and the exact linearity of the conditional drift — are proved here; they are
all purely combinatorial, and together they instantiate the abstract engine
`ForMathlib/SteinMethod.abs_avg_sub_le` at `Ω = Equiv.Perm (Fin N)` and
`K = SwapIndex a`. -/

section SwapPair

variable {N m : ℕ}

/-- The set of **sampled positions** of a block `a`. -/
def blockSet (a : Fin m → Fin N) : Finset (Fin N) := Finset.image a Finset.univ

/-- A sum over the sampled *set* is a sum over the block *index*, the block being injective. -/
theorem sum_blockSet (a : Fin m → Fin N) (ha : Function.Injective a) (g : Fin N → ℝ) :
    ∑ p ∈ blockSet a, g p = ∑ i, g (a i) := by
  classical
  rw [blockSet, Finset.sum_image fun i _ j _ hij => ha hij]

/-- The sampled set has exactly `m` elements. -/
theorem card_blockSet (a : Fin m → Fin N) (ha : Function.Injective a) :
    (blockSet a).card = m := by
  classical
  rw [blockSet, Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]

/-- The **swap index**: an ordered pair consisting of one sampled and one unsampled position.
Interchanging the two is the elementary move that generates the exchangeable pair. There are
exactly `m (N - m)` of them. -/
abbrev SwapIndex (a : Fin m → Fin N) : Type :=
  {p : Fin N // p ∈ blockSet a} × {q : Fin N // q ∈ (blockSet a)ᶜ}

/-- The number of elementary swaps is `m (N - m)`. -/
theorem card_swapIndex (a : Fin m → Fin N) (ha : Function.Injective a) :
    Fintype.card (SwapIndex a) = m * (N - m) := by
  classical
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, Finset.card_compl,
    card_blockSet a ha, Fintype.card_fin]

/-- The **standardized block sum**, as a function on the acting group: `u` is the reciprocal
of the standardizing scale. -/
noncomputable def stdBlockSum (a : Fin m → Fin N) (d : Fin N → ℝ) (u : ℝ)
    (σ : Equiv.Perm (Fin N)) : ℝ := u * ∑ r ∈ blockSet a, d (σ r)

/-- The second coordinate of the exchangeable pair: the standardized block sum after the
elementary swap `k` has been applied to the positions. -/
noncomputable def stdBlockSumSwap (a : Fin m → Fin N) (d : Fin N → ℝ) (u : ℝ)
    (σ : Equiv.Perm (Fin N)) (k : SwapIndex a) : ℝ :=
  stdBlockSum a d u (σ * Equiv.swap k.1.1 k.2.1)

/-- **The elementary swap moves exactly one summand.** Interchanging a sampled position `p`
with an unsampled position `q` removes `d(σ p)` from the block sum and inserts `d(σ q)`. -/
theorem sum_blockSet_mul_swap (a : Fin m → Fin N) (d : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    {p q : Fin N} (hp : p ∈ blockSet a) (hq : q ∈ (blockSet a)ᶜ) :
    ∑ r ∈ blockSet a, d ((σ * Equiv.swap p q) r)
      = (∑ r ∈ blockSet a, d (σ r)) - d (σ p) + d (σ q) := by
  classical
  rw [Finset.mem_compl] at hq
  rw [← Finset.add_sum_erase _ (fun r => d ((σ * Equiv.swap p q) r)) hp,
    ← Finset.add_sum_erase _ (fun r => d (σ r)) hp]
  have h1 : d ((σ * Equiv.swap p q) p) = d (σ q) := by
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have h2 : ∀ r ∈ (blockSet a).erase p, d ((σ * Equiv.swap p q) r) = d (σ r) := by
    intro r hr
    have hrp : r ≠ p := (Finset.mem_erase.1 hr).1
    have hrq : r ≠ q := fun hcon => hq (hcon ▸ (Finset.mem_erase.1 hr).2)
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hrp hrq]
  rw [h1, Finset.sum_congr rfl h2]
  ring

/-- **The increment of the exchangeable pair.** -/
theorem stdBlockSumSwap_sub (a : Fin m → Fin N) (d : Fin N → ℝ) (u : ℝ)
    (σ : Equiv.Perm (Fin N)) (k : SwapIndex a) :
    stdBlockSumSwap a d u σ k - stdBlockSum a d u σ = u * (d (σ k.2.1) - d (σ k.1.1)) := by
  rw [stdBlockSumSwap, stdBlockSum, stdBlockSum, sum_blockSet_mul_swap a d σ k.1.2 k.2.2]
  ring

/-- **Exchangeability of the swap pair.** For every test function `F` of two variables the
total sum over the group and the swap index is unchanged when the two coordinates of the pair
are interchanged. The proof is a reindexing of the group by right multiplication with the
transposition, which is an involution: `(σ s) s = σ`. -/
theorem sum_swap_exchangeable (a : Fin m → Fin N) (d : Fin N → ℝ) (u : ℝ) (F : ℝ → ℝ → ℝ) :
    ∑ σ : Equiv.Perm (Fin N), ∑ k : SwapIndex a,
        F (stdBlockSum a d u σ) (stdBlockSumSwap a d u σ k)
      = ∑ σ : Equiv.Perm (Fin N), ∑ k : SwapIndex a,
        F (stdBlockSumSwap a d u σ k) (stdBlockSum a d u σ) := by
  classical
  have main : ∀ k : SwapIndex a,
      ∑ σ : Equiv.Perm (Fin N), F (stdBlockSum a d u σ) (stdBlockSumSwap a d u σ k)
        = ∑ σ : Equiv.Perm (Fin N), F (stdBlockSumSwap a d u σ k) (stdBlockSum a d u σ) := by
    intro k
    set s : Equiv.Perm (Fin N) := Equiv.swap k.1.1 k.2.1 with hs
    have hss : s * s = 1 := Equiv.swap_mul_self _ _
    have key := Equiv.sum_comp (Equiv.mulRight s)
      (fun σ : Equiv.Perm (Fin N) =>
        F (stdBlockSum a d u σ) (stdBlockSum a d u (σ * s)))
    simp only [Equiv.coe_mulRight, mul_assoc, hss, mul_one] at key
    exact key.symm
  calc ∑ σ : Equiv.Perm (Fin N), ∑ k : SwapIndex a,
          F (stdBlockSum a d u σ) (stdBlockSumSwap a d u σ k)
      = ∑ k : SwapIndex a, ∑ σ : Equiv.Perm (Fin N),
          F (stdBlockSum a d u σ) (stdBlockSumSwap a d u σ k) := Finset.sum_comm
    _ = ∑ k : SwapIndex a, ∑ σ : Equiv.Perm (Fin N),
          F (stdBlockSumSwap a d u σ k) (stdBlockSum a d u σ) :=
        Finset.sum_congr rfl fun k _ => main k
    _ = _ := Finset.sum_comm

/-- **The linearity condition, exactly.** For a *centred* population the conditional drift of
the swap pair is proportional to the current value:
`∑ₖ (W' σ k − W σ) = -N · W σ`, i.e. `𝔼[W' − W ∣ σ] = -λ W σ` with

`λ = N / (m (N − m))`,

since there are `m (N − m)` elementary swaps. (The wave-6 status note of
`tendsto_perm_cdf_blockSum` recorded `λ = 1/(m(N-m))`; the correct value carries the extra
factor `N`, as the computation below shows.) -/
theorem sum_swapIndex_increment (a : Fin m → Fin N) (ha : Function.Injective a)
    (d : Fin N → ℝ) (hd : ∑ l, d l = 0) (u : ℝ) (σ : Equiv.Perm (Fin N)) :
    ∑ k : SwapIndex a, (stdBlockSumSwap a d u σ k - stdBlockSum a d u σ)
      = -(N : ℝ) * stdBlockSum a d u σ := by
  classical
  have hmN : m ≤ N := by
    have := card_blockSet a ha ▸ Finset.card_le_univ (blockSet a)
    simpa using this
  have htot : ∑ r : Fin N, d (σ r) = 0 := by rw [Equiv.sum_comp σ d]; exact hd
  have hsplit := Finset.sum_add_sum_compl (blockSet a) (fun r => d (σ r))
  have hcompl : ∑ r ∈ (blockSet a)ᶜ, d (σ r) = -∑ r ∈ blockSet a, d (σ r) := by
    rw [htot] at hsplit; linarith
  have hcardc : ((blockSet a)ᶜ.card : ℝ) = (N : ℝ) - m := by
    rw [Finset.card_compl, card_blockSet a ha, Fintype.card_fin,
      Nat.cast_sub hmN]
  rw [Finset.sum_congr rfl fun k _ => stdBlockSumSwap_sub a d u σ k, Fintype.sum_prod_type]
  have hinner : ∀ p : {p : Fin N // p ∈ blockSet a},
      ∑ q : {q : Fin N // q ∈ (blockSet a)ᶜ}, u * (d (σ q.1) - d (σ p.1))
        = u * (-∑ r ∈ blockSet a, d (σ r)) - ((N : ℝ) - m) * (u * d (σ p.1)) := by
    intro p
    have hdist : ∀ q : {q : Fin N // q ∈ (blockSet a)ᶜ},
        u * (d (σ q.1) - d (σ p.1)) = u * d (σ q.1) - u * d (σ p.1) := fun q => by ring
    rw [Finset.sum_congr rfl fun q _ => hdist q, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, hcardc, ← Finset.mul_sum,
      Finset.sum_coe_sort (blockSet a)ᶜ (fun r => d (σ r)), hcompl]
  rw [Finset.sum_congr rfl fun p _ => hinner p, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, card_blockSet a ha, nsmul_eq_mul]
  have hlast : ∑ p : {p : Fin N // p ∈ blockSet a}, ((N : ℝ) - m) * (u * d (σ p.1))
      = ((N : ℝ) - m) * (u * ∑ r ∈ blockSet a, d (σ r)) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_coe_sort (blockSet a) (fun r => d (σ r))]
  rw [hlast, stdBlockSum]
  ring

/-- **The conditional variance of the swap pair, exactly.** For a *centred* population,
$$ \sum_k \bigl(W'(\sigma,k) - W(\sigma)\bigr)^2
   \;=\; u^2\Bigl( m\sum_l d_l^2 \;+\; (N - 2m)\,A_2(\sigma) \;+\; 2\,B(\sigma)^2 \Bigr), $$
where `A₂(σ) = ∑_{r ∈ blockSet a} d(σ r)²` is the block sum of squares and
`B(σ) = ∑_{r ∈ blockSet a} d(σ r) = u⁻¹ W(σ)` is the block sum itself. Expanding the square
of the increment `u(d(σq) − d(σp))` produces the three terms: the `m(N−m)` cross terms of
`∑_q d(σq)²` and `∑_p d(σp)²` are counted with multiplicities `m` and `N−m`, and the
`-2 ∑_p ∑_q d(σp)d(σq)` term collapses to `+2B(σ)²` because the complement of the block sums
to `-B(σ)`.

This is the identity that turns the variance-regression defect
`𝔼|1 − (2λ)⁻¹ ∑_k (W' − W)²|` of `SteinMethod.abs_avg_sub_le` into a statement about the
concentration of `A₂` alone: with `λ = N/(m(N−m))` and `u² = N/(m(N−m))` one gets
`(2λ)⁻¹∑_k (W' − W)² = ½(m N⁻¹ ∑ d² + (1 − 2m/N) A₂(σ) + 2N⁻¹ B(σ)²)`, and both `B(σ)²/N`
and the deviation of `A₂` from its mean `(m/N)∑d²` are second-order. -/
theorem sum_sq_swapIndex_increment (a : Fin m → Fin N) (ha : Function.Injective a)
    (d : Fin N → ℝ) (hd : ∑ l, d l = 0) (u : ℝ) (σ : Equiv.Perm (Fin N)) :
    ∑ k : SwapIndex a, (stdBlockSumSwap a d u σ k - stdBlockSum a d u σ) ^ 2
      = u ^ 2 * ((m : ℝ) * ∑ l, d l ^ 2
          + ((N : ℝ) - 2 * (m : ℝ)) * ∑ r ∈ blockSet a, d (σ r) ^ 2
          + 2 * (∑ r ∈ blockSet a, d (σ r)) ^ 2) := by
  classical
  have hmN : m ≤ N := by
    have := card_blockSet a ha ▸ Finset.card_le_univ (blockSet a)
    simpa using this
  have htot : ∑ r : Fin N, d (σ r) = 0 := by rw [Equiv.sum_comp σ d]; exact hd
  have htot2 : ∑ r : Fin N, d (σ r) ^ 2 = ∑ l, d l ^ 2 :=
    Equiv.sum_comp σ fun l => d l ^ 2
  have hs1 := Finset.sum_add_sum_compl (blockSet a) fun r => d (σ r)
  have hs2 := Finset.sum_add_sum_compl (blockSet a) fun r => d (σ r) ^ 2
  rw [htot] at hs1
  rw [htot2] at hs2
  have hcardc : ((blockSet a)ᶜ.card : ℝ) = (N : ℝ) - m := by
    rw [Finset.card_compl, card_blockSet a ha, Fintype.card_fin, Nat.cast_sub hmN]
  have hc1 : ∑ r ∈ (blockSet a)ᶜ, d (σ r) = -∑ r ∈ blockSet a, d (σ r) := by linarith
  have hc2 : ∑ r ∈ (blockSet a)ᶜ, d (σ r) ^ 2
      = (∑ l, d l ^ 2) - ∑ r ∈ blockSet a, d (σ r) ^ 2 := by linarith
  rw [Finset.sum_congr rfl fun k _ => by rw [stdBlockSumSwap_sub a d u σ k],
    Fintype.sum_prod_type]
  have hinner : ∀ p : {p : Fin N // p ∈ blockSet a},
      ∑ q : {q : Fin N // q ∈ (blockSet a)ᶜ}, (u * (d (σ q.1) - d (σ p.1))) ^ 2
        = u ^ 2 * ((∑ l, d l ^ 2) - ∑ r ∈ blockSet a, d (σ r) ^ 2)
          + (2 * u ^ 2 * (∑ r ∈ blockSet a, d (σ r))) * d (σ p.1)
          + (((N : ℝ) - m) * u ^ 2) * d (σ p.1) ^ 2 := by
    intro p
    have hexp : ∀ q : {q : Fin N // q ∈ (blockSet a)ᶜ},
        (u * (d (σ q.1) - d (σ p.1))) ^ 2
          = u ^ 2 * d (σ q.1) ^ 2 - 2 * (u ^ 2 * d (σ p.1)) * d (σ q.1)
            + u ^ 2 * d (σ p.1) ^ 2 := fun q => by ring
    rw [Finset.sum_congr rfl fun q _ => hexp q, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, hcardc,
      Finset.sum_coe_sort (blockSet a)ᶜ fun r => d (σ r) ^ 2,
      Finset.sum_coe_sort (blockSet a)ᶜ fun r => d (σ r), hc1, hc2]
    ring
  rw [Finset.sum_congr rfl fun p _ => hinner p, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    card_blockSet a ha, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_coe_sort (blockSet a) fun r => d (σ r),
    Finset.sum_coe_sort (blockSet a) fun r => d (σ r) ^ 2]
  ring

/-- The mean of the block sum of squares `A₂(σ) = ∑_{r ∈ blockSet a} d(σ r)²`, from the
one-coordinate marginal: each sampled position is uniform on the population. -/
theorem avg_perm_blockSumSq (a : Fin m → Fin N) (ha : Function.Injective a) (d : Fin N → ℝ) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), ∑ r ∈ blockSet a, d (σ r) ^ 2
      = (m : ℝ) * ((N : ℝ)⁻¹ * ∑ l, d l ^ 2) := by
  rw [Finset.sum_congr rfl fun σ _ => sum_blockSet a ha fun r => d (σ r) ^ 2]
  exact avg_perm_blockSum a fun l => d l ^ 2

/-- The second moment of the block sum, written over the sampled *set* rather than the block
*index* — the shape in which `sum_sq_swapIndex_increment` produces it. -/
theorem avg_perm_blockSet_sq (hN : 2 ≤ N) (a : Fin m → Fin N) (ha : Function.Injective a)
    (d : Fin N → ℝ) (hd : ∑ l, d l = 0) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), (∑ r ∈ blockSet a, d (σ r)) ^ 2
      = (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * ∑ l, d l ^ 2 := by
  rw [Finset.sum_congr rfl fun σ _ => by rw [sum_blockSet a ha fun r => d (σ r)]]
  exact avg_perm_blockSum_sq hN a ha d hd

/-- **The mean of the conditional variance of the swap pair, exactly.** Averaging
`sum_sq_swapIndex_increment` over the group and feeding in the two moment computations
`avg_perm_blockSumSq` and `avg_perm_blockSet_sq` collapses the three terms to a single one:
$$ \frac1{|\mathbf S_N|}\sum_\sigma \sum_k \bigl(W'(\sigma,k) - W(\sigma)\bigr)^2
   \;=\; u^2\,\frac{2m(N-m)}{N-1}\sum_l d_l^2 . $$
Consequently, with the Stein normalisation `λ = N/(m(N−m))` and `u² = N/(m(N−m))` the
variance-regression *centring* is exact:
`avg_σ (2λ)⁻¹ ∑ₖ (W' − W)² = (N − 1)⁻¹ ∑_l d_l²`, which tends to `1` precisely under the
hypothesis `N⁻¹ ∑ d² → 1` of `tendsto_perm_avg_lipschitz`. What is left of the
variance-regression term is therefore purely a *concentration* statement about `A₂`, i.e. a
fourth-moment computation, and not a centring one. -/
theorem avg_perm_sum_sq_swapIndex_increment (hN : 2 ≤ N) (a : Fin m → Fin N)
    (ha : Function.Injective a) (d : Fin N → ℝ) (hd : ∑ l, d l = 0) (u : ℝ) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N),
          ∑ k : SwapIndex a, (stdBlockSumSwap a d u σ k - stdBlockSum a d u σ) ^ 2
      = u ^ 2 * (2 * (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)) * ∑ l, d l ^ 2 := by
  classical
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hc : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hexp : ∑ σ : Equiv.Perm (Fin N),
      ∑ k : SwapIndex a, (stdBlockSumSwap a d u σ k - stdBlockSum a d u σ) ^ 2
      = ∑ σ : Equiv.Perm (Fin N), (u ^ 2 * ((m : ℝ) * ∑ l, d l ^ 2)
          + (u ^ 2 * ((N : ℝ) - 2 * (m : ℝ))) * ∑ r ∈ blockSet a, d (σ r) ^ 2
          + (2 * u ^ 2) * (∑ r ∈ blockSet a, d (σ r)) ^ 2) :=
    Finset.sum_congr rfl fun σ _ => by
      rw [sum_sq_swapIndex_increment a ha d hd u σ]; ring
  have hconst : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ _σ : Equiv.Perm (Fin N), u ^ 2 * ((m : ℝ) * ∑ l, d l ^ 2)
      = u ^ 2 * ((m : ℝ) * ∑ l, d l ^ 2) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hc.ne', one_mul]
  have hA := avg_perm_blockSumSq a ha d
  have hB := avg_perm_blockSet_sq hN a ha d hd
  rw [hexp, Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add, mul_add, hconst,
    ← Finset.mul_sum, ← Finset.mul_sum,
    show (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ((u ^ 2 * ((N : ℝ) - 2 * (m : ℝ)))
          * ∑ σ : Equiv.Perm (Fin N), ∑ r ∈ blockSet a, d (σ r) ^ 2)
      = (u ^ 2 * ((N : ℝ) - 2 * (m : ℝ)))
          * ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹
            * ∑ σ : Equiv.Perm (Fin N), ∑ r ∈ blockSet a, d (σ r) ^ 2) from by ring,
    show (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ((2 * u ^ 2) * ∑ σ : Equiv.Perm (Fin N), (∑ r ∈ blockSet a, d (σ r)) ^ 2)
      = (2 * u ^ 2) * ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹
            * ∑ σ : Equiv.Perm (Fin N), (∑ r ∈ blockSet a, d (σ r)) ^ 2) from by ring,
    hA, hB]
  field_simp
  ring

/-- The linearity condition in the exact shape consumed by
`ForMathlib/SteinMethod.abs_avg_sub_le`, with `λ = N / (m (N − m))`. -/
theorem sum_swapIndex_increment' (a : Fin m → Fin N) (ha : Function.Injective a)
    (hm : 0 < m) (hmN : m < N) (d : Fin N → ℝ) (hd : ∑ l, d l = 0) (u : ℝ)
    (σ : Equiv.Perm (Fin N)) :
    ∑ k : SwapIndex a, (stdBlockSumSwap a d u σ k - stdBlockSum a d u σ)
      = -((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) * (Fintype.card (SwapIndex a) : ℝ)
          * stdBlockSum a d u σ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNmR : (0 : ℝ) < (N : ℝ) - m := by
    have : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    linarith
  rw [sum_swapIndex_increment a ha d hd u σ, card_swapIndex a ha,
    Nat.cast_mul, Nat.cast_sub hmN.le]
  field_simp

end SwapPair

/-! ### Standardization and the central limit theorem -/

/-- The asymptotic standard deviation `√(m(N-m)/N)` of a block sum drawn from a population
normalized by `N⁻¹ ∑ d² = 1`. The exact standard deviation of `avg_perm_blockSum_sq` differs
by the factor `√(N/(N-1) · N⁻¹ ∑ d²)`, which tends to `1` in the regime of
`tendsto_perm_cdf_blockSum`. -/
noncomputable def blockSumScale (N m : ℕ) : ℝ := Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / (N : ℝ))

/-- To bound a square root it is enough to bound the radicand by a square. -/
private lemma sqrt_le_of_sq_le {x y : ℝ} (hy : 0 ≤ y) (hxy : x ≤ y ^ 2) :
    Real.sqrt x ≤ y := by
  calc Real.sqrt x ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt hxy
    _ = y := Real.sqrt_sq hy

/-- **Cauchy–Schwarz for a finite average**: the average of `|f|` is at most the square root
of the average of `f²`. -/
private lemma avg_abs_le_sqrt_avg_sq {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    (Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i|
      ≤ Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ^ 2) := by
  have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnn : (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i| :=
    mul_nonneg (inv_nonneg.2 hc.le) (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hcs : (∑ i, |f i|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, f i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => |f i|)
    simpa [Finset.card_univ, sq_abs] using h
  calc (Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i|
      = Real.sqrt (((Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i|) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [mul_pow]
        have hstep : ((Fintype.card ι : ℝ)⁻¹) ^ 2 * (∑ i, |f i|) ^ 2
            ≤ ((Fintype.card ι : ℝ)⁻¹) ^ 2 * ((Fintype.card ι : ℝ) * ∑ i, f i ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
        calc ((Fintype.card ι : ℝ)⁻¹) ^ 2 * (∑ i, |f i|) ^ 2
            ≤ ((Fintype.card ι : ℝ)⁻¹) ^ 2 * ((Fintype.card ι : ℝ) * ∑ i, f i ^ 2) := hstep
          _ = (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ^ 2 := by field_simp

/-- The elementary cube inequality `|x − y|³ ≤ 4(|x|³ + |y|³)`. -/
private lemma abs_sub_cube_le (x y : ℝ) : |x - y| ^ 3 ≤ 4 * (|x| ^ 3 + |y| ^ 3) := by
  have h1 : |x - y| ≤ |x| + |y| := by
    have h := abs_add_le x (-y)
    simpa [sub_eq_add_neg, abs_neg] using h
  have h2 : |x - y| ^ 3 ≤ (|x| + |y|) ^ 3 := by
    exact pow_le_pow_left₀ (abs_nonneg _) h1 3
  nlinarith [abs_nonneg x, abs_nonneg y,
    mul_nonneg (add_nonneg (abs_nonneg x) (abs_nonneg y)) (sq_nonneg (|x| - |y|))]

/-- `xy/(x+y) ≤ min x y`: the Stein scale is at most Hájek's scale. -/
private lemma mul_div_add_le_min {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * y / (x + y) ≤ min x y := by
  have hxy : (0 : ℝ) < x + y := by linarith
  refine le_min ?_ ?_
  · rw [div_le_iff₀ hxy]; nlinarith
  · rw [div_le_iff₀ hxy]; nlinarith

/-- `min x y ≤ 2 xy/(x+y)`: Hájek's scale is at most twice the Stein scale. -/
private lemma min_div_two_le_mul_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    min x y / 2 ≤ x * y / (x + y) := by
  have hxy : (0 : ℝ) < x + y := by linarith
  rw [div_le_div_iff₀ (by norm_num) hxy]
  rcases le_total x y with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

/-! ### The third-moment term of the swap pair -/

/-- **The third-moment term of the swap pair.** The increment of the swap pair is
`u (d(σq) − d(σp))`, so its cube is controlled by the third absolute moment of the population
alone: the average over the group *and* the swap index of `|W' − W|³` is at most
`8 |u|³ N⁻¹ ∑ |d|³`. Both `p` and `q` are single positions, so only the one-coordinate
marginal `avg_perm_apply` is used. -/
private lemma avg_cube_increment_le {N m : ℕ} (a : Fin m → Fin N) (ha : Function.Injective a)
    (hm : 0 < m) (hmN : m < N) (d : Fin N → ℝ) (u : ℝ) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ * (Fintype.card (SwapIndex a) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), ∑ k : SwapIndex a,
          |stdBlockSumSwap a d u σ k - stdBlockSum a d u σ| ^ 3
      ≤ 8 * |u| ^ 3 * ((N : ℝ)⁻¹ * ∑ l, |d l| ^ 3) := by
  classical
  have hcP : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcK : (0 : ℝ) < (Fintype.card (SwapIndex a) : ℝ) := by
    rw [card_swapIndex a ha]
    exact_mod_cast Nat.mul_pos hm (Nat.sub_pos_of_lt hmN)
  set T : ℝ := (N : ℝ)⁻¹ * ∑ l, |d l| ^ 3 with hT
  have h3 : (0 : ℝ) ≤ |u| ^ 3 := by positivity
  -- the bound for a single elementary swap
  have hper : ∀ k : SwapIndex a,
      (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N), |stdBlockSumSwap a d u σ k - stdBlockSum a d u σ| ^ 3
        ≤ 8 * |u| ^ 3 * T := by
    intro k
    have hb : ∀ σ : Equiv.Perm (Fin N),
        |stdBlockSumSwap a d u σ k - stdBlockSum a d u σ| ^ 3
          ≤ 4 * |u| ^ 3 * (|d (σ k.2.1)| ^ 3 + |d (σ k.1.1)| ^ 3) := by
      intro σ
      rw [stdBlockSumSwap_sub a d u σ k, abs_mul, mul_pow]
      calc |u| ^ 3 * |d (σ k.2.1) - d (σ k.1.1)| ^ 3
          ≤ |u| ^ 3 * (4 * (|d (σ k.2.1)| ^ 3 + |d (σ k.1.1)| ^ 3)) :=
            mul_le_mul_of_nonneg_left (abs_sub_cube_le _ _) h3
        _ = 4 * |u| ^ 3 * (|d (σ k.2.1)| ^ 3 + |d (σ k.1.1)| ^ 3) := by ring
    have hq := avg_perm_apply (α := Fin N) k.2.1 fun l => |d l| ^ 3
    have hp := avg_perm_apply (α := Fin N) k.1.1 fun l => |d l| ^ 3
    rw [Fintype.card_fin] at hq hp
    have hq' : ∑ σ : Equiv.Perm (Fin N), |d (σ k.2.1)| ^ 3
        = (Fintype.card (Equiv.Perm (Fin N)) : ℝ) * T := by
      rw [hT, ← hq, ← mul_assoc, mul_inv_cancel₀ hcP.ne', one_mul]
    have hp' : ∑ σ : Equiv.Perm (Fin N), |d (σ k.1.1)| ^ 3
        = (Fintype.card (Equiv.Perm (Fin N)) : ℝ) * T := by
      rw [hT, ← hp, ← mul_assoc, mul_inv_cancel₀ hcP.ne', one_mul]
    calc (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N), |stdBlockSumSwap a d u σ k - stdBlockSum a d u σ| ^ 3
        ≤ (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N),
              4 * |u| ^ 3 * (|d (σ k.2.1)| ^ 3 + |d (σ k.1.1)| ^ 3) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hb σ) (inv_nonneg.2 hcP.le)
      _ = 8 * |u| ^ 3 * T := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, hq', hp']
          field_simp
          ring
  -- average over the swap index
  have hswap : ∀ (c₁ c₂ : ℝ) (g : SwapIndex a → ℝ),
      c₁ * c₂ * ∑ k, g k = c₂ * ∑ k, c₁ * g k := by
    intro c₁ c₂ g
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  calc (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ * (Fintype.card (SwapIndex a) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N), ∑ k : SwapIndex a,
            |stdBlockSumSwap a d u σ k - stdBlockSum a d u σ| ^ 3
      = (Fintype.card (SwapIndex a) : ℝ)⁻¹ * ∑ k : SwapIndex a,
          ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N),
              |stdBlockSumSwap a d u σ k - stdBlockSum a d u σ| ^ 3) := by
        rw [Finset.sum_comm]; exact hswap _ _ _
    _ ≤ (Fintype.card (SwapIndex a) : ℝ)⁻¹ * ∑ _k : SwapIndex a, 8 * |u| ^ 3 * T :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hper k) (inv_nonneg.2 hcK.le)
    _ = 8 * |u| ^ 3 * T := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hcK.ne', one_mul]

/-! ### The variance-regression term of the swap pair -/

/-- **The variance-regression term of the swap pair.** With the Stein normalisation
`u² = λ = N/(m(N−m))`, the exact conditional variance `sum_sq_swapIndex_increment` gives
`(2λ)⁻¹ 𝔼[(W'−W)² ∣ σ] = (2m(N−m))⁻¹ (m ∑d² + (N−2m) A₂(σ) + 2 B(σ)²)`, whose group average is
`(N−1)⁻¹ ∑ d²` (`avg_perm_sum_sq_swapIndex_increment`). Subtracting the exact mean leaves two
fluctuations: that of the block sum of squares `A₂`, controlled by Cauchy–Schwarz and the
finite-population variance `avg_perm_blockSum_sq` applied to the *centred squares*
`d² − N⁻¹∑d²` — this is the fourth-moment input `∑ d⁴` — and that of `B²`, which is `O(1/N)`
in mean because `B` is the block sum itself. -/
private lemma avg_abs_one_sub_condSq_le {N m : ℕ} (hN : 2 ≤ N) (hm : 0 < m) (hmN : m < N)
    (a : Fin m → Fin N) (ha : Function.Injective a) (d : Fin N → ℝ) (hd : ∑ l, d l = 0)
    {u : ℝ} (hu2 : u ^ 2 = (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N),
          |1 - (2 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))))⁻¹ *
            condSqIncrement (stdBlockSum a d u) (stdBlockSumSwap a d u) σ|
      ≤ |1 - (∑ l, d l ^ 2) / ((N : ℝ) - 1)|
        + |(N : ℝ) - 2 * (m : ℝ)| / (2 * (m : ℝ) * ((N : ℝ) - m)) *
            Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * ∑ l, d l ^ 4)
        + 2 * (∑ l, d l ^ 2) / ((N : ℝ) * ((N : ℝ) - 1)) := by
  classical
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmNR : (0 : ℝ) < (N : ℝ) - (m : ℝ) := by
    have : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    linarith
  have hcP : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  set S₂ : ℝ := ∑ l, d l ^ 2 with hS₂
  set S₄ : ℝ := ∑ l, d l ^ 4 with hS₄
  have hS₂0 : (0 : ℝ) ≤ S₂ := Finset.sum_nonneg fun l _ => sq_nonneg _
  set AA : Equiv.Perm (Fin N) → ℝ := fun σ => ∑ r ∈ blockSet a, d (σ r) ^ 2 with hAA
  set BB : Equiv.Perm (Fin N) → ℝ := fun σ => ∑ r ∈ blockSet a, d (σ r) with hBB
  set c : ℝ := (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * S₂ with hc
  have hc0 : (0 : ℝ) ≤ c := by
    rw [hc]
    exact mul_nonneg (by positivity) hS₂0
  set coef₁ : ℝ := ((N : ℝ) - 2 * (m : ℝ)) / (2 * (m : ℝ) * ((N : ℝ) - m)) with hcoef₁
  set coef₂ : ℝ := ((m : ℝ) * ((N : ℝ) - m))⁻¹ with hcoef₂
  -- the exact pointwise decomposition of the variance-regression ratio
  have hXeq : ∀ σ : Equiv.Perm (Fin N),
      (2 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))))⁻¹ *
          condSqIncrement (stdBlockSum a d u) (stdBlockSumSwap a d u) σ
        = S₂ / ((N : ℝ) - 1) + coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂))
          + coef₂ * ((BB σ) ^ 2 - c) := by
    intro σ
    rw [condSqIncrement, sum_sq_swapIndex_increment a ha d hd u σ, card_swapIndex a ha,
      Nat.cast_mul, Nat.cast_sub hmN.le, hu2, hcoef₁, hcoef₂, hc, hAA, hBB]
    field_simp
    ring
  -- the pointwise triangle inequality
  have hpt : ∀ σ : Equiv.Perm (Fin N),
      |1 - (2 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))))⁻¹ *
          condSqIncrement (stdBlockSum a d u) (stdBlockSumSwap a d u) σ|
        ≤ |1 - S₂ / ((N : ℝ) - 1)| + |coef₁| * |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|
          + |coef₂| * |(BB σ) ^ 2 - c| := by
    intro σ
    rw [hXeq σ]
    have h1 : 1 - (S₂ / ((N : ℝ) - 1) + coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂))
        + coef₂ * ((BB σ) ^ 2 - c))
        = (1 - S₂ / ((N : ℝ) - 1)) + (-(coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)))
          + -(coef₂ * ((BB σ) ^ 2 - c))) := by ring
    rw [h1]
    calc |(1 - S₂ / ((N : ℝ) - 1)) + (-(coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)))
            + -(coef₂ * ((BB σ) ^ 2 - c)))|
        ≤ |1 - S₂ / ((N : ℝ) - 1)| + |-(coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)))
            + -(coef₂ * ((BB σ) ^ 2 - c))| := abs_add_le _ _
      _ ≤ |1 - S₂ / ((N : ℝ) - 1)| + (|-(coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)))|
            + |-(coef₂ * ((BB σ) ^ 2 - c))|) := by
          have hab := abs_add_le (-(coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂))))
            (-(coef₂ * ((BB σ) ^ 2 - c)))
          linarith
      _ = |1 - S₂ / ((N : ℝ) - 1)| + |coef₁| * |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|
            + |coef₂| * |(BB σ) ^ 2 - c| := by
          rw [abs_neg, abs_neg, abs_mul, abs_mul]; ring
  -- the fluctuation of the block sum of squares, by Cauchy-Schwarz
  set e : Fin N → ℝ := fun l => d l ^ 2 - (N : ℝ)⁻¹ * S₂ with he
  have hecent : ∑ l, e l = 0 := by
    rw [he, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hN0.ne', one_mul, ← hS₂, sub_self]
  have hAe : ∀ σ : Equiv.Perm (Fin N),
      ∑ i, e (σ (a i)) = AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂) := by
    intro σ
    have hblock : AA σ = ∑ i, d (σ (a i)) ^ 2 := sum_blockSet a ha fun r => d (σ r) ^ 2
    rw [hblock, he]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hesq : ∑ l, e l ^ 2 ≤ S₄ := by
    have hexp : ∑ l, e l ^ 2 = S₄ - (N : ℝ) * ((N : ℝ)⁻¹ * S₂) ^ 2 := by
      have hterm : ∀ l : Fin N, e l ^ 2
          = d l ^ 4 - 2 * ((N : ℝ)⁻¹ * S₂) * d l ^ 2 + ((N : ℝ)⁻¹ * S₂) ^ 2 := by
        intro l; rw [he]; ring
      rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, ← hS₂, ← hS₄]
      field_simp
      ring
    rw [hexp]
    nlinarith [sq_nonneg ((N : ℝ)⁻¹ * S₂), hN0]
  have hAavg : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|
      ≤ Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * S₄) := by
    have hcs := avg_abs_le_sqrt_avg_sq (ι := Equiv.Perm (Fin N)) fun σ => ∑ i, e (σ (a i))
    have hsq := avg_perm_blockSum_sq hN a ha e hecent
    have hstep : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|
        ≤ Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * ∑ l, e l ^ 2) := by
      have hL : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N), |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|
          = (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N), |∑ i, e (σ (a i))| :=
        congrArg _ (Finset.sum_congr rfl fun σ _ => by rw [hAe σ])
      rw [hL]
      refine hcs.trans (le_of_eq ?_)
      rw [hsq]
    refine hstep.trans ?_
    refine Real.sqrt_le_sqrt ?_
    exact mul_le_mul_of_nonneg_left hesq (by positivity)
  -- the fluctuation of the squared block sum
  have hBavg : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), |(BB σ) ^ 2 - c| ≤ 2 * c := by
    have hpt2 : ∀ σ : Equiv.Perm (Fin N), |(BB σ) ^ 2 - c| ≤ (BB σ) ^ 2 + c := by
      intro σ
      calc |(BB σ) ^ 2 - c| ≤ |(BB σ) ^ 2| + |c| := by
            have h := abs_add_le ((BB σ) ^ 2) (-c)
            simpa [sub_eq_add_neg, abs_neg] using h
        _ = (BB σ) ^ 2 + c := by rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hc0]
    have hsq := avg_perm_blockSet_sq hN a ha d hd
    calc (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N), |(BB σ) ^ 2 - c|
        ≤ (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N), ((BB σ) ^ 2 + c) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hpt2 σ) (inv_nonneg.2 hcP.le)
      _ = 2 * c := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            mul_add, ← mul_assoc, inv_mul_cancel₀ hcP.ne', one_mul, hBB, hsq, hc, ← hS₂]
          ring
  -- assemble
  have hsplit : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), (|1 - S₂ / ((N : ℝ) - 1)|
        + |coef₁| * |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)| + |coef₂| * |(BB σ) ^ 2 - c|)
      = |1 - S₂ / ((N : ℝ) - 1)|
        + |coef₁| * ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N), |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|)
        + |coef₂| * ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N), |(BB σ) ^ 2 - c|) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, mul_add, mul_add, ← mul_assoc,
      inv_mul_cancel₀ hcP.ne', one_mul]
    ring
  have habs₁ : |coef₁| = |(N : ℝ) - 2 * (m : ℝ)| / (2 * (m : ℝ) * ((N : ℝ) - m)) := by
    rw [hcoef₁, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (m : ℝ) * ((N : ℝ) - m))]
  have habs₂ : |coef₂| * (2 * c) = 2 * S₂ / ((N : ℝ) * ((N : ℝ) - 1)) := by
    rw [hcoef₂, hc, abs_of_pos (by positivity : (0 : ℝ) < ((m : ℝ) * ((N : ℝ) - m))⁻¹)]
    field_simp
  calc (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N),
            |1 - (2 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))))⁻¹ *
              condSqIncrement (stdBlockSum a d u) (stdBlockSumSwap a d u) σ|
      ≤ (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N), (|1 - S₂ / ((N : ℝ) - 1)|
            + |coef₁| * |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)| + |coef₂| * |(BB σ) ^ 2 - c|) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hpt σ) (inv_nonneg.2 hcP.le)
    _ = |1 - S₂ / ((N : ℝ) - 1)|
          + |coef₁| * ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
              ∑ σ : Equiv.Perm (Fin N), |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|)
          + |coef₂| * ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
              ∑ σ : Equiv.Perm (Fin N), |(BB σ) ^ 2 - c|) := hsplit
    _ ≤ |1 - S₂ / ((N : ℝ) - 1)|
          + |coef₁| * Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * S₄)
          + |coef₂| * (2 * c) := by
        gcongr
    _ = |1 - S₂ / ((N : ℝ) - 1)|
          + |(N : ℝ) - 2 * (m : ℝ)| / (2 * (m : ℝ) * ((N : ℝ) - m)) *
              Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * S₄)
          + 2 * S₂ / ((N : ℝ) * ((N : ℝ) - 1)) := by rw [habs₁, habs₂]

/-! ### The Berry-Esseen-type bound at a fixed stage -/

/-- **A Berry–Esseen-type bound for a block sum, at a fixed stage.** For a centred population
`d` on `Fin N` and a block of `m` distinct positions, standardized by any `u > 0` with
`u² = N/(m(N−m))`, the group average of a bounded `L`-Lipschitz test function differs from its
standard normal expectation by at most the sum of a *variance-regression* term — the defect of
`(N−1)⁻¹∑d²` from `1` plus a fourth-moment fluctuation — and a *third-moment* term. Both are
explicit finite-population quantities; the asymptotic statement
`tendsto_perm_avg_lipschitz` is obtained by applying this bound to a truncated population. -/
theorem abs_avg_blockSum_sub_stdGaussianExpect_le {N m : ℕ} (hN : 2 ≤ N) (hm : 0 < m)
    (hmN : m < N) (a : Fin m → Fin N) (ha : Function.Injective a) (d : Fin N → ℝ)
    (hd : ∑ l, d l = 0) {u : ℝ} (hu : 0 < u)
    (hu2 : u ^ 2 = (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m)))
    {h : ℝ → ℝ} {L C : ℝ} (hL : 0 ≤ L) (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|)
    (hbdd : ∀ x, |h x| ≤ C) :
    |(Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), h (u * ∑ i, d (σ (a i))) - stdGaussianExpect h|
      ≤ 2 * L * (|1 - (∑ l, d l ^ 2) / ((N : ℝ) - 1)|
          + |(N : ℝ) - 2 * (m : ℝ)| / (2 * (m : ℝ) * ((N : ℝ) - m)) *
              Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * ∑ l, d l ^ 4)
          + 2 * (∑ l, d l ^ 2) / ((N : ℝ) * ((N : ℝ) - 1)))
        + 10 * L * u * ((N : ℝ)⁻¹ * ∑ l, |d l| ^ 3) := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmNR : (0 : ℝ) < (N : ℝ) - (m : ℝ) := by
    have : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hlam : (0 : ℝ) < (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m)) := by positivity
  haveI : Nonempty (SwapIndex a) := by
    have h1 : a ⟨0, hm⟩ ∈ blockSet a := by
      rw [blockSet]; exact Finset.mem_image_of_mem a (Finset.mem_univ _)
    have hcard : 0 < ((blockSet a)ᶜ).card := by
      rw [Finset.card_compl, card_blockSet a ha, Fintype.card_fin]
      omega
    obtain ⟨q, hq⟩ := Finset.card_pos.1 hcard
    exact ⟨(⟨a ⟨0, hm⟩, h1⟩, ⟨q, hq⟩)⟩
  have hh : Continuous h := continuous_of_lipschitz_bound hL hlip
  have hderiv : ∀ w : ℝ, HasDerivAt (steinSolution h) (deriv (steinSolution h) w) w := by
    intro w
    rw [(hasDerivAt_steinSolution hh hbdd w).deriv]
    exact hasDerivAt_steinSolution hh hbdd w
  have hengine := abs_avg_sub_le (Ω := Equiv.Perm (Fin N)) (K := SwapIndex a)
    (W := stdBlockSum a d u) (W' := stdBlockSumSwap a d u)
    (lam := (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) hlam (sum_swap_exchangeable a d u)
    (sum_swapIndex_increment' a ha hm hmN d hd u) (h := h) (f := steinSolution h)
    (f' := deriv (steinSolution h)) (c := stdGaussianExpect h) (B₁ := 2 * L) (B₂ := 5 * L)
    (by linarith) hderiv (fun w => steinSolution_sub_mul hh hbdd w)
    (abs_deriv_steinSolution_le hL hlip hbdd) (lipschitz_deriv_steinSolution hL hlip hbdd)
  have hWeq : ∀ σ : Equiv.Perm (Fin N), stdBlockSum a d u σ = u * ∑ i, d (σ (a i)) := by
    intro σ; rw [stdBlockSum, sum_blockSet a ha]
  have hgoal : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), h (u * ∑ i, d (σ (a i)))
      = (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), h (stdBlockSum a d u σ) :=
    congrArg _ (Finset.sum_congr rfl fun σ _ => by rw [hWeq σ])
  rw [hgoal]
  refine hengine.trans ?_
  have hvar := avg_abs_one_sub_condSq_le hN hm hmN a ha d hd hu2
  have hcube := avg_cube_increment_le a ha hm hmN d u
  have hcoef : (0 : ℝ) ≤ (4 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))))⁻¹ * (5 * L) := by
    have : (0 : ℝ) < 4 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) := by linarith
    positivity
  have hlast : (4 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))))⁻¹ * (5 * L) *
      (8 * |u| ^ 3 * ((N : ℝ)⁻¹ * ∑ l, |d l| ^ 3))
      = 10 * L * u * ((N : ℝ)⁻¹ * ∑ l, |d l| ^ 3) := by
    rw [abs_of_pos hu, ← hu2]
    field_simp
    ring
  calc 2 * L * ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N),
            |1 - (2 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))))⁻¹ *
              condSqIncrement (stdBlockSum a d u) (stdBlockSumSwap a d u) σ|)
        + (4 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))))⁻¹ * (5 * L) *
          ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ * (Fintype.card (SwapIndex a) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N), ∑ k : SwapIndex a,
              |stdBlockSumSwap a d u σ k - stdBlockSum a d u σ| ^ 3)
      ≤ 2 * L * (|1 - (∑ l, d l ^ 2) / ((N : ℝ) - 1)|
            + |(N : ℝ) - 2 * (m : ℝ)| / (2 * (m : ℝ) * ((N : ℝ) - m)) *
                Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * ∑ l, d l ^ 4)
            + 2 * (∑ l, d l ^ 2) / ((N : ℝ) * ((N : ℝ) - 1)))
          + (4 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))))⁻¹ * (5 * L) *
            (8 * |u| ^ 3 * ((N : ℝ)⁻¹ * ∑ l, |d l| ^ 3)) :=
        add_le_add (mul_le_mul_of_nonneg_left hvar (by linarith))
          (mul_le_mul_of_nonneg_left hcube hcoef)
    _ = _ := by rw [hlast]

/-! ### Changing the population inside a group average -/

/-- **Replacing the population costs a second moment.** Two *centred* populations `d` and `d'`
give group averages of an `L`-Lipschitz test function that differ by at most
`L u √(m(N−m)/(N(N−1)) ∑ (d − d')²)`; the finite-population factor is the exact second moment
`avg_perm_blockSum_sq` of the difference, and it is what makes the estimate symmetric under
`m ↦ N − m`. This is the step that discards the tail of a truncated population. -/
private lemma abs_avg_h_blockSum_sub_le {N m : ℕ} (hN : 2 ≤ N) (a : Fin m → Fin N)
    (ha : Function.Injective a) (d d' : Fin N → ℝ) (hd : ∑ l, d l = 0) (hd' : ∑ l, d' l = 0)
    {u : ℝ} (hu : 0 ≤ u) {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|) :
    |(Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N), h (u * ∑ i, d (σ (a i)))
        - (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N), h (u * ∑ i, d' (σ (a i)))|
      ≤ L * u * Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
          ∑ l, (d l - d' l) ^ 2) := by
  classical
  have hcP : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hecent : ∑ l, (d l - d' l) = 0 := by
    rw [Finset.sum_sub_distrib, hd, hd', sub_zero]
  have hsumdiff : ∀ σ : Equiv.Perm (Fin N),
      ∑ i, (d (σ (a i)) - d' (σ (a i)))
        = (∑ i, d (σ (a i))) - ∑ i, d' (σ (a i)) := fun σ => by
        rw [Finset.sum_sub_distrib]
  have hdiff : ∀ σ : Equiv.Perm (Fin N),
      |h (u * ∑ i, d (σ (a i))) - h (u * ∑ i, d' (σ (a i)))|
        ≤ L * u * |∑ i, (d (σ (a i)) - d' (σ (a i)))| := by
    intro σ
    have h1 := hlip (u * ∑ i, d (σ (a i))) (u * ∑ i, d' (σ (a i)))
    have h2 : |u * (∑ i, d (σ (a i))) - u * ∑ i, d' (σ (a i))|
        = u * |∑ i, (d (σ (a i)) - d' (σ (a i)))| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hu, hsumdiff σ]
    rw [h2] at h1
    calc |h (u * ∑ i, d (σ (a i))) - h (u * ∑ i, d' (σ (a i)))|
        ≤ L * (u * |∑ i, (d (σ (a i)) - d' (σ (a i)))|) := h1
      _ = L * u * |∑ i, (d (σ (a i)) - d' (σ (a i)))| := by ring
  have hsq := avg_perm_blockSum_sq hN a ha (fun l => d l - d' l) hecent
  have hstep1 : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), h (u * ∑ i, d (σ (a i)))
      - (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), h (u * ∑ i, d' (σ (a i)))
      = (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N),
          (h (u * ∑ i, d (σ (a i))) - h (u * ∑ i, d' (σ (a i)))) := by
    rw [← mul_sub, Finset.sum_sub_distrib]
  rw [hstep1, abs_mul, abs_of_nonneg (inv_nonneg.2 hcP.le)]
  calc (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          |∑ σ : Equiv.Perm (Fin N),
            (h (u * ∑ i, d (σ (a i))) - h (u * ∑ i, d' (σ (a i))))|
      ≤ (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N),
            |h (u * ∑ i, d (σ (a i))) - h (u * ∑ i, d' (σ (a i)))| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hcP.le)
    _ ≤ (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N), L * u * |∑ i, (d (σ (a i)) - d' (σ (a i)))| :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hdiff σ) (inv_nonneg.2 hcP.le)
    _ = L * u * ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N), |∑ i, (d (σ (a i)) - d' (σ (a i)))|) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ L * u * Real.sqrt ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N), (∑ i, (d (σ (a i)) - d' (σ (a i)))) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (avg_abs_le_sqrt_avg_sq fun σ : Equiv.Perm (Fin N) =>
            ∑ i, (d (σ (a i)) - d' (σ (a i)))) (by positivity)
    _ = L * u * Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
          ∑ l, (d l - d' l) ^ 2) := by rw [hsq]

/-! ### Truncating and recentring a finite population -/

/-- The part of the population *discarded* by truncation at level `τ`. -/
private noncomputable def truncDisc {N : ℕ} (τ : ℝ) (d : Fin N → ℝ) : Fin N → ℝ :=
  fun l => if τ ≤ |d l| then d l else 0

/-- The part of the population *kept* by truncation at level `τ`. -/
private noncomputable def truncKeep {N : ℕ} (τ : ℝ) (d : Fin N → ℝ) : Fin N → ℝ :=
  fun l => if τ ≤ |d l| then 0 else d l

/-- The second moment carried by the discarded part — the quantity that Hájek's Lindeberg
condition sends to `0`. -/
private noncomputable def truncLoss {N : ℕ} (τ : ℝ) (d : Fin N → ℝ) : ℝ :=
  ∑ l, truncDisc τ d l ^ 2

/-- The truncated population, recentred so as to be centred again. -/
private noncomputable def truncCentred {N : ℕ} (τ : ℝ) (d : Fin N → ℝ) : Fin N → ℝ :=
  fun l => truncKeep τ d l - (N : ℝ)⁻¹ * ∑ l', truncKeep τ d l'

private lemma truncKeep_add_truncDisc {N : ℕ} (τ : ℝ) (d : Fin N → ℝ) (l : Fin N) :
    truncKeep τ d l + truncDisc τ d l = d l := by
  simp only [truncKeep, truncDisc]
  by_cases hl : τ ≤ |d l| <;> simp [hl]

private lemma abs_truncKeep_le {N : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (d : Fin N → ℝ) (l : Fin N) :
    |truncKeep τ d l| ≤ τ := by
  simp only [truncKeep]
  by_cases hl : τ ≤ |d l|
  · simp [hl, hτ]
  · rw [if_neg hl]; exact le_of_not_ge hl

private lemma truncLoss_nonneg {N : ℕ} (τ : ℝ) (d : Fin N → ℝ) : 0 ≤ truncLoss τ d :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The Lindeberg tail in the shape in which the hypothesis of the central limit theorem
supplies it. -/
private lemma truncLoss_eq {N : ℕ} (τ : ℝ) (d : Fin N → ℝ) :
    truncLoss τ d = ∑ l, (if τ ≤ |d l| then d l ^ 2 else 0) := by
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [truncDisc]
  by_cases hl : τ ≤ |d l| <;> simp [hl]

private lemma sum_sq_truncKeep {N : ℕ} (τ : ℝ) (d : Fin N → ℝ) :
    ∑ l, truncKeep τ d l ^ 2 = (∑ l, d l ^ 2) - truncLoss τ d := by
  rw [truncLoss, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [truncKeep, truncDisc]
  by_cases hl : τ ≤ |d l| <;> simp [hl]

private lemma abs_sum_truncDisc_le {N : ℕ} {τ : ℝ} (hτ : 0 < τ) (d : Fin N → ℝ) :
    |∑ l, truncDisc τ d l| ≤ truncLoss τ d / τ := by
  have hpt : ∀ l : Fin N, |truncDisc τ d l| ≤ truncDisc τ d l ^ 2 / τ := by
    intro l
    simp only [truncDisc]
    by_cases hl : τ ≤ |d l|
    · rw [if_pos hl, le_div_iff₀ hτ, ← sq_abs (d l)]
      nlinarith [hl, abs_nonneg (d l)]
    · rw [if_neg hl]
      simp
  calc |∑ l, truncDisc τ d l| ≤ ∑ l, |truncDisc τ d l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, truncDisc τ d l ^ 2 / τ := Finset.sum_le_sum fun l _ => hpt l
    _ = truncLoss τ d / τ := by rw [truncLoss, Finset.sum_div]

private lemma sum_truncCentred_eq_zero {N : ℕ} (hN : 0 < N) (τ : ℝ) (d : Fin N → ℝ) :
    ∑ l, truncCentred τ d l = 0 := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact this.ne'
  simp only [truncCentred]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul, sub_self]

private lemma abs_truncCentred_le {N : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (d : Fin N → ℝ) (l : Fin N) :
    |truncCentred τ d l| ≤ τ + |(N : ℝ)⁻¹ * ∑ l', truncKeep τ d l'| := by
  simp only [truncCentred]
  calc |truncKeep τ d l - (N : ℝ)⁻¹ * ∑ l', truncKeep τ d l'|
      ≤ |truncKeep τ d l| + |(N : ℝ)⁻¹ * ∑ l', truncKeep τ d l'| := by
        have h := abs_add_le (truncKeep τ d l) (-((N : ℝ)⁻¹ * ∑ l', truncKeep τ d l'))
        simpa [sub_eq_add_neg, abs_neg] using h
    _ ≤ τ + |(N : ℝ)⁻¹ * ∑ l', truncKeep τ d l'| := by
        have h := abs_truncKeep_le hτ d l
        linarith

private lemma sum_sq_truncCentred {N : ℕ} (hN : 0 < N) (τ : ℝ) (d : Fin N → ℝ) :
    ∑ l, truncCentred τ d l ^ 2
      = (∑ l, d l ^ 2) - truncLoss τ d
        - (N : ℝ) * ((N : ℝ)⁻¹ * ∑ l', truncKeep τ d l') ^ 2 := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact this.ne'
  set μ : ℝ := (N : ℝ)⁻¹ * ∑ l', truncKeep τ d l' with hμ
  have hterm : ∀ l : Fin N, truncCentred τ d l ^ 2
      = truncKeep τ d l ^ 2 - 2 * μ * truncKeep τ d l + μ ^ 2 := by
    intro l; simp only [truncCentred]; rw [← hμ]; ring
  rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
    sum_sq_truncKeep]
  have hkey : ∑ l', truncKeep τ d l' = (N : ℝ) * μ := by
    rw [hμ, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
  rw [hkey]
  ring

private lemma sum_sq_sub_truncCentred_le {N : ℕ} (hN : 0 < N) (τ : ℝ) (d : Fin N → ℝ)
    (hd : ∑ l, d l = 0) :
    ∑ l, (d l - truncCentred τ d l) ^ 2 ≤ truncLoss τ d := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact this.ne'
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set μ : ℝ := (N : ℝ)⁻¹ * ∑ l', truncKeep τ d l' with hμ
  have hkeep : ∑ l', truncKeep τ d l' = (N : ℝ) * μ := by
    rw [hμ, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
  have hdisc : ∑ l, truncDisc τ d l = -((N : ℝ) * μ) := by
    have hsplit : (∑ l, truncKeep τ d l) + ∑ l, truncDisc τ d l = 0 := by
      rw [← Finset.sum_add_distrib,
        Finset.sum_congr rfl fun l _ => truncKeep_add_truncDisc τ d l, hd]
    rw [hkeep] at hsplit
    linarith
  have hterm : ∀ l : Fin N, d l - truncCentred τ d l = truncDisc τ d l + μ := by
    intro l
    simp only [truncCentred]
    rw [← hμ, ← truncKeep_add_truncDisc τ d l]
    ring
  have hexp : ∑ l, (d l - truncCentred τ d l) ^ 2
      = truncLoss τ d + 2 * μ * (∑ l, truncDisc τ d l) + (N : ℝ) * μ ^ 2 := by
    have hsq : ∀ l : Fin N, (d l - truncCentred τ d l) ^ 2
        = truncDisc τ d l ^ 2 + 2 * μ * truncDisc τ d l + μ ^ 2 := by
      intro l; rw [hterm l]; ring
    rw [Finset.sum_congr rfl fun l _ => hsq l, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
      truncLoss]
  rw [hexp, hdisc]
  nlinarith [sq_nonneg μ, hNpos]

/-- Third absolute moment from a sup bound. -/
private lemma sum_abs_cube_le {N : ℕ} {B : ℝ} (f : Fin N → ℝ) (hB : ∀ l, |f l| ≤ B) :
    ∑ l, |f l| ^ 3 ≤ B * ∑ l, f l ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  calc |f l| ^ 3 = |f l| * f l ^ 2 := by rw [show |f l| ^ 3 = |f l| * |f l| ^ 2 by ring, sq_abs]
    _ ≤ B * f l ^ 2 := mul_le_mul_of_nonneg_right (hB l) (sq_nonneg _)

/-- Fourth moment from a sup bound. -/
private lemma sum_pow_four_le {N : ℕ} {B : ℝ} (f : Fin N → ℝ) (hB : ∀ l, |f l| ≤ B) :
    ∑ l, f l ^ 4 ≤ B ^ 2 * ∑ l, f l ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  have hsq : f l ^ 2 ≤ B ^ 2 := by
    have h := hB l
    have h0 : (0 : ℝ) ≤ |f l| := abs_nonneg _
    nlinarith [sq_abs (f l)]
  calc f l ^ 4 = f l ^ 2 * f l ^ 2 := by ring
    _ ≤ B ^ 2 * f l ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

private lemma sum_truncKeep_eq_neg {N : ℕ} (τ : ℝ) (d : Fin N → ℝ) (hd : ∑ l, d l = 0) :
    ∑ l, truncKeep τ d l = -∑ l, truncDisc τ d l := by
  have hsplit : (∑ l, truncKeep τ d l) + ∑ l, truncDisc τ d l = 0 := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl fun l _ => truncKeep_add_truncDisc τ d l, hd]
  linarith

/-- The recentring shift is controlled by the Lindeberg tail: `|μ| ≤ (N⁻¹ ∑ tail²)/τ`. -/
private lemma abs_mean_truncKeep_le {N : ℕ} {τ : ℝ} (hτ : 0 < τ) (hN : 0 < N)
    (d : Fin N → ℝ) (hd : ∑ l, d l = 0) :
    |(N : ℝ)⁻¹ * ∑ l, truncKeep τ d l| ≤ ((N : ℝ)⁻¹ * truncLoss τ d) * τ⁻¹ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hNpos.le), sum_truncKeep_eq_neg τ d hd, abs_neg]
  have hstep := abs_sum_truncDisc_le hτ d
  rw [div_eq_mul_inv] at hstep
  calc (N : ℝ)⁻¹ * |∑ l, truncDisc τ d l|
      ≤ (N : ℝ)⁻¹ * (truncLoss τ d * τ⁻¹) :=
        mul_le_mul_of_nonneg_left hstep (inv_nonneg.2 hNpos.le)
    _ = ((N : ℝ)⁻¹ * truncLoss τ d) * τ⁻¹ := by ring

/-! ### From an `ε`-family of bounds to a limit -/

/-- If a sequence is eventually within `C ε` of `A` for every `ε > 0`, it converges to `A`. -/
private lemma tendsto_of_eventually_abs_sub_le {F : ℕ → ℝ} {A Cst : ℝ} (hC : 0 ≤ Cst)
    (hF : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, |F k - A| ≤ Cst * ε) :
    Tendsto F atTop (𝓝 A) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hpos : (0 : ℝ) < δ / (2 * (Cst + 1)) := by positivity
  filter_upwards [hF (δ / (2 * (Cst + 1))) hpos] with k hk
  rw [Real.dist_eq]
  have hkey : Cst * (δ / (2 * (Cst + 1))) < δ := by
    rw [← mul_div_assoc, div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (Cst + 1))]
    nlinarith
  linarith

set_option maxHeartbeats 800000 in
-- the whole `ε`-step (truncation, recentring, both Stein error terms and the coupling) is
-- carried out in a single block, over a dozen `set` abbreviations
/-- **The fixed-stage estimate after truncation.** All the hypotheses are the ones that the
Lindeberg condition, the normalisation `N⁻¹∑d² → 1` and the growth of both blocks make
eventually true at level `ε`; the conclusion is the `ε`-step of the diagonal argument. The
population is truncated at Hájek's scale `ε√(min (m, N−m))` and recentred, the fixed-stage
Berry–Esseen bound `abs_avg_blockSum_sub_stdGaussianExpect_le` is applied to the truncated
population, and the discarded part is paid for by `abs_avg_h_blockSum_sub_le`. -/
private lemma abs_avg_blockSum_sub_le_of_trunc {N m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (a : Fin m → Fin N) (ha : Function.Injective a) (d : Fin N → ℝ) (hd : ∑ l, d l = 0)
    {h : ℝ → ℝ} {L C : ℝ} (hL : 0 ≤ L) (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|)
    (hbdd : ∀ x, |h x| ≤ C)
    (hN2 : (2 : ℝ) ≤ (N : ℝ)) (hmk : (0 : ℝ) < (m : ℝ)) (hNmk : (0 : ℝ) < (N : ℝ) - m)
    (hMn1 : (1 : ℝ) ≤ min (m : ℝ) ((N : ℝ) - m))
    (hΛk : |(N : ℝ)⁻¹ * truncLoss (ε * Real.sqrt (min (m : ℝ) ((N : ℝ) - m))) d| < ε ^ 2)
    (hQk : |(∑ l, truncCentred (ε * Real.sqrt (min (m : ℝ) ((N : ℝ) - m))) d l ^ 2)
        / ((N : ℝ) - 1) - 1| < ε)
    (hPk : |(N : ℝ)⁻¹ *
        ∑ l, truncCentred (ε * Real.sqrt (min (m : ℝ) ((N : ℝ) - m))) d l ^ 2 - 1| < 1)
    (hT3k : |2 * (∑ l, truncCentred (ε * Real.sqrt (min (m : ℝ) ((N : ℝ) - m))) d l ^ 2)
        / ((N : ℝ) * ((N : ℝ) - 1))| < ε) :
    |(Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), h ((blockSumScale N m)⁻¹ * ∑ i, d (σ (a i)))
      - stdGaussianExpect h| ≤ 100 * (L + 1) * ε := by
  -- integer and real facts at stage `k`
  have hNnat : 2 ≤ N := by exact_mod_cast hN2
  have hmnat : 0 < m := by exact_mod_cast hmk
  have hmNnat : m < N := by
    have hlt : (m : ℝ) < (N : ℝ) := by linarith
    exact_mod_cast hlt
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1pos : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  set Mn : ℝ := min (m : ℝ) ((N : ℝ) - m) with hMndef
  have hMnpos : (0 : ℝ) < Mn := by linarith
  have hsqrtMn : (0 : ℝ) < Real.sqrt Mn := Real.sqrt_pos.2 hMnpos
  have hsqMn : Real.sqrt Mn * Real.sqrt Mn = Mn := Real.mul_self_sqrt hMnpos.le
  set τ : ℝ := ε * Real.sqrt Mn with hτdef
  have hτpos : (0 : ℝ) < τ := by rw [hτdef]; exact mul_pos hε hsqrtMn
  set dt : Fin N → ℝ := truncCentred τ d with hdtdef
  have hdtcent : ∑ l, dt l = 0 := by
    rw [hdtdef]; exact sum_truncCentred_eq_zero (by omega) τ d
  -- the two elementary comparisons of the Stein scale with Hajek's scale
  have hsumMn : (m : ℝ) + ((N : ℝ) - m) = (N : ℝ) := by ring
  have hh1 : Mn * (N : ℝ) ≤ ((m : ℝ) * ((N : ℝ) - m)) * 2 := by
    have hx := min_div_two_le_mul_div hmk hNmk
    rw [hsumMn, ← hMndef, div_le_div_iff₀ (by norm_num) hNpos] at hx
    exact hx
  have hh2 : (m : ℝ) * ((N : ℝ) - m) ≤ Mn * (N : ℝ) := by
    have hx := mul_div_add_le_min hmk hNmk
    rw [hsumMn, ← hMndef, div_le_iff₀ hNpos] at hx
    exact hx
  -- the standardizing scale
  have hXpos : (0 : ℝ) < (m : ℝ) * ((N : ℝ) - m) / (N : ℝ) := by positivity
  have hscalepos : (0 : ℝ) < blockSumScale N m := by
    rw [blockSumScale, Real.sqrt_pos]; exact hXpos
  have hupos : (0 : ℝ) < (blockSumScale N m)⁻¹ := inv_pos.2 hscalepos
  have hu2 : ((blockSumScale N m)⁻¹) ^ 2
      = (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m)) := by
    rw [blockSumScale, inv_pow, Real.sq_sqrt hXpos.le, inv_div]
  have hule : (blockSumScale N m)⁻¹ ≤ 2 / Real.sqrt Mn := by
    have hy : (0 : ℝ) < 2 / Real.sqrt Mn := by positivity
    have hsq : ((blockSumScale N m)⁻¹) ^ 2 ≤ (2 / Real.sqrt Mn) ^ 2 := by
      rw [hu2, div_pow, Real.sq_sqrt hMnpos.le,
        div_le_div_iff₀ (by positivity) hMnpos]
      nlinarith [hh1, mul_pos hmk hNmk]
    nlinarith [hupos, hy, hsq]
  -- the truncated population: sup bound and moments
  have hsup0 : ∀ l, |dt l| ≤ τ + |(N : ℝ)⁻¹ * ∑ l', truncKeep τ d l'| := by
    intro l
    rw [hdtdef]
    exact abs_truncCentred_le hτpos.le d l
  set Λ : ℝ := (N : ℝ)⁻¹ * truncLoss τ d with hΛdef
  set μ : ℝ := (N : ℝ)⁻¹ * ∑ l', truncKeep τ d l' with hμdef
  set B : ℝ := τ + |μ| with hBdef
  have hΛnn : (0 : ℝ) ≤ Λ := by
    rw [hΛdef]
    exact mul_nonneg (inv_nonneg.2 hNpos.le) (truncLoss_nonneg _ _)
  have hΛeps : Λ ≤ ε ^ 2 := by rw [abs_of_nonneg hΛnn] at hΛk; linarith
  have hμ2 : |μ| ≤ ε * Real.sqrt Mn := by
    have hx : |μ| ≤ Λ * τ⁻¹ := by
      rw [hμdef, hΛdef]
      exact abs_mean_truncKeep_le hτpos (by omega) d (hd)
    have hprod : ε * Real.sqrt Mn * τ = ε ^ 2 * Mn := by
      rw [hτdef, show ε * Real.sqrt Mn * (ε * Real.sqrt Mn)
        = ε ^ 2 * (Real.sqrt Mn * Real.sqrt Mn) by ring, hsqMn]
    have hy : Λ * τ⁻¹ ≤ ε * Real.sqrt Mn := by
      rw [← div_eq_mul_inv, div_le_iff₀ hτpos, hprod]
      nlinarith [hΛeps, hMn1, sq_nonneg ε]
    linarith
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hBdef]
    exact add_nonneg hτpos.le (abs_nonneg _)
  have hBbound : B ≤ 2 * ε * Real.sqrt Mn := by rw [hBdef, hτdef]; linarith
  have hmom3 : ∑ l, |dt l| ^ 3 ≤ B * ∑ l, dt l ^ 2 := sum_abs_cube_le dt hsup0
  have hmom4 : ∑ l, dt l ^ 4 ≤ B ^ 2 * ∑ l, dt l ^ 2 := sum_pow_four_le dt hsup0
  have hPle : (N : ℝ)⁻¹ * ∑ l, dt l ^ 2 ≤ 2 := by
    rw [abs_lt] at hPk; linarith [hPk.2]
  have hSle : ∑ l, dt l ^ 2 ≤ 2 * (N : ℝ) := by
    rw [inv_mul_le_iff₀ hNpos] at hPle; linarith
  -- the coupling with the untruncated population
  have hcoupsum : ∑ l, (d l - dt l) ^ 2 ≤ (N : ℝ) * Λ := by
    have hx := sum_sq_sub_truncCentred_le (N := N) (by omega) τ d (hd)
    rw [← hdtdef] at hx
    have hΛeq : (N : ℝ) * Λ = truncLoss τ d := by
      rw [hΛdef, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
    rw [hΛeq]
    exact hx
  have hradc : (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
      ∑ l, (d l - dt l) ^ 2 ≤ (2 * ε * Real.sqrt Mn) ^ 2 := by
    have hcf : (0 : ℝ) ≤ (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) := by
      positivity
    have hfrac : (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
        ((N : ℝ) * Λ) ≤ 2 * Mn * ε ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have e1 : ((m : ℝ) * ((N : ℝ) - m)) * ((N : ℝ) * Λ)
          ≤ (Mn * (N : ℝ)) * ((N : ℝ) * Λ) :=
        mul_le_mul_of_nonneg_right hh2 (mul_nonneg hNpos.le hΛnn)
      have e2 : (Mn * (N : ℝ)) * ((N : ℝ) * Λ)
          ≤ (Mn * (N : ℝ)) * ((N : ℝ) * ε ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΛeps hNpos.le)
          (mul_nonneg hMnpos.le hNpos.le)
      have hnn : (0 : ℝ) ≤ Mn * ε ^ 2 * (N : ℝ) * ((N : ℝ) - 2) :=
        mul_nonneg (mul_nonneg (mul_nonneg hMnpos.le (sq_nonneg ε)) hNpos.le) (by linarith)
      linarith
    have hstep : (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
        ∑ l, (d l - dt l) ^ 2
        ≤ (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * ((N : ℝ) * Λ) :=
      mul_le_mul_of_nonneg_left hcoupsum hcf
    have hsq : (2 * ε * Real.sqrt Mn) ^ 2 = 4 * Mn * ε ^ 2 := by
      rw [show (2 * ε * Real.sqrt Mn) ^ 2 = 4 * ε ^ 2 * (Real.sqrt Mn * Real.sqrt Mn) by ring,
        hsqMn]
      ring
    rw [hsq]
    nlinarith [hstep, hfrac, mul_nonneg hMnpos.le (sq_nonneg ε)]
  have hcoup := abs_avg_h_blockSum_sub_le hNnat a ha d dt hd hdtcent
    hupos.le hL hlip
  have hcoupbound : |(Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N),
          h ((blockSumScale N m)⁻¹ * ∑ i, d (σ (a i)))
      - (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N),
          h ((blockSumScale N m)⁻¹ * ∑ i, dt (σ (a i)))| ≤ 4 * L * ε := by
    refine hcoup.trans ?_
    have hsqrtle : Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
        ∑ l, (d l - dt l) ^ 2) ≤ 2 * ε * Real.sqrt Mn :=
      sqrt_le_of_sq_le (by positivity) hradc
    have hfin : (blockSumScale N m)⁻¹ * (2 * ε * Real.sqrt Mn) ≤ 4 * ε := by
      have hx : (blockSumScale N m)⁻¹ * (2 * ε * Real.sqrt Mn)
          ≤ (2 / Real.sqrt Mn) * (2 * ε * Real.sqrt Mn) :=
        mul_le_mul_of_nonneg_right hule (by positivity)
      have hy : (2 / Real.sqrt Mn) * (2 * ε * Real.sqrt Mn) = 4 * ε := by
        field_simp
        ring
      linarith
    calc L * (blockSumScale N m)⁻¹ *
          Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
            ∑ l, (d l - dt l) ^ 2)
        ≤ L * (blockSumScale N m)⁻¹ * (2 * ε * Real.sqrt Mn) := by
          refine mul_le_mul_of_nonneg_left hsqrtle ?_
          positivity
      _ = L * ((blockSumScale N m)⁻¹ * (2 * ε * Real.sqrt Mn)) := by ring
      _ ≤ L * (4 * ε) := mul_le_mul_of_nonneg_left hfin hL
      _ = 4 * L * ε := by ring
  -- the three terms of the fixed-stage bound
  have hmain := abs_avg_blockSum_sub_stdGaussianExpect_le hNnat hmnat hmNnat a ha dt
    hdtcent hupos hu2 hL hlip hbdd
  have hT1 : |1 - (∑ l, dt l ^ 2) / ((N : ℝ) - 1)| ≤ ε := by
    rw [abs_sub_comm]; linarith
  have hT3 : 2 * (∑ l, dt l ^ 2) / ((N : ℝ) * ((N : ℝ) - 1)) ≤ ε := by
    have hx := abs_lt.1 hT3k
    linarith [hx.2]
  have hT2 : |(N : ℝ) - 2 * (m : ℝ)| / (2 * (m : ℝ) * ((N : ℝ) - m)) *
      Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
        ∑ l, dt l ^ 4) ≤ 2 * ε := by
    have hcoefle : |(N : ℝ) - 2 * (m : ℝ)| / (2 * (m : ℝ) * ((N : ℝ) - m))
        ≤ 1 / (2 * Mn) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rcases le_total (m : ℝ) ((N : ℝ) - m) with hle | hle
      · rw [hMndef, min_eq_left hle, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) - 2 * m)]
        nlinarith
      · rw [hMndef, min_eq_right hle,
          abs_of_nonpos (by linarith : (N : ℝ) - 2 * (m : ℝ) ≤ 0)]
        nlinarith
    have hrad : (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
        ∑ l, dt l ^ 4 ≤ (2 * B * Real.sqrt Mn) ^ 2 := by
      have hcf : (0 : ℝ) ≤ (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) := by
        positivity
      have hfrac : (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
          (B ^ 2 * (2 * (N : ℝ))) ≤ 4 * Mn * B ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have e1 : ((m : ℝ) * ((N : ℝ) - m)) * (B ^ 2 * (2 * (N : ℝ)))
            ≤ (Mn * (N : ℝ)) * (B ^ 2 * (2 * (N : ℝ))) :=
          mul_le_mul_of_nonneg_right hh2
            (mul_nonneg (sq_nonneg B) (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ)))
        have hnn : (0 : ℝ) ≤ Mn * B ^ 2 * (N : ℝ) * ((N : ℝ) - 2) :=
          mul_nonneg (mul_nonneg (mul_nonneg hMnpos.le (sq_nonneg B)) hNpos.le) (by linarith)
        linarith
      have hstep : (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
          ∑ l, dt l ^ 4
          ≤ (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
            (B ^ 2 * (2 * (N : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hcf
        calc ∑ l, dt l ^ 4 ≤ B ^ 2 * ∑ l, dt l ^ 2 := hmom4
          _ ≤ B ^ 2 * (2 * (N : ℝ)) := mul_le_mul_of_nonneg_left hSle (sq_nonneg B)
      have hsq : (2 * B * Real.sqrt Mn) ^ 2 = 4 * Mn * B ^ 2 := by
        rw [show (2 * B * Real.sqrt Mn) ^ 2 = 4 * B ^ 2 * (Real.sqrt Mn * Real.sqrt Mn) by ring,
          hsqMn]
        ring
      rw [hsq]
      linarith
    have hsqrtle : Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
        ∑ l, dt l ^ 4) ≤ 2 * B * Real.sqrt Mn :=
      sqrt_le_of_sq_le (by positivity) hrad
    have hfin : 1 / (2 * Mn) * (2 * B * Real.sqrt Mn) ≤ 2 * ε := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Mn)]
      have e1 : 2 * B * Real.sqrt Mn ≤ 2 * (2 * ε * Real.sqrt Mn) * Real.sqrt Mn := by
        have hx := mul_le_mul_of_nonneg_right hBbound (Real.sqrt_nonneg Mn)
        linarith
      have e2 : 2 * (2 * ε * Real.sqrt Mn) * Real.sqrt Mn = 4 * ε * Mn := by
        rw [show 2 * (2 * ε * Real.sqrt Mn) * Real.sqrt Mn
          = 4 * ε * (Real.sqrt Mn * Real.sqrt Mn) by ring, hsqMn]
      linarith
    calc |(N : ℝ) - 2 * (m : ℝ)| / (2 * (m : ℝ) * ((N : ℝ) - m)) *
          Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
            ∑ l, dt l ^ 4)
        ≤ 1 / (2 * Mn) * (2 * B * Real.sqrt Mn) := by
          refine mul_le_mul hcoefle hsqrtle (Real.sqrt_nonneg _) (by positivity)
      _ ≤ 2 * ε := hfin
  have hM3 : 10 * L * (blockSumScale N m)⁻¹ *
      ((N : ℝ)⁻¹ * ∑ l, |dt l| ^ 3) ≤ 80 * L * ε := by
    have ha1 : (N : ℝ)⁻¹ * ∑ l, |dt l| ^ 3 ≤ 4 * ε * Real.sqrt Mn := by
      calc (N : ℝ)⁻¹ * ∑ l, |dt l| ^ 3
          ≤ (N : ℝ)⁻¹ * (B * ∑ l, dt l ^ 2) :=
            mul_le_mul_of_nonneg_left hmom3 (inv_nonneg.2 hNpos.le)
        _ = B * ((N : ℝ)⁻¹ * ∑ l, dt l ^ 2) := by ring
        _ ≤ B * 2 := mul_le_mul_of_nonneg_left hPle hB0
        _ ≤ (2 * ε * Real.sqrt Mn) * 2 := by linarith
        _ = 4 * ε * Real.sqrt Mn := by ring
    have ha2 : (blockSumScale N m)⁻¹ * (4 * ε * Real.sqrt Mn) ≤ 8 * ε := by
      have hx : (blockSumScale N m)⁻¹ * (4 * ε * Real.sqrt Mn)
          ≤ (2 / Real.sqrt Mn) * (4 * ε * Real.sqrt Mn) :=
        mul_le_mul_of_nonneg_right hule (by positivity)
      have hy : (2 / Real.sqrt Mn) * (4 * ε * Real.sqrt Mn) = 8 * ε := by
        field_simp
        ring
      linarith
    have hstep : (blockSumScale N m)⁻¹ * ((N : ℝ)⁻¹ * ∑ l, |dt l| ^ 3) ≤ 8 * ε := by
      have hx : (blockSumScale N m)⁻¹ * ((N : ℝ)⁻¹ * ∑ l, |dt l| ^ 3)
          ≤ (blockSumScale N m)⁻¹ * (4 * ε * Real.sqrt Mn) :=
        mul_le_mul_of_nonneg_left ha1 hupos.le
      linarith
    calc 10 * L * (blockSumScale N m)⁻¹ * ((N : ℝ)⁻¹ * ∑ l, |dt l| ^ 3)
        = 10 * L * ((blockSumScale N m)⁻¹ * ((N : ℝ)⁻¹ * ∑ l, |dt l| ^ 3)) := by
          ring
      _ ≤ 10 * L * (8 * ε) := mul_le_mul_of_nonneg_left hstep (by linarith)
      _ = 80 * L * ε := by ring
  -- assemble
  have hsum3 : |1 - (∑ l, dt l ^ 2) / ((N : ℝ) - 1)|
      + |(N : ℝ) - 2 * (m : ℝ)| / (2 * (m : ℝ) * ((N : ℝ) - m)) *
          Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) *
            ∑ l, dt l ^ 4)
      + 2 * (∑ l, dt l ^ 2) / ((N : ℝ) * ((N : ℝ) - 1)) ≤ ε + 2 * ε + ε := by
    linarith
  have hmul3 := mul_le_mul_of_nonneg_left hsum3 (by linarith : (0 : ℝ) ≤ 2 * L)
  have htri := abs_sub_le ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N),
        h ((blockSumScale N m)⁻¹ * ∑ i, d (σ (a i))))
    ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N),
        h ((blockSumScale N m)⁻¹ * ∑ i, dt (σ (a i))))
    (stdGaussianExpect h)
  linarith [htri, hcoupbound, hmain, hmul3, hM3, mul_nonneg hL hε.le, hε.le]

/-- **The combinatorial central limit theorem, tested against Lipschitz functions** — the
core analytic brick. Under the hypotheses of `tendsto_perm_cdf_blockSum`, the group average
of `h` evaluated at the standardized block sum converges to the standard normal expectation
of `h`, for every bounded Lipschitz `h`.

STATUS (wave 9): PROVED, axiom-clean. Route: Stein's method for exchangeable pairs
(`ForMathlib/SteinMethod`) applied to the **truncated** population, plus a diagonal argument
in the truncation level `ε`.

* the engine `SteinMethod.abs_avg_sub_le` bounds `|avg h(W) − 𝔼h(Z)|` by
  `B₁ · avg|1 − V/(2λ)| + B₂/(4λ) · avg|W' − W|³` for any exchangeable pair with
  `𝔼[W' − W ∣ σ] = -λ W`, with `B₁ = 2L` (`SteinMethod.abs_deriv_steinSolution_le`) and
  `B₂ = 5L` (`SteinMethod.lipschitz_deriv_steinSolution`);
* the pair is the swap pair of the section above: `Ω = Equiv.Perm (Fin (N k))`,
  `K = SwapIndex (a k)`, `W = stdBlockSum`, `W' = stdBlockSumSwap`, with exchangeability
  (`sum_swap_exchangeable`), the linearity condition with `λ = N/(m(N−m))`
  (`sum_swapIndex_increment'`) and the exact conditional variance
  (`sum_sq_swapIndex_increment`);
* the two moment estimates for this pair are `avg_cube_increment_le` (third moment, from the
  one-coordinate marginal only) and `avg_abs_one_sub_condSq_le` (variance regression, from
  Cauchy–Schwarz and the exact second moment `avg_perm_blockSum_sq` applied to the *centred
  squares* `d² − N⁻¹∑d²`, i.e. a fourth-moment input `∑ d⁴`). Together they give the
  fixed-stage Berry–Esseen-type bound `abs_avg_blockSum_sub_stdGaussianExpect_le`;
* the truncation is `truncCentred (ε√(min (m, N−m)))`: the kept part is bounded by the
  Lindeberg scale, and the recentring shift by `abs_mean_truncKeep_le`. The discarded part
  is paid for by `abs_avg_h_blockSum_sub_le`, which costs *one exact second moment* of the
  difference — with the finite-population factor `m(N−m)/(N(N−1))`, which is what makes the
  estimate symmetric under `m ↦ N − m` (a Chebyshev bound without that factor is not);
* `abs_avg_blockSum_sub_le_of_trunc` is the `ε`-step, and `tendsto_of_eventually_abs_sub_le`
  performs the diagonal argument. The two comparisons `mul_div_add_le_min` and
  `min_div_two_le_mul_div` — `min(m,N−m)/2 ≤ m(N−m)/N ≤ min(m,N−m)` — are what convert the
  Stein scale `√(m(N−m)/N)` into Hájek's scale `√(min (m, N−m))` at both error terms.

WARNING (wave 8, and the reason for the truncation). It is not merely that a naive bound on
the third moment fails: the raw third-moment error term of `abs_avg_sub_le`, applied to the
*untruncated* pair, can itself **diverge** under the hypotheses of this theorem, so any
reduction of this statement to "the two error terms of the raw swap pair tend to `0`" is a
reduction to something FALSE. Explicit witness: take `m k = ⌈log N⌉`, two coefficients
`d₁ = -d₂ = √N / log log N` and the remaining `N − 2` coefficients `±1`, balanced. Then
`∑ d = 0`, `N⁻¹∑d² → 1`, and for every `ε > 0` the Hájek–Lindeberg sum is eventually
`2 (log log N)^{-2} → 0` (only `d₁, d₂` exceed the threshold `ε√(log N)`), so all hypotheses
hold; yet, since `λ⁻¹ 𝔼|W' − W|³ ≍ N⁻¹∑|d|³ / √(m(N−m)/N)`,
`≍ √N (log log N)^{-3} / √(log N) → ∞`. After truncation at the Lindeberg scale one has
`N⁻¹∑|d|³ ≤ ε√(min(m, N−m)) · N⁻¹∑d²`, which is `O(ε)` after dividing by the scale. -/
theorem tendsto_perm_avg_lipschitz {N m : ℕ → ℕ}
    -- USER-INPUT: at each stage the block is a set of `m k` distinct positions
    (a : ∀ k, Fin (m k) → Fin (N k)) (ha : ∀ k, Function.Injective (a k))
    -- USER-INPUT: the finite populations, centred
    (d : ∀ k, Fin (N k) → ℝ) (hcent : ∀ k, ∑ l, d k l = 0)
    -- USER-INPUT: both the block and its complement grow
    (hm : Tendsto (fun k => (m k : ℝ)) atTop atTop)
    (hNm : Tendsto (fun k => (N k : ℝ) - m k) atTop atTop)
    -- USER-INPUT: the populations are normalized in the second moment
    (hvar : Tendsto (fun k => (N k : ℝ)⁻¹ * ∑ l, d k l ^ 2) atTop (𝓝 1))
    -- USER-INPUT: Hájek's Lindeberg condition at scale `√(min (m k) (N k - m k))`
    (hlind : ∀ ε > (0 : ℝ), Tendsto (fun k => (N k : ℝ)⁻¹ *
        ∑ l, (if ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k)) ≤ |d k l|
              then d k l ^ 2 else 0)) atTop (𝓝 0))
    -- USER-INPUT: a bounded Lipschitz test function
    (h : ℝ → ℝ) {L C : ℝ} (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|)
    (hbdd : ∀ x, |h x| ≤ C) :
    Tendsto (fun k => (Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (N k)),
          h ((blockSumScale (N k) (m k))⁻¹ * ∑ i, d k (σ (a k i))))
      atTop (𝓝 (stdGaussianExpect h)) := by
  classical
  have hL : (0 : ℝ) ≤ L := by
    have hx := hlip 1 0
    have h0 : (0 : ℝ) ≤ |h 1 - h 0| := abs_nonneg _
    rw [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at hx
    linarith
  have hNlim : Tendsto (fun k => (N k : ℝ)) atTop atTop := by
    have hsum := hm.atTop_add_atTop hNm
    simpa using hsum
  have hMnlim : Tendsto (fun k => min (m k : ℝ) ((N k : ℝ) - m k)) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [tendsto_atTop.1 hm b, tendsto_atTop.1 hNm b] with k h1 h2
    exact le_min h1 h2
  have hNm1 : Tendsto (fun k => (N k : ℝ) - 1) atTop atTop := by
    have := Filter.tendsto_atTop_add_const_right atTop (-1 : ℝ) hNlim
    simpa [sub_eq_add_neg] using this
  have hinvNm1 : Tendsto (fun k => ((N k : ℝ) - 1)⁻¹) atTop (𝓝 0) := by
    simpa using! hNm1.inv_tendsto_atTop
  refine tendsto_of_eventually_abs_sub_le (Cst := 100 * (L + 1)) (by positivity) ?_
  intro ε hε
  -- the truncation level and the limits attached to it
  have hsqrtlim : Tendsto (fun k => ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k)))
      atTop atTop :=
    Filter.Tendsto.const_mul_atTop hε (Real.tendsto_sqrt_atTop.comp hMnlim)
  have hΛ0 : Tendsto (fun k => (N k : ℝ)⁻¹ *
      truncLoss (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k)) atTop (𝓝 0) := by
    refine Filter.Tendsto.congr (fun k => ?_) (hlind ε hε)
    rw [truncLoss_eq]
  have hμ0 : Tendsto (fun k => (N k : ℝ)⁻¹ *
      ∑ l, truncKeep (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k) l)
      atTop (𝓝 0) := by
    have hinv : Tendsto
        (fun k => (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k)))⁻¹) atTop (𝓝 0) :=
      Filter.Tendsto.congr (fun _ => rfl) hsqrtlim.inv_tendsto_atTop
    have hbnd : ∀ᶠ k in atTop, ‖(N k : ℝ)⁻¹ *
        ∑ l, truncKeep (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k) l‖
        ≤ ((N k : ℝ)⁻¹ * truncLoss (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k))
          * (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k)))⁻¹ := by
      filter_upwards [hsqrtlim.eventually_gt_atTop 0, hNlim.eventually_gt_atTop 0]
        with k hτk hNk
      have hNnat : 0 < N k := by exact_mod_cast hNk
      rw [Real.norm_eq_abs]
      exact abs_mean_truncKeep_le hτk hNnat (d k) (hcent k)
    refine squeeze_zero_norm' hbnd ?_
    have hmul := hΛ0.mul hinv
    rw [mul_zero] at hmul
    exact hmul
  have hP1 : Tendsto (fun k => (N k : ℝ)⁻¹ *
      ∑ l, truncCentred (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k) l ^ 2)
      atTop (𝓝 1) := by
    have hcongr : ∀ᶠ k in atTop, (N k : ℝ)⁻¹ *
        ∑ l, truncCentred (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k) l ^ 2
        = ((N k : ℝ)⁻¹ * ∑ l, d k l ^ 2)
          - ((N k : ℝ)⁻¹ * truncLoss (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k))
          - ((N k : ℝ)⁻¹ *
              ∑ l, truncKeep (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k) l) ^ 2 := by
      filter_upwards [hNlim.eventually_gt_atTop 0] with k hNk
      have hNnat : 0 < N k := by exact_mod_cast hNk
      rw [sum_sq_truncCentred hNnat]
      have hne : ((N k : ℝ)) ≠ 0 := ne_of_gt hNk
      field_simp
    refine Filter.Tendsto.congr' (hcongr.mono fun k hk => hk.symm) ?_
    have hstep := (hvar.sub hΛ0).sub (hμ0.pow 2)
    simpa using hstep
  have hNratio : Tendsto (fun k => (N k : ℝ) * ((N k : ℝ) - 1)⁻¹) atTop (𝓝 1) := by
    have hc : ∀ᶠ k in atTop, (N k : ℝ) * ((N k : ℝ) - 1)⁻¹ = 1 + ((N k : ℝ) - 1)⁻¹ := by
      filter_upwards [hNlim.eventually_ge_atTop 2] with k hNk
      have h2 : ((N k : ℝ) - 1) ≠ 0 := by
        have : (0 : ℝ) < (N k : ℝ) - 1 := by linarith
        exact ne_of_gt this
      field_simp
      ring
    refine Filter.Tendsto.congr' (hc.mono fun k hk => hk.symm) ?_
    simpa using tendsto_const_nhds.add hinvNm1
  have hQ1 : Tendsto (fun k =>
      (∑ l, truncCentred (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k) l ^ 2)
        / ((N k : ℝ) - 1)) atTop (𝓝 1) := by
    have hcongr : ∀ᶠ k in atTop,
        (∑ l, truncCentred (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k) l ^ 2)
          / ((N k : ℝ) - 1)
        = ((N k : ℝ)⁻¹ *
            ∑ l, truncCentred (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k) l ^ 2)
          * ((N k : ℝ) * ((N k : ℝ) - 1)⁻¹) := by
      filter_upwards [hNlim.eventually_ge_atTop 2] with k hNk
      have h1 : ((N k : ℝ)) ≠ 0 := by
        have : (0 : ℝ) < (N k : ℝ) := by linarith
        exact ne_of_gt this
      have h2 : ((N k : ℝ) - 1) ≠ 0 := by
        have : (0 : ℝ) < (N k : ℝ) - 1 := by linarith
        exact ne_of_gt this
      field_simp
    refine Filter.Tendsto.congr' (hcongr.mono fun k hk => hk.symm) ?_
    simpa using hP1.mul hNratio
  have hT30 : Tendsto (fun k =>
      2 * (∑ l, truncCentred (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k) l ^ 2)
        / ((N k : ℝ) * ((N k : ℝ) - 1))) atTop (𝓝 0) := by
    have hcongr : ∀ᶠ k in atTop,
        2 * (∑ l, truncCentred (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k) l ^ 2)
          / ((N k : ℝ) * ((N k : ℝ) - 1))
        = 2 * ((N k : ℝ)⁻¹ *
            ∑ l, truncCentred (ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k))) (d k) l ^ 2)
          * ((N k : ℝ) - 1)⁻¹ := by
      filter_upwards [hNlim.eventually_ge_atTop 2] with k hNk
      have h1 : ((N k : ℝ)) ≠ 0 := by
        have : (0 : ℝ) < (N k : ℝ) := by linarith
        exact ne_of_gt this
      have h2 : ((N k : ℝ) - 1) ≠ 0 := by
        have : (0 : ℝ) < (N k : ℝ) - 1 := by linarith
        exact ne_of_gt this
      field_simp
    refine Filter.Tendsto.congr' (hcongr.mono fun k hk => hk.symm) ?_
    have hc2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    have hstep := (hc2.mul hP1).mul hinvNm1
    simpa using hstep
  filter_upwards [hNlim.eventually_ge_atTop 2, hm.eventually_gt_atTop 0,
    hNm.eventually_gt_atTop 0, hMnlim.eventually_ge_atTop 1,
    Metric.tendsto_nhds.1 hΛ0 (ε ^ 2) (by positivity),
    Metric.tendsto_nhds.1 hQ1 ε hε, Metric.tendsto_nhds.1 hP1 1 one_pos,
    Metric.tendsto_nhds.1 hT30 ε hε] with k hN2 hmk hNmk hMn1 hΛk hQk hPk hT3k
  rw [Real.dist_eq, sub_zero] at hΛk hT3k
  rw [Real.dist_eq] at hQk hPk
  exact abs_avg_blockSum_sub_le_of_trunc hε (a k) (ha k) (d k) (hcent k) hL hlip hbdd
    hN2 hmk hNmk hMn1 hΛk hQk hPk hT3k

/-- **The combinatorial central limit theorem** (Wald–Wolfowitz, Noether, Hoeffding,
Erdős–Rényi, Hájek). Let `d k` be a centred population on `Fin (N k)` with normalized second
moment tending to `1`, and let `a k` sample `m k` distinct positions. If both block sizes
`m k` and `N k - m k` tend to infinity and the populations satisfy Hájek's Lindeberg
condition at scale `√(min (m k) (N k - m k))`, then the block sum standardized by
`blockSumScale` is asymptotically standard normal — stated here in the group-average
c.d.f. form in which randomization distributions are defined.

STATUS (wave 7): DISCHARGED to the single core brick `tendsto_perm_avg_lipschitz` below —
the same theorem tested against *Lipschitz* functions instead of a half-line indicator. The
de-smoothing step performed here is the elementary one: the indicator of `Iic t` is squeezed
between two ramps of width `ε` (`ForMathlib/EsseenSmoothing.ramp`), the ramps are `ε⁻¹`-
Lipschitz and bounded by `1`, their Gaussian expectations bracket `Φ(t ∓ ε)`, and `Φ` is
1-Lipschitz (`ForMathlib/SteinMethod.lipschitzWith_cdf_gaussianReal`), hence continuous, so
letting `ε → 0` costs nothing. -/
theorem tendsto_perm_cdf_blockSum {N m : ℕ → ℕ}
    -- USER-INPUT: at each stage the block is a set of `m k` distinct positions
    (a : ∀ k, Fin (m k) → Fin (N k)) (ha : ∀ k, Function.Injective (a k))
    -- USER-INPUT: the finite populations
    (d : ∀ k, Fin (N k) → ℝ)
    -- USER-INPUT: each population is centred
    (hcent : ∀ k, ∑ l, d k l = 0)
    -- USER-INPUT: both the block and its complement grow
    (hm : Tendsto (fun k => (m k : ℝ)) atTop atTop)
    (hNm : Tendsto (fun k => (N k : ℝ) - m k) atTop atTop)
    -- USER-INPUT: the populations are normalized in the second moment
    (hvar : Tendsto (fun k => (N k : ℝ)⁻¹ * ∑ l, d k l ^ 2) atTop (𝓝 1))
    -- USER-INPUT: Hájek's Lindeberg condition at scale `√(min (m k) (N k - m k))`
    (hlind : ∀ ε > (0 : ℝ), Tendsto (fun k => (N k : ℝ)⁻¹ *
        ∑ l, (if ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k)) ≤ |d k l|
              then d k l ^ 2 else 0)) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun k => (Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (N k)),
          (if ∑ i, d k (σ (a k i)) ≤ t * blockSumScale (N k) (m k) then (1 : ℝ) else 0))
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
  classical
  have hcont : ContinuousAt (fun s : ℝ => cdf (gaussianReal 0 1) s) t :=
    lipschitzWith_cdf_gaussianReal.continuous.continuousAt
  refine tendsto_of_squeeze_continuousAt hcont ?_
  intro ε hε
  -- the two ramp test functions: `ε⁻¹`-Lipschitz and bounded by `1`
  have hrbdd : ∀ (u : ℝ) (x : ℝ), |ramp u ε x| ≤ 1 := fun u x => by
    rw [abs_of_nonneg (ramp_nonneg u ε x)]; exact ramp_le_one u ε x
  have hU := tendsto_perm_avg_lipschitz a ha d hcent hm hNm hvar hlind (ramp t ε)
    (fun x y => abs_ramp_sub_ramp_le hε x y) (hrbdd t)
  have hL := tendsto_perm_avg_lipschitz a ha d hcent hm hNm hvar hlind (ramp (t - ε) ε)
    (fun x y => abs_ramp_sub_ramp_le hε x y) (hrbdd (t - ε))
  -- the Gaussian expectations of the two ramps bracket the limit c.d.f.
  have hUb : stdGaussianExpect (ramp t ε) ≤ cdf (gaussianReal 0 1) (t + ε) := by
    have hb := integral_ramp_le_measure_Iic (gaussianReal 0 1) hε t
    rw [stdGaussianExpect, cdf_eq_real, measureReal_def]
    exact hb
  have hLb : cdf (gaussianReal 0 1) (t - ε) ≤ stdGaussianExpect (ramp (t - ε) ε) := by
    have hb := measure_Iic_le_integral_ramp (gaussianReal 0 1) hε (t - ε)
    rw [stdGaussianExpect, cdf_eq_real, measureReal_def]
    exact hb
  -- the standardizing scale is eventually positive, and then the indicator is squeezed
  have hscale : ∀ᶠ k in atTop, 0 < blockSumScale (N k) (m k) := by
    filter_upwards [hm.eventually_gt_atTop 0, hNm.eventually_gt_atTop 0] with k h1 h2
    have hN : (0 : ℝ) < (N k : ℝ) := by linarith
    rw [blockSumScale, Real.sqrt_pos]
    exact div_pos (mul_pos h1 h2) hN
  have hsq : ∀ᶠ k in atTop,
      ((Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (N k)),
          ramp (t - ε) ε ((blockSumScale (N k) (m k))⁻¹ * ∑ i, d k (σ (a k i)))
        ≤ (Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (N k)),
            (if ∑ i, d k (σ (a k i)) ≤ t * blockSumScale (N k) (m k) then (1 : ℝ) else 0))
      ∧ ((Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (N k)),
            (if ∑ i, d k (σ (a k i)) ≤ t * blockSumScale (N k) (m k) then (1 : ℝ) else 0)
          ≤ (Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (N k)),
              ramp t ε ((blockSumScale (N k) (m k))⁻¹ * ∑ i, d k (σ (a k i)))) := by
    filter_upwards [hscale] with k hk
    have hiff : ∀ σ : Equiv.Perm (Fin (N k)),
        (∑ i, d k (σ (a k i)) ≤ t * blockSumScale (N k) (m k))
          ↔ (blockSumScale (N k) (m k))⁻¹ * (∑ i, d k (σ (a k i))) ≤ t := by
      intro σ
      rw [inv_mul_le_iff₀ hk, mul_comm]
    have hcinv : (0 : ℝ) ≤ (Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ :=
      inv_nonneg.2 (Nat.cast_nonneg _)
    constructor
    · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) hcinv
      by_cases hσ : ∑ i, d k (σ (a k i)) ≤ t * blockSumScale (N k) (m k)
      · rw [if_pos hσ]; exact ramp_le_one _ _ _
      · rw [if_neg hσ]
        refine le_of_eq (ramp_eq_zero_of_le hε ?_)
        have hnot : ¬ ((blockSumScale (N k) (m k))⁻¹ * (∑ i, d k (σ (a k i))) ≤ t) :=
          fun hcon => hσ ((hiff σ).2 hcon)
        rw [not_le] at hnot
        linarith
    · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) hcinv
      by_cases hσ : ∑ i, d k (σ (a k i)) ≤ t * blockSumScale (N k) (m k)
      · rw [if_pos hσ, ramp_eq_one_of_le hε ((hiff σ).1 hσ)]
      · rw [if_neg hσ]; exact ramp_nonneg _ _ _
  -- close the squeeze
  filter_upwards [hsq, Metric.tendsto_nhds.1 hU ε hε, Metric.tendsto_nhds.1 hL ε hε]
    with k hk hUk hLk
  rw [Real.dist_eq, abs_lt] at hUk hLk
  exact ⟨by linarith [hk.1, hLk.1], by linarith [hk.2, hUk.2]⟩

end StatLean.HypothesisTesting
