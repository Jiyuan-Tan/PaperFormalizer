module
public import StatLean.CausalInference.Randomized.DifferenceInMeans

@[expose] public section

/-!
# Neyman's theorem — unbiasedness and the exact randomization variance

The first two parts of the flagship finite-population result. Under complete randomization
with `n₁` treated and `n₀` control units,

$$\mathbb E[\hat\tau]=\tau,\qquad
  \operatorname{Var}(\hat\tau)=\frac{S^2(1)}{n_1}+\frac{S^2(0)}{n_0}-\frac{S^2(\tau)}{n},$$

where `S²(1)`, `S²(0)`, `S²(τ)` are the finite-population variances of the treated
potential outcomes, the control potential outcomes and the individual effects. The
variance-estimator half of Ding's Theorem 4.1 is in `Randomized.VarianceEstimator`.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Theorem 4.1(1)–(2) (§4.2, pp. 44–45) and its
supporting Lemma 4.1 (§4.1, p. 44: `2S(1,0) = S²(1) + S²(0) - S²(τ)`), under the
completely randomized experiment of Definition 3.1. (`Ding Theorem 4.1; Lemma 4.1`.) The
same repeated-sampling analysis is in G. W. Imbens and D. B. Rubin, *Causal Inference for
Statistics, Social, and Biomedical Sciences*, Cambridge University Press, 2015, ch. 6.
(`IR ch. 6`.)

**Proof formalization notes.** Both parts go through the linearization
`diffInMeans_eq_affine`: unbiasedness from `completeDesign_expect_ind` (`E[Zᵢ] = n₁/n`),
and the variance from `completeDesign_var_linear` (the sampling-without-replacement
variance of a linear statistic) followed by the algebraic identity of Lemma 4.1. The
constant `n₁n₀/(n(n-1))` multiplying `∑(cᵢ - c̄)²` with `cᵢ = Yᵢ(1)/n₁ + Yᵢ(0)/n₀`
rearranges into the three-term form; that rearrangement is where Lemma 4.1 enters.

**Bibliographic comments.** J. Neyman, "On the application of probability theory to
agricultural experiments. Essay on principles. Section 9" (1923), translated by
D. M. Dabrowska and T. P. Speed, *Statist. Sci.* **5** (1990), 465–472.
-/

namespace StatLean.CausalInference

variable {n n₁ n₀ : ℕ}

/-! ### LEAN-ONLY helpers: linearity of `Design.expect` and the centred-sum identity

`Design.expect` is a normalized `Finset` sum over the support, so the four facts below —
that it only depends on the values on the support, that it commutes with finite sums and
scalar multiples, and that subtracting a constant shifts the mean and leaves the variance
alone — are pure big-operator bookkeeping. They carry no probabilistic content. -/

/-- Expectations only see the values on the support. -/
private lemma expect_congr (D : Design n) {f g : Assignment n → ℝ}
    (hfg : ∀ z ∈ D.support, f z = g z) : D.expect f = D.expect g := by
  simp only [Design.expect]
  exact congrArg _ (Finset.sum_congr rfl hfg)

/-- Variances only see the values on the support. -/
private lemma var_congr (D : Design n) {f g : Assignment n → ℝ}
    (hfg : ∀ z ∈ D.support, f z = g z) : D.var f = D.var g := by
  simp only [Design.var]
  rw [expect_congr D hfg]
  exact expect_congr D fun z hz => by rw [hfg z hz]

/-- `Design.expect` commutes with finite sums. -/
private lemma expect_sum (D : Design n) {ι : Type*} (s : Finset ι) (f : ι → Assignment n → ℝ) :
    D.expect (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, D.expect (f i) := by
  simp only [Design.expect, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- `Design.expect` is homogeneous. -/
private lemma expect_const_mul (D : Design n) (a : ℝ) (f : Assignment n → ℝ) :
    D.expect (fun z => a * f z) = a * D.expect f := by
  simp only [Design.expect, ← Finset.mul_sum]
  ring

/-- Subtracting a constant shifts the mean by that constant. -/
private lemma expect_const_sub (D : Design n) (f : Assignment n → ℝ) (a : ℝ) :
    D.expect (fun z => f z - a) = D.expect f - a := by
  have hc : ((D.support.card : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr D.support_nonempty).ne'
  simp only [Design.expect, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_sub]
  field_simp

/-- Subtracting a constant does not change the variance. -/
private lemma var_sub_const (D : Design n) (f : Assignment n → ℝ) (a : ℝ) :
    D.var (fun z => f z - a) = D.var f := by
  simp only [Design.var, expect_const_sub]
  exact congrArg _ (funext fun z => by ring)

/-- The centred sum of squares of the individual effects, in terms of the centred sums of
the two potential-outcome vectors. This is the sum-level form of Lemma 4.1. -/
private lemma sum_unitEffect_sq (S : ScienceTable n) :
    ∑ i, (S.unitEffect i - popMean S.unitEffect) ^ 2
      = (∑ i, (S.y1 i - popMean S.y1) ^ 2) + (∑ i, (S.y0 i - popMean S.y0) ^ 2)
        - 2 * ∑ i, (S.y1 i - popMean S.y1) * (S.y0 i - popMean S.y0) := by
  have hmean : popMean S.unitEffect = popMean S.y1 - popMean S.y0 := finiteATE_eq_sub_popMean S
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmean]
  simp only [ScienceTable.unitEffect]
  ring

/-- **Lemma 4.1** (Ding §4.1, p. 44): the finite-population variance identity
`2S(1,0) = S²(1) + S²(0) - S²(τ)` linking the covariance of the potential outcomes to the
variance of the individual effects. -/
theorem two_mul_popCov_eq (S : ScienceTable n) :
    2 * popCov S.y1 S.y0 = popVar S.y1 + popVar S.y0 - popVar S.unitEffect := by
  simp only [popCov, popVar, sum_unitEffect_sq S]
  ring

/-- **Neyman's theorem, part 1** (Ding Theorem 4.1(1)): under complete randomization the
difference in means is unbiased for the finite-population average causal effect. -/
theorem differenceInMeans_unbiased (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    -- USER-INPUT: both arms nonempty, as in the CRE of Ding Definition 3.1
    (h1 : 0 < n₁) (h0 : 0 < n₀) :
    (completeDesign n n₁ (by omega)).expect (diffInMeans S) = S.finiteATE := by
  have h : n₁ ≤ n := by omega
  change (completeDesign n n₁ h).expect (diffInMeans S) = S.finiteATE
  have hn1 : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h1.ne'
  have hn0 : (n₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.ne'
  have hnn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : (n₁ : ℝ) + (n₀ : ℝ) = (n : ℝ) := by exact_mod_cast hsum
  have hsum' : (n₁ : ℝ) + (n₀ : ℝ) ≠ 0 := by rw [hcast]; exact hnn
  -- the affine form of `τ̂`, valid on the support, then linearity of the expectation
  have hE : (completeDesign n n₁ h).expect (diffInMeans S)
      = (∑ i, (S.y1 i / (n₁ : ℝ) + S.y0 i / (n₀ : ℝ)) * ((n₁ : ℝ) / (n : ℝ)))
          - (n₀ : ℝ)⁻¹ * ∑ i, S.y0 i := by
    rw [expect_congr _ (fun z hz => diffInMeans_eq_affine S hsum h hz h1 h0),
      expect_const_sub, expect_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [expect_const_mul, completeDesign_expect_ind]
  have hlin : ∑ i, (S.y1 i / (n₁ : ℝ) + S.y0 i / (n₀ : ℝ)) * ((n₁ : ℝ) / (n : ℝ))
      = (n : ℝ)⁻¹ * (∑ i, S.y1 i) + ((n₁ : ℝ) / ((n₀ : ℝ) * (n : ℝ))) * ∑ i, S.y0 i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hE, hlin, finiteATE_eq_sub_popMean, popMean, popMean, ← hcast]
  field_simp
  ring

/-- **Neyman's theorem, part 2** (Ding Theorem 4.1(2), eqs. (4.1)–(4.2)): the exact
randomization variance of the difference in means. The third term `-S²(τ)/n` is the
finite-population correction; it is the term that cannot be estimated from the data. -/
theorem differenceInMeans_variance (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    -- USER-INPUT: both arms nonempty, as in the CRE of Ding Definition 3.1
    (h1 : 0 < n₁) (h0 : 0 < n₀)
    -- LEAN-ONLY: at least two units, else the divisor `n - 1` in `popVar` vanishes
    (hn : 2 ≤ n) :
    (completeDesign n n₁ (by omega)).var (diffInMeans S)
      = popVar S.y1 / (n₁ : ℝ) + popVar S.y0 / (n₀ : ℝ) - popVar S.unitEffect / (n : ℝ) := by
  have h : n₁ ≤ n := by omega
  change (completeDesign n n₁ h).var (diffInMeans S) = _
  have hn1 : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h1.ne'
  have hn0 : (n₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.ne'
  have hcast : (n₁ : ℝ) + (n₀ : ℝ) = (n : ℝ) := by exact_mod_cast hsum
  have hsum' : (n₁ : ℝ) + (n₀ : ℝ) ≠ 0 := by
    rw [hcast]; exact Nat.cast_ne_zero.mpr (by omega)
  have hsub1 : (n₁ : ℝ) + (n₀ : ℝ) - 1 ≠ 0 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [hcast]; linarith
  -- the variance of the affine form: the constant drops, the linear part is `var_linear`
  have hVar : (completeDesign n n₁ h).var (diffInMeans S)
      = ((n₁ : ℝ) * ((n : ℝ) - (n₁ : ℝ))) / ((n : ℝ) * ((n : ℝ) - 1))
          * ∑ i, ((S.y1 i / (n₁ : ℝ) + S.y0 i / (n₀ : ℝ))
              - popMean (fun i => S.y1 i / (n₁ : ℝ) + S.y0 i / (n₀ : ℝ))) ^ 2 := by
    rw [var_congr _ (fun z hz => diffInMeans_eq_affine S hsum h hz h1 h0), var_sub_const]
    exact completeDesign_var_linear h hn _
  -- expand the centred coefficients
  have hexp : ∑ i, ((S.y1 i / (n₁ : ℝ) + S.y0 i / (n₀ : ℝ))
        - popMean (fun i => S.y1 i / (n₁ : ℝ) + S.y0 i / (n₀ : ℝ))) ^ 2
      = ((n₁ : ℝ)⁻¹) ^ 2 * (∑ i, (S.y1 i - popMean S.y1) ^ 2)
        + 2 * ((n₁ : ℝ)⁻¹ * (n₀ : ℝ)⁻¹)
            * (∑ i, (S.y1 i - popMean S.y1) * (S.y0 i - popMean S.y0))
        + ((n₀ : ℝ)⁻¹) ^ 2 * (∑ i, (S.y0 i - popMean S.y0) ^ 2) := by
    rw [popMean_affineCoeff, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hVar, hexp, popVar, popVar, popVar, sum_unitEffect_sq S]
  obtain ⟨A, hA⟩ : ∃ A, ∑ i, (S.y1 i - popMean S.y1) ^ 2 = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, ∑ i, (S.y0 i - popMean S.y0) ^ 2 = B := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, ∑ i, (S.y1 i - popMean S.y1) * (S.y0 i - popMean S.y0) = C := ⟨_, rfl⟩
  rw [hA, hB, hC, ← hcast]
  field_simp
  ring

/-- Under a constant treatment effect the finite-population correction vanishes, so the
randomization variance is the familiar two-term expression (Ding §4.2). -/
theorem differenceInMeans_variance_of_constantEffect (S : ScienceTable n) {τ : ℝ}
    -- USER-INPUT: the additive constant-effect model; Ding §4.2
    (hconst : S.ConstantEffect τ) (hsum : n₁ + n₀ = n) (h1 : 0 < n₁) (h0 : 0 < n₀)
    (hn : 2 ≤ n) :
    (completeDesign n n₁ (by omega)).var (diffInMeans S)
      = popVar S.y1 / (n₁ : ℝ) + popVar S.y0 / (n₀ : ℝ) := by
  have hnn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmean : popMean S.unitEffect = τ := by
    have hs : ∑ i, S.unitEffect i = (n : ℝ) * τ := by
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hconst i]
      simp
    rw [popMean, hs, ← mul_assoc, inv_mul_cancel₀ hnn, one_mul]
  have hzero : popVar S.unitEffect = 0 := by
    have hterm : ∀ i : Fin n, (S.unitEffect i - popMean S.unitEffect) ^ 2 = 0 := by
      intro i; rw [hconst i, hmean]; ring
    rw [popVar, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i]
    simp
  have key := differenceInMeans_variance (n₁ := n₁) (n₀ := n₀) S hsum h1 h0 hn
  rw [hzero] at key
  simpa using key

end StatLean.CausalInference
