module
public import StatLean.CausalInference.Randomized.CompleteRandomization
public import StatLean.CausalInference.Core.FinitePopulation

@[expose] public section

/-!
# The difference-in-means estimator as a linear statistic in the assignment

The key structural fact behind Neyman's theorem: on the support of complete randomization
the difference in means is an **affine function of the treatment indicators**,

$$\hat\tau(Z)=\sum_i\Bigl(\frac{Y_i(1)}{n_1}+\frac{Y_i(0)}{n_0}\Bigr)Z_i
              -\frac1{n_0}\sum_i Y_i(0),$$

so its mean and variance follow from the first two assignment moments. The arm means
themselves are linear in `Z` as well.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §4.2: the difference-in-means estimator and the
proof of Theorem 4.1, which is organized exactly around this linearization; Lemma C.2
(§C.1, p. 434) for the sample-mean moments. (`Ding §4.2; Lemma C.2`.)

**Proof formalization notes.** The arm sizes are constant on the support (`card_armIdx_*`
in `CompleteRandomization`), which is what makes the coefficients deterministic; off the
support the statements say nothing. Sums over the treated set are rewritten as sums over
all units weighted by `ind (z i)`, which is the form `HypergeometricMoments.var_linear`
consumes.
-/

namespace StatLean.CausalInference

variable {n n₁ n₀ : ℕ}

/-- A sum over the treated units is a weighted sum over all units. -/
theorem sum_armIdx_true_eq_sum_ind (z : Assignment n) (v : Fin n → ℝ) :
    ∑ i ∈ armIdx z true, v i = ∑ i, v i * ind (z i) := by
  rw [armIdx, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases hzi : z i <;> simp [ind]

/-- A sum over the control units is a weighted sum over all units. -/
theorem sum_armIdx_false_eq_sum_ind (z : Assignment n) (v : Fin n → ℝ) :
    ∑ i ∈ armIdx z false, v i = ∑ i, v i * (1 - ind (z i)) := by
  rw [armIdx, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases hzi : z i <;> simp [ind]

/-- The **treated sample mean is linear in the assignment**: on the support of complete
randomization, `Ȳ₁ = n₁⁻¹∑ᵢ Yᵢ(1)Zᵢ`. -/
theorem armMean_true_eq (S : ScienceTable n) (h : n₁ ≤ n) {z : Assignment n}
    (hz : z ∈ completeSupport n n₁)
    -- LEAN-ONLY: a nonempty treated arm, else the mean is a junk value; no scope change
    (h1 : 0 < n₁) :
    armMean S z true = (n₁ : ℝ)⁻¹ * ∑ i, S.y1 i * ind (z i) := by
  have hbody : ∑ i, S.observed z i * ind (z i) = ∑ i, S.y1 i * ind (z i) :=
    Finset.sum_congr rfl fun i _ => by
      cases hzi : z i
      · simp [ind]
      · rw [observed_eq_y1 S hzi]
  rw [armMean, card_armIdx_true h hz, sum_armIdx_true_eq_sum_ind, hbody]

/-- The **control sample mean is affine in the assignment**:
`Ȳ₀ = n₀⁻¹∑ᵢ Yᵢ(0)(1 - Zᵢ)`. -/
theorem armMean_false_eq (S : ScienceTable n) (hsum : n₁ + n₀ = n) (h : n₁ ≤ n)
    {z : Assignment n} (hz : z ∈ completeSupport n n₁)
    -- LEAN-ONLY: a nonempty control arm, else the mean is a junk value; no scope change
    (h0 : 0 < n₀) :
    armMean S z false = (n₀ : ℝ)⁻¹ * ∑ i, S.y0 i * (1 - ind (z i)) := by
  have hcard : (armIdx z false).card = n₀ := by
    rw [card_armIdx_false h hz]; omega
  have hbody : ∑ i, S.observed z i * (1 - ind (z i)) = ∑ i, S.y0 i * (1 - ind (z i)) :=
    Finset.sum_congr rfl fun i _ => by
      cases hzi : z i
      · rw [observed_eq_y0 S hzi]
      · simp [ind]
  rw [armMean, hcard, sum_armIdx_false_eq_sum_ind, hbody]

/-- **The linearization of `τ̂`** (Ding §4.2): on the support of complete randomization the
difference in means is affine in the treatment indicators, with deterministic
coefficients `cᵢ = Yᵢ(1)/n₁ + Yᵢ(0)/n₀`. -/
theorem diffInMeans_eq_affine (S : ScienceTable n) (hsum : n₁ + n₀ = n) (h : n₁ ≤ n)
    {z : Assignment n} (hz : z ∈ completeSupport n n₁)
    -- LEAN-ONLY: both arms nonempty, else the arm means are junk values; no scope change
    (h1 : 0 < n₁) (h0 : 0 < n₀) :
    diffInMeans S z
      = (∑ i, (S.y1 i / (n₁ : ℝ) + S.y0 i / (n₀ : ℝ)) * ind (z i))
          - (n₀ : ℝ)⁻¹ * ∑ i, S.y0 i := by
  have key : ∀ i : Fin n,
      (n₁ : ℝ)⁻¹ * (S.y1 i * ind (z i)) - (n₀ : ℝ)⁻¹ * (S.y0 i * (1 - ind (z i)))
        = (S.y1 i / (n₁ : ℝ) + S.y0 i / (n₀ : ℝ)) * ind (z i) - (n₀ : ℝ)⁻¹ * S.y0 i :=
    fun i => by ring
  rw [diffInMeans, armMean_true_eq S h hz h1, armMean_false_eq S hsum h hz h0]
  calc (n₁ : ℝ)⁻¹ * ∑ i, S.y1 i * ind (z i)
        - (n₀ : ℝ)⁻¹ * ∑ i, S.y0 i * (1 - ind (z i))
      = ∑ i, ((n₁ : ℝ)⁻¹ * (S.y1 i * ind (z i))
              - (n₀ : ℝ)⁻¹ * (S.y0 i * (1 - ind (z i)))) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = ∑ i, ((S.y1 i / (n₁ : ℝ) + S.y0 i / (n₀ : ℝ)) * ind (z i) - (n₀ : ℝ)⁻¹ * S.y0 i) :=
        Finset.sum_congr rfl fun i _ => key i
    _ = (∑ i, (S.y1 i / (n₁ : ℝ) + S.y0 i / (n₀ : ℝ)) * ind (z i))
          - (n₀ : ℝ)⁻¹ * ∑ i, S.y0 i := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The mean of the linearizing coefficients: `c̄ = ȳ(1)/n₁ + ȳ(0)/n₀`. -/
theorem popMean_affineCoeff (S : ScienceTable n) :
    popMean (fun i => S.y1 i / (n₁ : ℝ) + S.y0 i / (n₀ : ℝ))
      = popMean S.y1 / (n₁ : ℝ) + popMean S.y0 / (n₀ : ℝ) := by
  simp only [popMean, Finset.sum_add_distrib, ← Finset.sum_div]
  ring

end StatLean.CausalInference
