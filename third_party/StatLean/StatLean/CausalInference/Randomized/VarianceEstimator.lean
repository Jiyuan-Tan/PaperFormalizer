module
public import StatLean.CausalInference.Randomized.Neyman

@[expose] public section

/-!
# Neyman's variance estimator — unbiasedness of the arm variances and conservativeness

The third part of Neyman's theorem. The arm sample variances are unbiased for the
corresponding finite-population variances, so

$$\mathbb E[\hat V]=\frac{S^2(1)}{n_1}+\frac{S^2(0)}{n_0}
  \quad\Longrightarrow\quad
  \mathbb E[\hat V]-\operatorname{Var}(\hat\tau)=\frac{S^2(\tau)}{n}\ \ge 0 :$$

the estimator `V̂` overestimates the true randomization variance by exactly the
unidentifiable finite-population correction, and is *exactly* unbiased precisely when the
treatment effect is constant.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Theorem 4.1(3) (§4.2, pp. 44–45), with the
unbiasedness of the arm sample variances from Lemma C.3 (§C.1, p. 434: sample variances
of a simple random sample are unbiased). (`Ding Theorem 4.1(3); Lemma C.3`.) Compare
G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
Sciences*, Cambridge University Press, 2015, ch. 6. (`IR ch. 6`.)

**Proof formalization notes.** `armVar_true_unbiased` is Lemma C.3 for the treated arm and
is the only genuinely new computation: expand
`ŝ²(1) = (n₁-1)⁻¹(∑_{i:Zᵢ=1}Yᵢ(1)² - n₁Ȳ₁²)`, take expectations with
`completeDesign_expect_ind` on the first term and `E[Ȳ₁²] = Var(Ȳ₁) + (ȳ(1))²` on the
second, and substitute `Var(Ȳ₁) = n₀S²(1)/(n·n₁)` from `completeDesign_var_linear`. Each
arm needs at least two units for its sample variance to be defined (divisor `card - 1`),
which is Ding's standing `n₁, n₀ ≥ 2` for this part.

**Bibliographic comments.** The conservativeness of `V̂` and its exactness under a
constant effect are already in Neyman (1923); the point that the excess `S²(τ)/n` is
unidentifiable from a single experiment is discussed at length in ch. 4 of the reference.
-/

namespace StatLean.CausalInference

variable {n n₁ n₀ : ℕ}

/-! ### LEAN-ONLY private helpers: `Design.expect` algebra and raw-moment identities

`Design.expect` is a normalized `Finset` sum, so linearity is bookkeeping; the four
`expect_*` lemmas below and `var_eq` carry no mathematical content. (`CompleteRandomization`
has a private `dvar_eq` of the same shape; private names do not cross files, so the
two-line derivation is repeated here.) -/

/-- Expectations only see the support. -/
private lemma expect_congr (D : Design n) {f g : Assignment n → ℝ}
    (h : ∀ z ∈ D.support, f z = g z) : D.expect f = D.expect g := by
  simp only [Design.expect]
  rw [Finset.sum_congr rfl h]

/-- The expectation of a constant. -/
private lemma expect_const (D : Design n) (c : ℝ) : D.expect (fun _ => c) = c := by
  have hc : ((D.support.card : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr D.support_nonempty).ne'
  simp only [Design.expect, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- Additivity of the expectation. -/
private lemma expect_add (D : Design n) (f g : Assignment n → ℝ) :
    D.expect (fun z => f z + g z) = D.expect f + D.expect g := by
  simp only [Design.expect, Finset.sum_add_distrib, mul_add]

/-- Subtractivity of the expectation. -/
private lemma expect_sub (D : Design n) (f g : Assignment n → ℝ) :
    D.expect (fun z => f z - g z) = D.expect f - D.expect g := by
  simp only [Design.expect, Finset.sum_sub_distrib, mul_sub]

/-- Scalars pull out of the expectation. -/
private lemma expect_const_mul (D : Design n) (c : ℝ) (f : Assignment n → ℝ) :
    D.expect (fun z => c * f z) = c * D.expect f := by
  simp only [Design.expect, ← Finset.mul_sum]
  ring

/-- Finite sums pull out of the expectation. -/
private lemma expect_sum {ι : Type*} (D : Design n) (s : Finset ι)
    (F : ι → Assignment n → ℝ) :
    D.expect (fun z => ∑ i ∈ s, F i z) = ∑ i ∈ s, D.expect (F i) := by
  simp only [Design.expect, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- `Var(f) = E[f²] - (E f)²`. -/
private lemma var_eq (D : Design n) (f : Assignment n → ℝ) :
    D.var f = D.expect (fun z => f z ^ 2) - (D.expect f) ^ 2 := by
  have h2 : D.var f = D.expect (fun z => (f z - D.expect f) ^ 2) := rfl
  have h3 : D.expect (fun z => (f z - D.expect f) ^ 2)
      = D.expect (fun z => (f z ^ 2 - (2 * D.expect f) * f z) + (D.expect f) ^ 2) :=
    expect_congr D fun z _ => by ring
  have h4 : D.expect (fun z => (f z ^ 2 - (2 * D.expect f) * f z) + (D.expect f) ^ 2)
      = D.expect (fun z => f z ^ 2 - (2 * D.expect f) * f z)
        + D.expect (fun _ => (D.expect f) ^ 2) := expect_add D _ _
  have h5 : D.expect (fun z => f z ^ 2 - (2 * D.expect f) * f z)
      = D.expect (fun z => f z ^ 2) - D.expect (fun z => (2 * D.expect f) * f z) :=
    expect_sub D _ _
  have h6 : D.expect (fun z => (2 * D.expect f) * f z) = (2 * D.expect f) * D.expect f :=
    expect_const_mul D _ _
  rw [h2, h3, h4, h5, h6, expect_const]
  ring

/-- Subtracting a random variable from a constant does not change the variance. -/
private lemma var_const_sub (D : Design n) (a : ℝ) (f : Assignment n → ℝ) :
    D.var (fun z => a - f z) = D.var f := by
  have hE : D.expect (fun z => a - f z) = a - D.expect f := by
    have h1 : D.expect (fun z => (fun _ : Assignment n => a) z - f z)
        = D.expect (fun _ : Assignment n => a) - D.expect f := expect_sub D _ _
    rwa [expect_const] at h1
  have h2 : D.var (fun z => a - f z)
      = D.expect (fun z => ((a - f z) - D.expect (fun z => a - f z)) ^ 2) := rfl
  rw [h2, hE, show D.var f = D.expect (fun z => (f z - D.expect f) ^ 2) from rfl]
  exact expect_congr D fun z _ => by ring

/-- Expansion of a sum of squared deviations from an arbitrary centre. -/
private lemma sum_sq_sub {ι : Type*} (T : Finset ι) (f : ι → ℝ) (m : ℝ) :
    ∑ i ∈ T, (f i - m) ^ 2
      = (∑ i ∈ T, f i ^ 2) - 2 * m * (∑ i ∈ T, f i) + (T.card : ℝ) * m ^ 2 := by
  calc ∑ i ∈ T, (f i - m) ^ 2
      = ∑ i ∈ T, (f i ^ 2 - (2 * m) * f i + m ^ 2) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = (∑ i ∈ T, f i ^ 2) - (2 * m) * (∑ i ∈ T, f i) + (T.card : ℝ) * m ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum]
    _ = _ := by ring

/-- The population total in terms of the population mean. -/
private lemma sum_eq_mul_popMean (v : Fin n → ℝ) (hn : 2 ≤ n) :
    ∑ i, v i = (n : ℝ) * popMean v := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  rw [popMean, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]

/-- The total sum of squared deviations is `(n-1)S²`. -/
private lemma sum_sq_dev (v : Fin n → ℝ) (hn : 2 ≤ n) :
    ∑ i, (v i - popMean v) ^ 2 = ((n : ℝ) - 1) * popVar v := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  rw [popVar, ← mul_assoc, mul_inv_cancel₀ hn1, one_mul]

/-- The raw-moment identity `∑ vᵢ² = (n-1)S²(v) + n v̄²`. -/
private lemma sum_sq_eq (v : Fin n → ℝ) (hn : 2 ≤ n) :
    ∑ i, v i ^ 2 = ((n : ℝ) - 1) * popVar v + (n : ℝ) * popMean v ^ 2 := by
  have hexp := sum_sq_sub (Finset.univ : Finset (Fin n)) v (popMean v)
  simp only [Finset.card_univ, Fintype.card_fin] at hexp
  rw [sum_sq_dev v hn, sum_eq_mul_popMean v hn] at hexp
  linarith

/-- The population mean commutes with division by a scalar. -/
private lemma popMean_div (v : Fin n → ℝ) (c : ℝ) :
    popMean (fun i => v i / c) = popMean v / c := by
  simp only [popMean, ← Finset.sum_div]
  ring

/-- The sum of squared deviations of a rescaled vector. -/
private lemma sum_sq_dev_div (v : Fin n → ℝ) (c : ℝ) (hn : 2 ≤ n) :
    ∑ i, (v i / c - popMean (fun j => v j / c)) ^ 2 = (((n : ℝ) - 1) * popVar v) / c ^ 2 := by
  rw [popMean_div v c, ← sum_sq_dev v hn, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by rw [div_sub_div_same, div_pow]

/-- A finite-population variance is nonnegative. -/
private lemma popVar_nonneg (v : Fin n → ℝ) (hn : 2 ≤ n) : 0 ≤ popVar v := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [popVar]
  exact mul_nonneg (inv_nonneg.mpr (by linarith))
    (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-! ### LEAN-ONLY private helper: the common core of the two arms

Both arms of Lemma C.3 are the same computation for a weight function `W` with
`E[Wᵢ] = m/n` (`W = Z` and `m = n₁` for the treated arm, `W = 1 - Z` and `m = n₀` for the
control arm). Isolating it here avoids running the argument twice. -/

/-- **The engine of Lemma C.3.** If the arm sample variance `A` has, on the support, the
raw-moment form `(m-1)⁻¹(∑ᵢ vᵢ²Wᵢ - m(∑ᵢ(vᵢ/m)Wᵢ)²)`, the weights have mean `m/n`, and the
arm mean `∑ᵢ(vᵢ/m)Wᵢ` has variance `(n-m)/(nm)·S²(v)`, then `E[A] = S²(v)`. -/
private lemma armVar_unbiased_core (D : Design n) (m : ℕ) (v : Fin n → ℝ)
    (W : Assignment n → Fin n → ℝ) (A : Assignment n → ℝ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hE : ∀ i, D.expect (fun z => W z i) = (m : ℝ) / (n : ℝ))
    (hV : D.var (fun z => ∑ i, (v i / (m : ℝ)) * W z i)
            = ((n : ℝ) - (m : ℝ)) / ((n : ℝ) * (m : ℝ)) * popVar v)
    (hA : ∀ z ∈ D.support, A z = ((m : ℝ) - 1)⁻¹ *
            ((∑ i, v i ^ 2 * W z i) - (m : ℝ) * (∑ i, (v i / (m : ℝ)) * W z i) ^ 2)) :
    D.expect A = popVar v := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hn1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hm1 : (m : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  -- the arm mean is unbiased for the population mean
  have hEg : D.expect (fun z => ∑ i, (v i / (m : ℝ)) * W z i) = popMean v := by
    have h1 : D.expect (fun z => ∑ i, (v i / (m : ℝ)) * W z i)
        = ∑ i, D.expect (fun z => (v i / (m : ℝ)) * W z i) :=
      expect_sum D Finset.univ fun i z => (v i / (m : ℝ)) * W z i
    have h2 : ∀ i : Fin n, D.expect (fun z => (v i / (m : ℝ)) * W z i) = v i / (n : ℝ) := by
      intro i
      rw [expect_const_mul D (v i / (m : ℝ)) fun z => W z i, hE i]
      field_simp
    have h3 : ∑ i, D.expect (fun z => (v i / (m : ℝ)) * W z i) = ∑ i : Fin n, v i / (n : ℝ) :=
      Finset.sum_congr rfl fun i _ => h2 i
    rw [h1, h3, popMean, ← Finset.sum_div]
    ring
  -- the arm raw second moment
  have hEsq : D.expect (fun z => ∑ i, v i ^ 2 * W z i) = (m : ℝ) / (n : ℝ) * ∑ i, v i ^ 2 := by
    have h1 : D.expect (fun z => ∑ i, v i ^ 2 * W z i)
        = ∑ i, D.expect (fun z => v i ^ 2 * W z i) :=
      expect_sum D Finset.univ fun i z => v i ^ 2 * W z i
    have h2 : ∀ i : Fin n,
        D.expect (fun z => v i ^ 2 * W z i) = v i ^ 2 * ((m : ℝ) / (n : ℝ)) := by
      intro i
      rw [expect_const_mul D (v i ^ 2) fun z => W z i, hE i]
    have h3 : ∑ i, D.expect (fun z => v i ^ 2 * W z i)
        = ∑ i : Fin n, v i ^ 2 * ((m : ℝ) / (n : ℝ)) :=
      Finset.sum_congr rfl fun i _ => h2 i
    rw [h1, h3, ← Finset.sum_mul]
    ring
  -- `E[Ȳ²] = Var(Ȳ) + (E Ȳ)²`
  have hEg2 : D.expect (fun z => (∑ i, (v i / (m : ℝ)) * W z i) ^ 2)
      = ((n : ℝ) - (m : ℝ)) / ((n : ℝ) * (m : ℝ)) * popVar v + popMean v ^ 2 := by
    have hve : D.var (fun z => ∑ i, (v i / (m : ℝ)) * W z i)
        = D.expect (fun z => (∑ i, (v i / (m : ℝ)) * W z i) ^ 2)
          - (D.expect (fun z => ∑ i, (v i / (m : ℝ)) * W z i)) ^ 2 := var_eq D _
    rw [hV, hEg] at hve
    linarith
  -- assemble
  have step : D.expect A = D.expect (fun z => ((m : ℝ) - 1)⁻¹ *
      ((∑ i, v i ^ 2 * W z i) - (m : ℝ) * (∑ i, (v i / (m : ℝ)) * W z i) ^ 2)) :=
    expect_congr D hA
  have hlin : D.expect (fun z => ((m : ℝ) - 1)⁻¹ *
        ((∑ i, v i ^ 2 * W z i) - (m : ℝ) * (∑ i, (v i / (m : ℝ)) * W z i) ^ 2))
      = ((m : ℝ) - 1)⁻¹ * D.expect (fun z =>
          (∑ i, v i ^ 2 * W z i) - (m : ℝ) * (∑ i, (v i / (m : ℝ)) * W z i) ^ 2) :=
    expect_const_mul D _ _
  have hsub : D.expect (fun z =>
        (∑ i, v i ^ 2 * W z i) - (m : ℝ) * (∑ i, (v i / (m : ℝ)) * W z i) ^ 2)
      = D.expect (fun z => ∑ i, v i ^ 2 * W z i)
        - D.expect (fun z => (m : ℝ) * (∑ i, (v i / (m : ℝ)) * W z i) ^ 2) :=
    expect_sub D _ _
  have hcm : D.expect (fun z => (m : ℝ) * (∑ i, (v i / (m : ℝ)) * W z i) ^ 2)
      = (m : ℝ) * D.expect (fun z => (∑ i, (v i / (m : ℝ)) * W z i) ^ 2) :=
    expect_const_mul D _ _
  rw [step, hlin, hsub, hcm, hEsq, hEg2, sum_sq_eq v hn]
  field_simp
  ring

/-- **Unbiasedness of the treated arm sample variance** (Ding Lemma C.3): under complete
randomization, `E[ŝ²(1)] = S²(1)`. -/
theorem armVar_true_unbiased (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    -- USER-INPUT: at least two treated units, so that `ŝ²(1)` is defined; Ding Theorem 4.1(3)
    (h1 : 2 ≤ n₁)
    -- USER-INPUT: a nonempty control arm; Ding Definition 3.1
    (h0 : 0 < n₀) :
    (completeDesign n n₁ (by omega)).expect (fun z => armVar S z true) = popVar S.y1 := by
  have hle : n₁ ≤ n := by omega
  have hn : 2 ≤ n := by omega
  have hn1R : (2 : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast h1
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1ne : (n₁ : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hn0ne : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hnm1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  refine armVar_unbiased_core _ n₁ _ (fun z i => ind (z i)) _ hn h1 ?_ ?_ ?_
  · intro i
    exact completeDesign_expect_ind hle i
  · rw [completeDesign_var_linear hle hn fun i => S.y1 i / (n₁ : ℝ),
      sum_sq_dev_div S.y1 (n₁ : ℝ) hn]
    field_simp
  · intro z hz
    have hcard : (armIdx z true).card = n₁ := card_armIdx_true hle hz
    have hM : armMean S z true = (n₁ : ℝ)⁻¹ * ∑ i, S.y1 i * ind (z i) :=
      armMean_true_eq S hle hz (by omega)
    have hobs : ∑ i ∈ armIdx z true, (S.observed z i - armMean S z true) ^ 2
        = ∑ i ∈ armIdx z true, (S.y1 i - armMean S z true) ^ 2 :=
      Finset.sum_congr rfl fun i hi => by
        rw [observed_eq_y1 S (by simpa [armIdx] using hi)]
    have hsum1 : ∑ i ∈ armIdx z true, S.y1 i = ∑ i, S.y1 i * ind (z i) :=
      sum_armIdx_true_eq_sum_ind z S.y1
    have hsum2 : ∑ i ∈ armIdx z true, S.y1 i ^ 2 = ∑ i, S.y1 i ^ 2 * ind (z i) :=
      sum_armIdx_true_eq_sum_ind z fun i => S.y1 i ^ 2
    have hsumM : ∑ i, S.y1 i * ind (z i) = (n₁ : ℝ) * armMean S z true := by
      rw [hM, ← mul_assoc, mul_inv_cancel₀ hn1ne, one_mul]
    have hgM : ∑ i, (S.y1 i / (n₁ : ℝ)) * ind (z i) = armMean S z true := by
      have hr : ∑ i, (S.y1 i / (n₁ : ℝ)) * ind (z i)
          = (n₁ : ℝ)⁻¹ * ∑ i, S.y1 i * ind (z i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hr, hM]
    rw [armVar, hobs, sum_sq_sub (armIdx z true) S.y1 (armMean S z true), hcard, hsum1,
      hsum2, hgM, hsumM]
    ring

/-- **Unbiasedness of the control arm sample variance** (Ding Lemma C.3):
`E[ŝ²(0)] = S²(0)`. -/
theorem armVar_false_unbiased (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    -- USER-INPUT: a nonempty treated arm; Ding Definition 3.1
    (h1 : 0 < n₁)
    -- USER-INPUT: at least two control units, so that `ŝ²(0)` is defined; Ding Theorem 4.1(3)
    (h0 : 2 ≤ n₀) :
    (completeDesign n n₁ (by omega)).expect (fun z => armVar S z false) = popVar S.y0 := by
  have hle : n₁ ≤ n := by omega
  have hn : 2 ≤ n := by omega
  have hcast : (n₁ : ℝ) + (n₀ : ℝ) = (n : ℝ) := by exact_mod_cast hsum
  have hn0R : (2 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast h0
  have hn1R : (1 : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast h1
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0ne : (n₀ : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hnm1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have e1 : (n : ℝ) - (n₁ : ℝ) = (n₀ : ℝ) := by linarith
  have e2 : (n : ℝ) - (n₀ : ℝ) = (n₁ : ℝ) := by linarith
  refine armVar_unbiased_core _ n₀ _ (fun z i => 1 - ind (z i)) _ hn h0 ?_ ?_ ?_
  · intro i
    have hs : (completeDesign n n₁ hle).expect (fun z => (fun _ : Assignment n => (1 : ℝ)) z
          - (fun z => ind (z i)) z)
        = (completeDesign n n₁ hle).expect (fun _ : Assignment n => (1 : ℝ))
          - (completeDesign n n₁ hle).expect (fun z => ind (z i)) := expect_sub _ _ _
    rw [hs, expect_const, completeDesign_expect_ind hle i]
    field_simp
    linarith
  · have hsplit : (fun z : Assignment n => ∑ i, (S.y0 i / (n₀ : ℝ)) * (1 - ind (z i)))
        = fun z => (∑ i, S.y0 i / (n₀ : ℝ)) - ∑ i, (S.y0 i / (n₀ : ℝ)) * ind (z i) := by
      funext z
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, var_const_sub, completeDesign_var_linear hle hn fun i => S.y0 i / (n₀ : ℝ),
      sum_sq_dev_div S.y0 (n₀ : ℝ) hn, e1, e2]
    field_simp
  · intro z hz
    have hcard : (armIdx z false).card = n₀ := by
      rw [card_armIdx_false hle hz]; omega
    have hM : armMean S z false = (n₀ : ℝ)⁻¹ * ∑ i, S.y0 i * (1 - ind (z i)) :=
      armMean_false_eq S hsum hle hz (by omega)
    have hobs : ∑ i ∈ armIdx z false, (S.observed z i - armMean S z false) ^ 2
        = ∑ i ∈ armIdx z false, (S.y0 i - armMean S z false) ^ 2 :=
      Finset.sum_congr rfl fun i hi => by
        rw [observed_eq_y0 S (by simpa [armIdx] using hi)]
    have hsum1 : ∑ i ∈ armIdx z false, S.y0 i = ∑ i, S.y0 i * (1 - ind (z i)) :=
      sum_armIdx_false_eq_sum_ind z S.y0
    have hsum2 : ∑ i ∈ armIdx z false, S.y0 i ^ 2 = ∑ i, S.y0 i ^ 2 * (1 - ind (z i)) :=
      sum_armIdx_false_eq_sum_ind z fun i => S.y0 i ^ 2
    have hsumM : ∑ i, S.y0 i * (1 - ind (z i)) = (n₀ : ℝ) * armMean S z false := by
      rw [hM, ← mul_assoc, mul_inv_cancel₀ hn0ne, one_mul]
    have hgM : ∑ i, (S.y0 i / (n₀ : ℝ)) * (1 - ind (z i)) = armMean S z false := by
      have hr : ∑ i, (S.y0 i / (n₀ : ℝ)) * (1 - ind (z i))
          = (n₀ : ℝ)⁻¹ * ∑ i, S.y0 i * (1 - ind (z i)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hr, hM]
    rw [armVar, hobs, sum_sq_sub (armIdx z false) S.y0 (armMean S z false), hcard, hsum1,
      hsum2, hgM, hsumM]
    ring

/-- **The expectation of Neyman's variance estimator** (Ding Theorem 4.1(3)):
`E[V̂] = S²(1)/n₁ + S²(0)/n₀`. -/
theorem neymanVarEst_expectation (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    -- USER-INPUT: both arms have at least two units; Ding Theorem 4.1(3)
    (h1 : 2 ≤ n₁) (h0 : 2 ≤ n₀) :
    (completeDesign n n₁ (by omega)).expect (neymanVarEst S)
      = popVar S.y1 / (n₁ : ℝ) + popVar S.y0 / (n₀ : ℝ) := by
  have hle : n₁ ≤ n := by omega
  have hE1 : (completeDesign n n₁ hle).expect (fun z => armVar S z true) = popVar S.y1 :=
    armVar_true_unbiased S hsum h1 (by omega)
  have hE0 : (completeDesign n n₁ hle).expect (fun z => armVar S z false) = popVar S.y0 :=
    armVar_false_unbiased S hsum (by omega) h0
  -- the arm sizes are constant on the support, so `V̂` is a fixed linear combination there
  have hcongr : (completeDesign n n₁ hle).expect (neymanVarEst S)
      = (completeDesign n n₁ hle).expect
          (fun z => (n₁ : ℝ)⁻¹ * armVar S z true + (n₀ : ℝ)⁻¹ * armVar S z false) := by
    refine expect_congr _ fun z hz => ?_
    rw [neymanVarEst, card_armIdx_true hle hz, card_armIdx_false hle hz,
      show n - n₁ = n₀ from by omega]
    ring
  have hsplit : (completeDesign n n₁ hle).expect
        (fun z => (n₁ : ℝ)⁻¹ * armVar S z true + (n₀ : ℝ)⁻¹ * armVar S z false)
      = (completeDesign n n₁ hle).expect (fun z => (n₁ : ℝ)⁻¹ * armVar S z true)
        + (completeDesign n n₁ hle).expect (fun z => (n₀ : ℝ)⁻¹ * armVar S z false) :=
    expect_add _ _ _
  have hc1 : (completeDesign n n₁ hle).expect (fun z => (n₁ : ℝ)⁻¹ * armVar S z true)
      = (n₁ : ℝ)⁻¹ * (completeDesign n n₁ hle).expect (fun z => armVar S z true) :=
    expect_const_mul _ _ _
  have hc0 : (completeDesign n n₁ hle).expect (fun z => (n₀ : ℝ)⁻¹ * armVar S z false)
      = (n₀ : ℝ)⁻¹ * (completeDesign n n₁ hle).expect (fun z => armVar S z false) :=
    expect_const_mul _ _ _
  rw [hcongr, hsplit, hc1, hc0, hE1, hE0]
  ring

/-- **The exact bias of Neyman's variance estimator** (Ding Theorem 4.1(3)): the estimator
exceeds the true randomization variance by exactly `S²(τ)/n`. -/
theorem neymanVarEst_bias (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    -- USER-INPUT: both arms have at least two units; Ding Theorem 4.1(3)
    (h1 : 2 ≤ n₁) (h0 : 2 ≤ n₀)
    -- LEAN-ONLY: at least two units, else the divisor `n - 1` in `popVar` vanishes
    (hn : 2 ≤ n) :
    (completeDesign n n₁ (by omega)).expect (neymanVarEst S)
        - (completeDesign n n₁ (by omega)).var (diffInMeans S)
      = popVar S.unitEffect / (n : ℝ) := by
  rw [neymanVarEst_expectation S hsum h1 h0,
    differenceInMeans_variance S hsum (by omega) (by omega) hn]
  ring

/-- **Conservativeness** (Ding Theorem 4.1(3)): Neyman's variance estimator is unbiased
*upward* — its expectation never underestimates the true randomization variance. Hence
the associated confidence intervals are conservative. -/
theorem neymanVarEst_conservative (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    (h1 : 2 ≤ n₁) (h0 : 2 ≤ n₀) (hn : 2 ≤ n) :
    (completeDesign n n₁ (by omega)).var (diffInMeans S)
      ≤ (completeDesign n n₁ (by omega)).expect (neymanVarEst S) := by
  have hb := neymanVarEst_bias S hsum h1 h0 hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : 0 ≤ popVar S.unitEffect / (n : ℝ) :=
    div_nonneg (popVar_nonneg S.unitEffect hn) (by linarith)
  linarith

/-- **Exactness under a constant effect** (Ding Theorem 4.1(3)): the bias `S²(τ)/n`
vanishes exactly when the individual effects are constant, and then `V̂` is unbiased. -/
theorem neymanVarEst_unbiased_of_constantEffect (S : ScienceTable n) {τ : ℝ}
    -- USER-INPUT: the additive constant-effect model; Ding Theorem 4.1(3)
    (hconst : S.ConstantEffect τ) (hsum : n₁ + n₀ = n)
    (h1 : 2 ≤ n₁) (h0 : 2 ≤ n₀) (hn : 2 ≤ n) :
    (completeDesign n n₁ (by omega)).expect (neymanVarEst S)
      = (completeDesign n n₁ (by omega)).var (diffInMeans S) := by
  have hb := neymanVarEst_bias S hsum h1 h0 hn
  have hc : ∀ i, S.unitEffect i = τ := hconst
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hpm : popMean S.unitEffect = τ := by
    simp only [popMean, hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hnne, one_mul]
  have hzero : popVar S.unitEffect = 0 := by
    simp [popVar, hpm, hc]
  rw [hzero] at hb
  simp only [zero_div] at hb
  linarith

end StatLean.CausalInference
