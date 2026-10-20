module
public import StatLean.RobustStatistics.LocationScale.Mean
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# The empirical-mean baseline — Chebyshev deviation under two moments

The starting point of modern (sub-Gaussian) mean estimation: under nothing but a finite
second moment, the deviation of the empirical mean is governed by Chebyshev's inequality
(`LM (2.3)`), and its `1/√δ` dependence on the confidence level — exponentially worse
than the `√log(1/δ)` a Gaussian sample would give (`LM (2.2)`) — is what every estimator
in this directory is built to beat.

* `sampleMean_variance` — `Var(μ̄ₙ) = σ²/n` for i.i.d. data with variance `σ²`.
* `sampleMean_chebyshev_deviation` — `P(|μ̄ₙ − μ| ≥ σ√(1/(nδ))) ≤ δ` (`LM (2.3)`).

**Reference.** G. Lugosi and S. Mendelson, *Mean estimation and regression under
heavy-tailed distributions — a survey*, Found. Comput. Math. (2019); arXiv:1906.04280v1.
(`LM`.) §2, displays (2.1)–(2.3). The estimator is Round-1's `sampleMean`; Chebyshev is
Mathlib's `ProbabilityTheory.meas_ge_le_variance_div_sq`.

**Bibliographic comments.** That Chebyshev's `1/√(nδ)` is essentially *sharp* for the
empirical mean — so that sub-Gaussian confidence under heavy tails requires a different
estimator — is Proposition 6.2 of O. Catoni, "Challenging the empirical mean and empirical
variance: a deviation study," *Ann. Inst. Henri Poincaré Probab. Stat.* **48** (2012),
1148–1185; the sub-Gaussian-estimator framework the comparison lives in is Devroye,
Lerasle, Lugosi and Oliveira, "Sub-Gaussian mean estimators," *Ann. Statist.* **44**
(2016), 2695–2725.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace StatLean.RobustStatistics

variable {Ξ : Type*} [MeasurableSpace Ξ] {μprob : Measure Ξ} [IsProbabilityMeasure μprob]
  {P : Measure ℝ} [IsProbabilityMeasure P]

/-! ### Moment transfer along the common law

The three private lemmas below move the hypotheses on `P` (square-integrability, mean,
variance) onto each coordinate `X i`, which is where the variance calculus happens. -/

omit [IsProbabilityMeasure μprob] [IsProbabilityMeasure P] in
/-- Square-integrability transfers from the law `P` to any random variable with law `P`. -/
private lemma memLp_two_of_law {f : Ξ → ℝ} (hf : Measurable f)
    (hlaw : μprob.map f = P) (hL2 : MemLp id 2 P) : MemLp f 2 μprob := by
  have h : MemLp id 2 (μprob.map f) := by rw [hlaw]; exact hL2
  simpa [Function.comp_def] using h.comp_of_map hf.aemeasurable

omit [IsProbabilityMeasure μprob] [IsProbabilityMeasure P] in
/-- The mean transfers from the law `P` to any random variable with law `P`. -/
private lemma integral_of_law {f : Ξ → ℝ} {μ₀ : ℝ} (hf : Measurable f)
    (hlaw : μprob.map f = P) (hmean : ∫ x, x ∂P = μ₀) : ∫ ξ, f ξ ∂μprob = μ₀ := by
  have h : ∫ y : ℝ, y ∂(μprob.map f) = ∫ ξ, f ξ ∂μprob :=
    integral_map hf.aemeasurable aestronglyMeasurable_id
  rw [hlaw, hmean] at h
  exact h.symm

omit [IsProbabilityMeasure μprob] [IsProbabilityMeasure P] in
/-- The variance transfers from the law `P` to any random variable with law `P`. -/
private lemma variance_of_law {f : Ξ → ℝ} {μ₀ σ2 : ℝ} (hf : Measurable f)
    (hlaw : μprob.map f = P) (hmean : ∫ x, x ∂P = μ₀)
    (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2) : Var[f; μprob] = σ2 := by
  have h1 : Var[id; μprob.map f] = Var[f; μprob] := variance_id_map hf.aemeasurable
  rw [hlaw] at h1
  rw [← h1, variance_eq_integral aemeasurable_id]
  simp only [id_eq]
  rw [hmean]
  exact hvar

/-- **Variance of the empirical mean** (`LM §2`, the display `E(μ̄ₙ − μ)² = σ²/n`):
for i.i.d. square-integrable data the empirical mean has variance `σ²/n`. -/
theorem sampleMean_variance {n : ℕ} (hn : n ≠ 0) {X : Fin n → Ξ → ℝ} {μ₀ σ2 : ℝ}
    -- LEAN-ONLY: measurability of each coordinate; regularity implicit in LM §2
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: the observations are jointly independent; LM §2 ("i.i.d.")
    (hX_indep : iIndepFun X μprob)
    -- USER-INPUT: common law P; LM §2 ("identically distributed draws from X")
    (hX_law : ∀ i, μprob.map (X i) = P)
    -- USER-INPUT: P is square-integrable; LM (2.3) context ("if σ exists")
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: mean and variance of P; LM §2
    (hmean : ∫ x, x ∂P = μ₀) (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2) :
    ∫ ξ, (sampleMean (fun i => X i ξ) - μ₀) ^ 2 ∂μprob = σ2 / n := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnR' : (n : ℝ) ≠ 0 := ne_of_gt hnR
  -- the coordinatewise moments
  have hML : ∀ i, MemLp (X i) 2 μprob := fun i =>
    memLp_two_of_law (hX_meas i) (hX_law i) hL2
  have hint : ∀ i, Integrable (X i) μprob := fun i => (hML i).integrable (by norm_num)
  have hEX : ∀ i, ∫ ξ, X i ξ ∂μprob = μ₀ := fun i =>
    integral_of_law (hX_meas i) (hX_law i) hmean
  have hVX : ∀ i, Var[X i; μprob] = σ2 := fun i =>
    variance_of_law (hX_meas i) (hX_law i) hmean hvar
  -- the empirical mean is measurable, has mean `μ₀` and variance `σ²/n`
  have hMmeas : Measurable fun ξ => sampleMean (fun i => X i ξ) := by
    simp only [sampleMean]
    exact (Finset.measurable_sum _ fun i _ => hX_meas i).div_const _
  have hMmean : ∫ ξ, sampleMean (fun i => X i ξ) ∂μprob = μ₀ := by
    simp only [sampleMean]
    rw [integral_div, integral_finset_sum _ fun i _ => hint i]
    simp only [hEX, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hVM : Var[fun ξ => sampleMean (fun i => X i ξ); μprob] = σ2 / n := by
    have hrw : (fun ξ => sampleMean (fun i => X i ξ))
        = fun ξ => (n : ℝ)⁻¹ * ∑ i, X i ξ := by
      funext ξ; simp [sampleMean, div_eq_inv_mul]
    have hsum : (fun ξ => ∑ i, X i ξ) = ∑ i : Fin n, X i := by
      funext ξ; simp
    rw [hrw, variance_const_mul, hsum,
      IndepFun.variance_sum (fun i _ => hML i) fun i _ j _ hij => hX_indep.indepFun hij]
    simp only [hVX, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- and `E(μ̄ − μ₀)²` is exactly that variance
  have hV : ∫ ξ, (sampleMean (fun i => X i ξ) - μ₀) ^ 2 ∂μprob
      = Var[fun ξ => sampleMean (fun i => X i ξ); μprob] := by
    rw [variance_eq_integral hMmeas.aemeasurable, hMmean]
  rw [hV, hVM]

/-- **Chebyshev's deviation bound for the empirical mean** (`LM (2.3)`): with probability
at least `1 − δ`, `|μ̄ₙ − μ| ≤ σ√(1/(nδ))`. The `1/√δ` confidence dependence is
essentially unimprovable for the empirical mean (`LM §2`, after (2.3), citing Catoni
(2012, Ann. IHP) Proposition 6.2) — the estimators of this directory replace it with
`√log(1/δ)`. -/
theorem sampleMean_chebyshev_deviation {n : ℕ} (hn : n ≠ 0) {X : Fin n → Ξ → ℝ}
    {μ₀ σ2 δ : ℝ}
    -- LEAN-ONLY: measurability of each coordinate; regularity implicit in LM §2
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: the observations are jointly independent; LM §2
    (hX_indep : iIndepFun X μprob)
    -- USER-INPUT: common law P; LM §2
    (hX_law : ∀ i, μprob.map (X i) = P)
    -- USER-INPUT: P is square-integrable; LM (2.3) context
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: mean and variance of P; LM §2
    (hmean : ∫ x, x ∂P = μ₀) (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2)
    -- USER-INPUT: confidence level; LM (2.1)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    -- USER-INPUT: nondegenerate variance (the bound is trivial at σ = 0); LM (2.3)
    (hσ : 0 < σ2) :
    μprob.real {ξ | Real.sqrt σ2 * Real.sqrt (1 / (n * δ))
      ≤ |sampleMean (fun i => X i ξ) - μ₀|} ≤ δ := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnR' : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hML : ∀ i, MemLp (X i) 2 μprob := fun i =>
    memLp_two_of_law (hX_meas i) (hX_law i) hL2
  have hint : ∀ i, Integrable (X i) μprob := fun i => (hML i).integrable (by norm_num)
  have hEX : ∀ i, ∫ ξ, X i ξ ∂μprob = μ₀ := fun i =>
    integral_of_law (hX_meas i) (hX_law i) hmean
  have hMmeas : Measurable fun ξ => sampleMean (fun i => X i ξ) := by
    simp only [sampleMean]
    exact (Finset.measurable_sum _ fun i _ => hX_meas i).div_const _
  have hMmean : ∫ ξ, sampleMean (fun i => X i ξ) ∂μprob = μ₀ := by
    simp only [sampleMean]
    rw [integral_div, integral_finset_sum _ fun i _ => hint i]
    simp only [hEX, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hM2 : MemLp (fun ξ => sampleMean (fun i => X i ξ)) 2 μprob := by
    have hsum : MemLp (fun ξ => ∑ i, X i ξ) 2 μprob :=
      memLp_finset_sum _ fun i _ => hML i
    simpa [sampleMean, div_eq_inv_mul] using hsum.const_mul ((n : ℝ)⁻¹)
  -- the variance of the empirical mean, from the previous theorem
  have hVM : Var[fun ξ => sampleMean (fun i => X i ξ); μprob] = σ2 / n := by
    rw [variance_eq_integral hMmeas.aemeasurable, hMmean]
    exact sampleMean_variance hn hX_meas hX_indep hX_law hL2 hmean hvar
  -- Chebyshev at the threshold `c = σ√(1/(nδ))`, whose square is `σ²/(nδ)`
  set c : ℝ := Real.sqrt σ2 * Real.sqrt (1 / (n * δ)) with hcdef
  have hc : 0 < c :=
    mul_pos (Real.sqrt_pos.mpr hσ) (Real.sqrt_pos.mpr (by positivity))
  have hc2 : c ^ 2 = σ2 * (1 / (n * δ)) := by
    rw [hcdef, mul_pow, Real.sq_sqrt hσ.le, Real.sq_sqrt (by positivity)]
  have hcheb := meas_ge_le_variance_div_sq (μ := μprob) hM2 hc
  rw [hMmean, hVM, hc2] at hcheb
  have hval : σ2 / (n : ℝ) / (σ2 * (1 / (n * δ))) = δ := by
    field_simp
  rw [hval] at hcheb
  exact ENNReal.toReal_le_of_le_ofReal hδ.le hcheb

end StatLean.RobustStatistics
