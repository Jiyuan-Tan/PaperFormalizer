module
public import StatLean.HypothesisTesting.Randomization.ExactLevel
public import StatLean.HypothesisTesting.ForMathlib.PermutationMarginals
public import StatLean.HypothesisTesting.Randomization.TwoSamplePermutation
public import StatLean.HypothesisTesting.Randomization.SlutskyRandomization
public import StatLean.AsymptoticStatistics.ForMathlib.Slutsky

@[expose] public section

/-!
# The studentized two-sample permutation test

The unstudentized two-sample permutation test compares a statistic whose permutation
variance $\lambda\sigma^2(P_Y) + \sigma^2(P_Z)$ differs from its true sampling variance
$\sigma^2(P_Y) + \lambda\sigma^2(P_Z)$ whenever the variances differ and the sample sizes
are unbalanced, so its asymptotic rejection probability need not equal $\alpha$ for testing
equality of *means*. Studentizing repairs this. Put
$$ \tilde T_{m,n} = \frac{T_{m,n}}{D_{m,n}}, \qquad
   D_{m,n}^2 = S_Y^2 + \frac{m}{n} S_Z^2 , $$
with $S_Y^2 = m^{-1}\sum_i (Y_i - \bar Y_m)^2$ and
$S_Z^2 = n^{-1}\sum_j (Z_j - \bar Z_n)^2$. Then

* the randomization distribution of $\tilde T_{m,n}$ converges in probability to the
  standard normal c.d.f., $\hat R^{\tilde T}_{m,n}(t) \xrightarrow{P} \Phi(t)$;
* the unconditional law also converges, $\tilde T_{m,n} \xrightarrow{d} N(0,1)$;

so the two match and the permutation test based on $\tilde T_{m,n}$ is asymptotically
level $\alpha$ — pointwise consistent in level — **even when the two populations have
different variances and the sample sizes are unbalanced**. When the populations are
identical the randomization hypothesis holds and the test is additionally *exact* at every
finite sample size, so studentization costs nothing.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 17 (Permutation and
Randomization Tests), §17.3 (Two-Sample Permutation Tests), Theorem 17.3.3 (asymptotic
validity of the studentized two-sample permutation test). (`TSH4 §17.3 Thm 17.3.3`.)

**Proof formalization notes.**
* *The exact studentization.* The scale is the one displayed above, $D^2 = S_Y^2 +
  (m/n)S_Z^2$, with both sample variances normalized by the sample size (not by
  $m-1$, $n-1$); this is the divisor the statement is proved with, and it is what makes
  $\tilde T_{m,n}$ pivotal.
* *Relation to the two-sample $t$-statistic.* Dividing numerator and denominator by
  $\sqrt m$ turns $\tilde T_{m,n}$ into
  $(\bar Y_m - \bar Z_n)/\sqrt{S_Y^2/m + S_Z^2/n}$, i.e. the two-sample $t$-statistic with
  **unpooled (Welch) standardization**; `studentizedTwoSample_eq_welch` records this
  algebraic identity. So the level statement below applies verbatim to that statistic
  without any equal-variance assumption. This is a different claim from the classical
  remark that the *pooled* two-sample $t$-test is asymptotically equivalent to the
  unstudentized permutation test — that comparison does require equal variances (or
  $\lambda = 1$), and is not asserted here.
* *Route.* Combining the two-sample permutation limit for the numerator with the Slutsky
  transfer for randomization distributions reduces the claim to showing that the
  studentizing scale, evaluated at a random permutation of the pooled data, converges in
  probability to the permutation scale $\tau$. That is a statement about the first two
  moments of a random sample drawn without replacement from the pooled data, and it is why
  the scale is *not* assumed group-invariant anywhere: it is not, and the Slutsky transfer
  is stated exactly to accommodate that.
* *Degenerate corners.* `twoSampleScale` can vanish (constant data), in which case
  `studentizedTwoSample` returns the junk value `x / 0 = 0`; the statistic is total. Under
  the standing hypotheses (nonzero population variances, sample sizes tending to infinity)
  the scale is eventually positive with probability tending to one, so the corner is
  asymptotically negligible rather than excluded by fiat.
* *No equal-variance hypothesis appears in any statement below* — that absence is the
  content of the theorem.

**Bibliographic comments.** That studentization restores asymptotic validity of the
two-sample permutation test under unequal variances is due to A. Janssen ("Studentized
permutation tests for non-i.i.d. hypotheses and the generalized Behrens–Fisher problem,"
*Statist. Probab. Lett.* **36** (1997), 9–21); the general principle — construct test
statistics whose limiting distribution is free of unknown parameters — was developed by
E. Chung and J. P. Romano ("Exact and asymptotically robust permutation tests," *Ann.
Statist.* **41** (2013), 484–507). The failure it repairs was identified by J. P. Romano
("On the behavior of randomization tests without a group invariance assumption," *J. Amer.
Statist. Assoc.* **85** (1990), 686–692; see also "Bootstrap and randomization tests of
some nonparametric hypotheses," *Ann. Statist.* **17** (1989), 141–159). The underlying
permutation limit theory is W. Hoeffding ("The large-sample power of tests based on
permutations of observations," *Ann. Math. Statist.* **23** (1952), 169–192), and the
exact finite-sample theory R. A. Fisher (*The Design of Experiments*, Oliver & Boyd,
Edinburgh, 1935), E. J. G. Pitman ("Significance tests which may be applied to samples
from any populations," *J. R. Statist. Soc. Suppl.* **4** (1937), 119–130) and
E. L. Lehmann and C. Stein ("On the theory of some non-parametric hypotheses," *Ann. Math.
Statist.* **20** (1949), 28–45); sampling the group rather than enumerating it is
M. Dwass ("Modified randomization tests for nonparametric hypotheses," *Ann. Math.
Statist.* **28** (1957), 181–187).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)
open StatLean.MultipleTesting (orderStat)

/-! ### The studentized statistic -/

/-- Sample mean of the first block (the `Y` sample) of the pooled data. -/
noncomputable def twoSampleMeanY (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i : Fin m, x (Fin.castAdd n i)

/-- Sample mean of the second block (the `Z` sample) of the pooled data. -/
noncomputable def twoSampleMeanZ (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j : Fin n, x (Fin.natAdd m j)

/-- The difference-of-means statistic in terms of the two block means. -/
lemma twoSampleMeanDiff_eq (m n : ℕ) (x : Fin (m + n) → ℝ) :
    twoSampleMeanDiff m n x =
      Real.sqrt (m : ℝ) * (twoSampleMeanY m n x - twoSampleMeanZ m n x) := rfl

/-- Sample variance of the `Y` block, normalized by `m`. -/
noncomputable def twoSampleVarY (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i : Fin m, (x (Fin.castAdd n i) - twoSampleMeanY m n x) ^ 2

/-- Sample variance of the `Z` block, normalized by `n`. -/
noncomputable def twoSampleVarZ (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j : Fin n, (x (Fin.natAdd m j) - twoSampleMeanZ m n x) ^ 2

/-- The **studentizing scale** `D_{m,n} = √(S²_Y + (m/n) S²_Z)`. -/
noncomputable def twoSampleScale (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  Real.sqrt (twoSampleVarY m n x + (m : ℝ) / n * twoSampleVarZ m n x)

/-- The **studentized two-sample statistic** `T̃_{m,n} = T_{m,n} / D_{m,n}`. Total: a
vanishing scale gives the junk value `0`. -/
noncomputable def studentizedTwoSample (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  twoSampleMeanDiff m n x / twoSampleScale m n x

/-- **The studentized permutation statistic is the unpooled (Welch) two-sample
`t`-statistic.** Dividing through by `√m`,
$$ \tilde T_{m,n} = \frac{\bar Y_m - \bar Z_n}{\sqrt{S_Y^2/m + S_Z^2/n}} , $$
an algebraic identity requiring no distributional assumption. Consequently every
asymptotic-level statement below is a statement about that `t`-statistic as well — with no
equal-variance assumption anywhere. -/
theorem studentizedTwoSample_eq_welch {m n : ℕ}
    -- USER-INPUT: both samples are nonempty, so the sample means are genuine averages
    (hm : 0 < m) (hn : 0 < n) (x : Fin (m + n) → ℝ) :
    studentizedTwoSample m n x =
      (twoSampleMeanY m n x - twoSampleMeanZ m n x) /
        Real.sqrt (twoSampleVarY m n x / m + twoSampleVarZ m n x / n) := by
  rw [studentizedTwoSample, twoSampleScale, twoSampleMeanDiff_eq]
  set a := twoSampleVarY m n x with ha
  set b := twoSampleVarZ m n x with hb
  set D := twoSampleMeanY m n x - twoSampleMeanZ m n x with hD
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkey : Real.sqrt (a + (m : ℝ) / n * b) =
      Real.sqrt m * Real.sqrt (a / m + b / n) := by
    rw [← Real.sqrt_mul hmR.le]
    congr 1
    field_simp
  rw [hkey, mul_div_mul_left _ _ (Real.sqrt_ne_zero'.2 hmR)]

/-! ### Shared bricks, imported from `Randomization/TwoSamplePermutation`

The triangular-array calculus for convergence in probability, the two block laws of large
numbers for the pooled law, the deterministic block weights and the pooled empirical average
are shared with `Randomization/TwoSamplePermutation` (which needs them for the
pooled-population hypotheses of the combinatorial central limit theorem) and now live there,
below this file in the import graph. -/


/-! ### Consistency of the studentizing scale -/

/-- The `Y`-block sample variance as (second moment) − (first moment)², the form in which the
law of large numbers reaches it. -/
private lemma twoSampleVarY_eq {m n : ℕ} (hm : 0 < m) (x : Fin (m + n) → ℝ) :
    twoSampleVarY m n x
      = (m : ℝ)⁻¹ * (∑ i : Fin m, (x (Fin.castAdd n i)) ^ 2)
        + -(twoSampleMeanY m n x ^ 2) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsum : ∑ i : Fin m, x (Fin.castAdd n i) = (m : ℝ) * twoSampleMeanY m n x := by
    rw [twoSampleMeanY, ← mul_assoc, mul_inv_cancel₀ hmR.ne', one_mul]
  have hexp : ∀ i : Fin m, (x (Fin.castAdd n i) - twoSampleMeanY m n x) ^ 2
      = (x (Fin.castAdd n i)) ^ 2
        - 2 * twoSampleMeanY m n x * x (Fin.castAdd n i)
        + twoSampleMeanY m n x ^ 2 := fun i => by ring
  rw [twoSampleVarY]
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum]
  field_simp
  ring

/-- The `Z`-block twin of `twoSampleVarY_eq`. -/
private lemma twoSampleVarZ_eq {m n : ℕ} (hn : 0 < n) (x : Fin (m + n) → ℝ) :
    twoSampleVarZ m n x
      = (n : ℝ)⁻¹ * (∑ j : Fin n, (x (Fin.natAdd m j)) ^ 2)
        + -(twoSampleMeanZ m n x ^ 2) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsum : ∑ j : Fin n, x (Fin.natAdd m j) = (n : ℝ) * twoSampleMeanZ m n x := by
    rw [twoSampleMeanZ, ← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul]
  have hexp : ∀ j : Fin n, (x (Fin.natAdd m j) - twoSampleMeanZ m n x) ^ 2
      = (x (Fin.natAdd m j)) ^ 2
        - 2 * twoSampleMeanZ m n x * x (Fin.natAdd m j)
        + twoSampleMeanZ m n x ^ 2 := fun j => by ring
  rw [twoSampleVarZ]
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum]
  field_simp
  ring

/-- **The studentizing scale is consistent for `s`.** Both sample variances converge in
probability to the corresponding population variances, and the sample-size ratio converges by
hypothesis; the scale is a continuous function of the three. -/
private lemma tendstoInProb_twoSampleScale (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ μ s : ℝ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam))
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    (hs : s ^ 2 = varY + lam * varZ) (hsnn : 0 ≤ s) :
    ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |twoSampleScale (m k) (n k) x - s|}) atTop (𝓝 0) := by
  classical
  have hidY : Integrable (fun t : ℝ => t) PY := by simpa using! hYL2.integrable (by norm_num)
  have hidZ : Integrable (fun t : ℝ => t) PZ := by simpa using! hZL2.integrable (by norm_num)
  have hsqY : Integrable (fun t : ℝ => t ^ 2) PY := by simpa using hYL2.integrable_sq
  have hsqZ : Integrable (fun t : ℝ => t ^ 2) PZ := by simpa using hZL2.integrable_sq
  -- The four block averages.
  have hMY : ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |twoSampleMeanY (m k) (n k) x - μ|}) atTop (𝓝 0) := by
    intro ε hε
    have h := tendsto_lln_blockY PY PZ m n hm (fun t : ℝ => t) measurable_id hidY hε
    rw [hmeanY] at h
    exact h
  have hMZ : ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |twoSampleMeanZ (m k) (n k) x - μ|}) atTop (𝓝 0) := by
    intro ε hε
    have h := tendsto_lln_blockZ PY PZ m n hn (fun t : ℝ => t) measurable_id hidZ hε
    rw [hmeanZ] at h
    exact h
  have hQY := fun ε hε => tendsto_lln_blockY PY PZ m n hm (fun t : ℝ => t ^ 2)
    (by fun_prop) hsqY (ε := ε) hε
  have hQZ := fun ε hε => tendsto_lln_blockZ PY PZ m n hn (fun t : ℝ => t ^ 2)
    (by fun_prop) hsqZ (ε := ε) hε
  -- The two sample variances.
  have hnegY := tendstoInProb_comp
    (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
    (φ := fun y : ℝ => -(y ^ 2)) (by fun_prop) hMY
  have hnegZ := tendstoInProb_comp
    (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
    (φ := fun y : ℝ => -(y ^ 2)) (by fun_prop) hMZ
  have haddY := tendstoInProb_add (P := fun k => twoSampleLaw (m k) (n k) PY PZ) hQY hnegY
  have haddZ := tendstoInProb_add (P := fun k => twoSampleLaw (m k) (n k) PY PZ) hQZ hnegZ
  have hvarYhat : ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |twoSampleVarY (m k) (n k) x - varY|}) atTop (𝓝 0) := by
    intro ε hε
    refine (haddY ε hε).congr' ?_
    filter_upwards [hm.eventually_gt_atTop 0] with k hk
    rw [var_eq_second_sub_sq hYL2 hmeanY hvarY]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, twoSampleVarY_eq hk x]
  have hvarZhat : ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |twoSampleVarZ (m k) (n k) x - varZ|}) atTop (𝓝 0) := by
    intro ε hε
    refine (haddZ ε hε).congr' ?_
    filter_upwards [hn.eventually_gt_atTop 0] with k hk
    rw [var_eq_second_sub_sq hZL2 hmeanZ hvarZ]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, twoSampleVarZ_eq hk x]
  -- Combine into the squared scale, then take the square root.
  have hratioZ := tendstoInProb_const_mul
    (P := fun k => twoSampleLaw (m k) (n k) PY PZ) hratio hvarZhat
  have hsqScale := tendstoInProb_add
    (P := fun k => twoSampleLaw (m k) (n k) PY PZ) hvarYhat hratioZ
  have hsqrt := tendstoInProb_comp
    (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
    (φ := Real.sqrt) (Real.continuous_sqrt.continuousAt) hsqScale
  intro ε hε
  have hlim : Real.sqrt (varY + lam * varZ) = s := by
    rw [← hs, Real.sqrt_sq hsnn]
  refine (hsqrt ε hε).congr fun k => ?_
  simp only [hlim, twoSampleScale]

/-! ### Group-averaged convergence in probability

`TendstoInProbRandomized` — the hypothesis the Slutsky transfer consumes — evaluates the
scaling at `g · x` with `g` uniform on the group, so it is a convex combination of the
per-`g` failure probabilities. The two closure properties needed below are therefore proved
exactly as their fixed-measure counterparts above, one group element at a time. -/

/-- **Continuous mapping for group-averaged convergence in probability.** -/
private lemma tendstoInProbRandomized_comp {𝓨 : ℕ → Type*} [∀ k, MeasurableSpace (𝓨 k)]
    (G : ℕ → Type*) [∀ k, Group (G k)] [∀ k, Fintype (G k)] [∀ k, MulAction (G k) (𝓨 k)]
    (P : ∀ k, Measure (𝓨 k)) [∀ k, IsProbabilityMeasure (P k)]
    {A : ∀ k, 𝓨 k → ℝ} {a : ℝ} {φ : ℝ → ℝ} (hφ : ContinuousAt φ a)
    (h : TendstoInProbRandomized G P A a) :
    TendstoInProbRandomized G P (fun k y => φ (A k y)) (φ a) := by
  intro ε hε
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.continuousAt_iff.mp hφ ε hε
  refine squeeze_zero (fun k => ?_) (fun k => ?_) (h ρ hρpos)
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun g _ => measureReal_nonneg)
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => ?_) (by positivity)
    refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_contra hcon
    push Not at hcon
    have hd : dist (A k (g • x)) a < ρ := by rwa [Real.dist_eq]
    have hlt := hρ hd
    rw [Real.dist_eq] at hlt
    linarith

/-- **The zero shift converges in probability at randomized data.** The studentized
statistic has no recentring, so this is the shift hypothesis of the Slutsky transfer. -/
private lemma tendstoInProbRandomized_zero {𝓨 : ℕ → Type*} [∀ k, MeasurableSpace (𝓨 k)]
    (G : ℕ → Type*) [∀ k, Group (G k)] [∀ k, Fintype (G k)] [∀ k, MulAction (G k) (𝓨 k)]
    (P : ∀ k, Measure (𝓨 k)) :
    TendstoInProbRandomized G P (fun _ _ => (0 : ℝ)) 0 := by
  intro ε hε
  have hfalse : ¬ (ε ≤ |(0 : ℝ) - 0|) := by rw [sub_zero, abs_zero]; exact not_le.2 hε
  simp only [hfalse, Set.setOf_false, measureReal_empty, Finset.sum_const_zero, mul_zero]
  exact tendsto_const_nhds

/-! ### Elementary bricks for the hypergeometric step -/

/-- Markov's inequality in `Measure.real` form. -/
private lemma measureReal_ge_le_integral {𝓨 : Type*} [MeasurableSpace 𝓨] (P : Measure 𝓨)
    [IsProbabilityMeasure P] {A : 𝓨 → ℝ} (hA : Measurable A) (hAnn : ∀ x, 0 ≤ A x)
    (hAint : Integrable A P) {ε : ℝ} (hε : 0 < ε) :
    P.real {x | ε ≤ A x} ≤ ε⁻¹ * ∫ x, A x ∂P := by
  have hset : MeasurableSet {x : 𝓨 | ε ≤ A x} := measurableSet_le measurable_const hA
  have hind : ∫ x, Set.indicator {x : 𝓨 | ε ≤ A x} (fun _ => ε) x ∂P
      = ε * P.real {x | ε ≤ A x} := by
    rw [integral_indicator_const _ hset, smul_eq_mul, mul_comm]
  have hle : ∫ x, Set.indicator {x : 𝓨 | ε ≤ A x} (fun _ => ε) x ∂P ≤ ∫ x, A x ∂P := by
    refine integral_mono ((integrable_const ε).indicator hset) hAint (fun x => ?_)
    by_cases hx : x ∈ {x : 𝓨 | ε ≤ A x}
    · rw [Set.indicator_of_mem hx]; exact hx
    · rw [Set.indicator_of_notMem hx]; exact hAnn x
  rw [hind] at hle
  rw [inv_mul_eq_div, le_div_iff₀ hε, mul_comm]
  linarith

/-- The empirical variance is at most the empirical second moment. -/
private lemma sum_sub_avg_sq_le {N : ℕ} (c : Fin N → ℝ) :
    ∑ l, (c l - (N : ℝ)⁻¹ * ∑ l', c l') ^ 2 ≤ ∑ l, c l ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set a : ℝ := (N : ℝ)⁻¹ * ∑ l', c l' with ha
  have hexp : ∀ l : Fin N, (c l - a) ^ 2 = c l ^ 2 - 2 * a * c l + a ^ 2 := fun l => by ring
  rw [Finset.sum_congr rfl fun l _ => hexp l]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum : ∑ l', c l' = (N : ℝ) * a := by
    rw [ha, ← mul_assoc, mul_inv_cancel₀ hNR.ne', one_mul]
  rw [hsum]
  nlinarith [sq_nonneg a, hNR]

/-! ### Coordinate marginals of the pooled law -/

private lemma isProbabilityMeasure_addCases' (m n : ℕ) (PY PZ : Measure ℝ)
    [IsProbabilityMeasure PY] [IsProbabilityMeasure PZ] (l : Fin (m + n)) :
    IsProbabilityMeasure
      (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) l) := by
  refine Fin.addCases (m := m) (n := n)
    (motive := fun l => IsProbabilityMeasure
      (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) l))
    (fun i => ?_) (fun j => ?_) l
  · simpa only [Fin.addCases_left] using (inferInstance : IsProbabilityMeasure PY)
  · simpa only [Fin.addCases_right] using (inferInstance : IsProbabilityMeasure PZ)

/-- The `i`-th `Y`-block coordinate of the pooled law is distributed as `P_Y`. -/
private lemma measurePreserving_evalY (m n : ℕ) (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (i : Fin m) :
    MeasurePreserving (fun x : Fin (m + n) → ℝ => x (Fin.castAdd n i))
      (twoSampleLaw m n PY PZ) PY := by
  haveI := isProbabilityMeasure_addCases' m n PY PZ
  have h := MeasureTheory.measurePreserving_eval
    (μ := Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ))
    (Fin.castAdd n i)
  rw [show (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ))
      (Fin.castAdd n i) = PY from by simp] at h
  exact h

/-- The `j`-th `Z`-block coordinate of the pooled law is distributed as `P_Z`. -/
private lemma measurePreserving_evalZ (m n : ℕ) (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (j : Fin n) :
    MeasurePreserving (fun x : Fin (m + n) → ℝ => x (Fin.natAdd m j))
      (twoSampleLaw m n PY PZ) PZ := by
  haveI := isProbabilityMeasure_addCases' m n PY PZ
  have h := MeasureTheory.measurePreserving_eval
    (μ := Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ))
    (Fin.natAdd m j)
  rw [show (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ))
      (Fin.natAdd m j) = PZ from by simp] at h
  exact h

/-- Integrability of a coordinatewise sum over the pooled law. -/
private lemma integrable_sum_coords (m n : ℕ) (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (g : ℝ → ℝ) (hgm : Measurable g)
    (hY : Integrable g PY) (hZ : Integrable g PZ) :
    Integrable (fun x : Fin (m + n) → ℝ => ∑ l, g (x l)) (twoSampleLaw m n PY PZ) := by
  have hsplit : (fun x : Fin (m + n) → ℝ => ∑ l, g (x l))
      = fun x : Fin (m + n) → ℝ => (∑ i : Fin m, g (x (Fin.castAdd n i)))
          + ∑ j : Fin n, g (x (Fin.natAdd m j)) := by
    funext x; exact Fin.sum_univ_add (f := fun l => g (x l))
  rw [hsplit]
  refine Integrable.add ?_ ?_
  · refine integrable_finset_sum _ fun i _ => ?_
    exact ((measurePreserving_evalY m n PY PZ i).integrable_comp
      hgm.aestronglyMeasurable).mpr hY
  · refine integrable_finset_sum _ fun j _ => ?_
    exact ((measurePreserving_evalZ m n PY PZ j).integrable_comp
      hgm.aestronglyMeasurable).mpr hZ

/-- The pooled expectation of a coordinatewise sum. -/
private lemma integral_sum_coords (m n : ℕ) (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (g : ℝ → ℝ) (hgm : Measurable g)
    (hY : Integrable g PY) (hZ : Integrable g PZ) :
    ∫ x, (∑ l, g (x l)) ∂(twoSampleLaw m n PY PZ)
      = (m : ℝ) * (∫ t, g t ∂PY) + (n : ℝ) * ∫ t, g t ∂PZ := by
  have hsplit : (fun x : Fin (m + n) → ℝ => ∑ l, g (x l))
      = fun x : Fin (m + n) → ℝ => (∑ i : Fin m, g (x (Fin.castAdd n i)))
          + ∑ j : Fin n, g (x (Fin.natAdd m j)) := by
    funext x; exact Fin.sum_univ_add (f := fun l => g (x l))
  have hintY : ∀ i : Fin m, Integrable
      (fun x : Fin (m + n) → ℝ => g (x (Fin.castAdd n i))) (twoSampleLaw m n PY PZ) :=
    fun i => ((measurePreserving_evalY m n PY PZ i).integrable_comp
      hgm.aestronglyMeasurable).mpr hY
  have hintZ : ∀ j : Fin n, Integrable
      (fun x : Fin (m + n) → ℝ => g (x (Fin.natAdd m j))) (twoSampleLaw m n PY PZ) :=
    fun j => ((measurePreserving_evalZ m n PY PZ j).integrable_comp
      hgm.aestronglyMeasurable).mpr hZ
  have hvalY : ∀ i : Fin m,
      ∫ x, g (x (Fin.castAdd n i)) ∂(twoSampleLaw m n PY PZ) = ∫ t, g t ∂PY := by
    intro i
    have hmap := (measurePreserving_evalY m n PY PZ i).map_eq
    conv_rhs => rw [← hmap]
    rw [integral_map (measurable_pi_apply _).aemeasurable
      (by rw [hmap]; exact hgm.aestronglyMeasurable)]
  have hvalZ : ∀ j : Fin n,
      ∫ x, g (x (Fin.natAdd m j)) ∂(twoSampleLaw m n PY PZ) = ∫ t, g t ∂PZ := by
    intro j
    have hmap := (measurePreserving_evalZ m n PY PZ j).map_eq
    conv_rhs => rw [← hmap]
    rw [integral_map (measurable_pi_apply _).aemeasurable
      (by rw [hmap]; exact hgm.aestronglyMeasurable)]
  rw [hsplit, integral_add (integrable_finset_sum _ fun i _ => hintY i)
    (integrable_finset_sum _ fun j _ => hintZ j),
    integral_finset_sum _ (fun i _ => hintY i), integral_finset_sum _ (fun j _ => hintZ j),
    Finset.sum_congr rfl (fun i _ => hvalY i), Finset.sum_congr rfl (fun j _ => hvalZ j),
    Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]


/-- **The randomized block average is close to the pooled average**, uniformly in the data:
Chebyshev over the group, then Fubini, then the crude second-moment bound. -/
private lemma perm_avg_block_sub_pooled_le (m n : ℕ) (PY PZ : Measure ℝ)
    [IsProbabilityMeasure PY] [IsProbabilityMeasure PZ]
    {p : ℕ} (hp : 0 < p) (hN : 2 ≤ m + n)
    (a : Fin p → Fin (m + n)) (ha : Function.Injective a)
    (f : ℝ → ℝ) (hfm : Measurable f)
    (hY : Integrable (fun t => f t ^ 2) PY) (hZ : Integrable (fun t => f t ^ 2) PZ)
    {ε : ℝ} (hε : 0 < ε) :
    (Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (m + n)), (twoSampleLaw m n PY PZ).real
          {x | ε ≤ |(p : ℝ)⁻¹ * (∑ i, f ((σ • x) (a i)))
                    - ((m + n : ℕ) : ℝ)⁻¹ * ∑ l, f (x l)|}
      ≤ ε⁻¹ ^ 2 * ((p : ℝ)⁻¹ * ((∫ t, f t ^ 2 ∂PY) + ∫ t, f t ^ 2 ∂PZ)) := by
  classical
  have hfsqm : Measurable (fun t : ℝ => f t ^ 2) := hfm.pow_const 2
  have hmeasA : ∀ σ : Equiv.Perm (Fin (m + n)), Measurable (fun x : Fin (m + n) → ℝ =>
      |(p : ℝ)⁻¹ * (∑ i, f ((σ • x) (a i))) - ((m + n : ℕ) : ℝ)⁻¹ * ∑ l, f (x l)|) := by
    intro σ
    have h1 : Measurable (fun x : Fin (m + n) → ℝ => ∑ i, f ((σ • x) (a i))) := by
      simp only [perm_smul_apply]
      exact Finset.measurable_sum _ fun i _ => hfm.comp (measurable_pi_apply _)
    have h2 : Measurable (fun x : Fin (m + n) → ℝ => ∑ l, f (x l)) :=
      Finset.measurable_sum _ fun l _ => hfm.comp (measurable_pi_apply _)
    exact ((h1.const_mul _).sub (h2.const_mul _)).abs
  rw [avg_measureReal_eq_integral_avg_indicator (twoSampleLaw m n PY PZ) _ hmeasA ε]
  -- the pointwise Chebyshev bound, with the empirical variance crudely majorized
  have hpt : ∀ x : Fin (m + n) → ℝ,
      (Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (m + n)),
        (if ε ≤ |(p : ℝ)⁻¹ * (∑ i, f ((σ • x) (a i)))
            - ((m + n : ℕ) : ℝ)⁻¹ * ∑ l, f (x l)| then (1 : ℝ) else 0)
      ≤ ε⁻¹ ^ 2 * ((p : ℝ)⁻¹ * (((m + n : ℕ) : ℝ)⁻¹ * ∑ l, f (x l) ^ 2)) := by
    intro x
    have h := perm_avg_indicator_blockAvg_inv_sub_mean_le hp hN a ha (fun l => f (x l)) hε
    simp only [perm_smul_apply]
    refine h.trans ?_
    have hvar := sum_sub_avg_sq_le (fun l => f (x l))
    gcongr
  -- integrate the bound
  have hset : ∀ σ : Equiv.Perm (Fin (m + n)), MeasurableSet {x : Fin (m + n) → ℝ |
      ε ≤ |(p : ℝ)⁻¹ * (∑ i, f ((σ • x) (a i))) - ((m + n : ℕ) : ℝ)⁻¹ * ∑ l, f (x l)|} :=
    fun σ => measurableSet_le measurable_const (hmeasA σ)
  have hintind : ∀ σ : Equiv.Perm (Fin (m + n)), Integrable (fun x : Fin (m + n) → ℝ =>
      if ε ≤ |(p : ℝ)⁻¹ * (∑ i, f ((σ • x) (a i))) - ((m + n : ℕ) : ℝ)⁻¹ * ∑ l, f (x l)|
        then (1 : ℝ) else 0) (twoSampleLaw m n PY PZ) := by
    intro σ
    have hrw : (fun x : Fin (m + n) → ℝ =>
        if ε ≤ |(p : ℝ)⁻¹ * (∑ i, f ((σ • x) (a i))) - ((m + n : ℕ) : ℝ)⁻¹ * ∑ l, f (x l)|
          then (1 : ℝ) else 0)
        = Set.indicator {x : Fin (m + n) → ℝ |
            ε ≤ |(p : ℝ)⁻¹ * (∑ i, f ((σ • x) (a i)))
              - ((m + n : ℕ) : ℝ)⁻¹ * ∑ l, f (x l)|} 1 := by
      funext x; simp [Set.indicator_apply]
    rw [hrw]
    exact (integrable_const (1 : ℝ)).indicator (hset σ)
  have hintL : Integrable (fun x : Fin (m + n) → ℝ =>
      (Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (m + n)),
        (if ε ≤ |(p : ℝ)⁻¹ * (∑ i, f ((σ • x) (a i)))
            - ((m + n : ℕ) : ℝ)⁻¹ * ∑ l, f (x l)| then (1 : ℝ) else 0))
      (twoSampleLaw m n PY PZ) :=
    (integrable_finset_sum _ fun σ _ => hintind σ).const_mul _
  have hS := integrable_sum_coords m n PY PZ (fun t => f t ^ 2) hfsqm hY hZ
  have hintR : Integrable (fun x : Fin (m + n) → ℝ =>
      ε⁻¹ ^ 2 * ((p : ℝ)⁻¹ * (((m + n : ℕ) : ℝ)⁻¹ * ∑ l, f (x l) ^ 2)))
      (twoSampleLaw m n PY PZ) := ((hS.const_mul _).const_mul _).const_mul _
  refine (integral_mono hintL hintR hpt).trans ?_
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    integral_sum_coords m n PY PZ (fun t => f t ^ 2) hfsqm hY hZ]
  have hQY : (0 : ℝ) ≤ ∫ t, f t ^ 2 ∂PY := integral_nonneg fun t => sq_nonneg _
  have hQZ : (0 : ℝ) ≤ ∫ t, f t ^ 2 ∂PZ := integral_nonneg fun t => sq_nonneg _
  have hNcast : ((m + n : ℕ) : ℝ) = (m : ℝ) + n := by push_cast; ring
  have hNpos : (0 : ℝ) < ((m + n : ℕ) : ℝ) := by
    rw [hNcast]
    have : (2 : ℝ) ≤ (m : ℝ) + n := by rw [← hNcast]; exact_mod_cast hN
    linarith
  have hkey : ((m + n : ℕ) : ℝ)⁻¹ * ((m : ℝ) * (∫ t, f t ^ 2 ∂PY)
      + (n : ℝ) * ∫ t, f t ^ 2 ∂PZ) ≤ (∫ t, f t ^ 2 ∂PY) + ∫ t, f t ^ 2 ∂PZ := by
    rw [inv_mul_le_iff₀ hNpos, hNcast]
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith
  gcongr




/-! ### From the pooled average to the randomized block average -/

/-- A union bound for a group average of probabilities, the second set being independent of
the group element. -/
private lemma avg_measureReal_le_add {𝓨 : Type*} [MeasurableSpace 𝓨] (P : Measure 𝓨)
    [IsProbabilityMeasure P] {G : Type*} [Fintype G] [Nonempty G]
    (S U : G → Set 𝓨) (V : Set 𝓨) (hsub : ∀ g, S g ⊆ U g ∪ V) :
    (Fintype.card G : ℝ)⁻¹ * ∑ g : G, P.real (S g)
      ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, P.real (U g) + P.real V := by
  have hcard : (0 : ℝ) < (Fintype.card G : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hle : ∀ g : G, P.real (S g) ≤ P.real (U g) + P.real V := fun g =>
    (measureReal_mono (hsub g) (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  have hstep : (Fintype.card G : ℝ)⁻¹ * ∑ g : G, P.real (S g)
      ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, (P.real (U g) + P.real V) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => hle g) (by positivity)
  refine hstep.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add,
    ← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]

/-- **The randomized block average converges, under a square-integrability hypothesis.**
For `f` with a finite second moment under both populations, the average of `f` over a block
of `p k` positions of a uniformly permuted pooled sample converges, in the group-averaged
in-probability sense, to the pooled mixture limit. -/
private lemma tendstoInProbRandomized_blockAvg_of_sq (PY PZ : Measure ℝ)
    [IsProbabilityMeasure PY] [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam : ℝ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    (p : ℕ → ℕ) (a : ∀ k, Fin (p k) → Fin (m k + n k)) (ha : ∀ k, Function.Injective (a k))
    (hp : Tendsto p atTop atTop)
    (f : ℝ → ℝ) (hfm : Measurable f) (hY : Integrable f PY) (hZ : Integrable f PZ)
    (hY2 : Integrable (fun t => f t ^ 2) PY) (hZ2 : Integrable (fun t => f t ^ 2) PZ) :
    ∀ ε > (0 : ℝ), Tendsto (fun k =>
        (Fintype.card (Equiv.Perm (Fin (m k + n k))) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin (m k + n k)), (twoSampleLaw (m k) (n k) PY PZ).real
            {x | ε ≤ |(p k : ℝ)⁻¹ * (∑ i, f ((σ • x) (a k i)))
              - (lam / (1 + lam) * (∫ t, f t ∂PY) + 1 / (1 + lam) * ∫ t, f t ∂PZ)|})
      atTop (𝓝 0) := by
  classical
  set L : ℝ := lam / (1 + lam) * (∫ t, f t ∂PY) + 1 / (1 + lam) * ∫ t, f t ∂PZ with hL
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  have hpool := tendstoInProb_pooledAvg PY PZ m n hm hn hratio hlam f hfm hY hZ (ε / 2) hε2
  -- the uniform Chebyshev bound, eventually in `k`
  have hbound : ∀ᶠ k in atTop,
      (Fintype.card (Equiv.Perm (Fin (m k + n k))) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin (m k + n k)), (twoSampleLaw (m k) (n k) PY PZ).real
            {x | ε ≤ |(p k : ℝ)⁻¹ * (∑ i, f ((σ • x) (a k i))) - L|}
        ≤ (ε / 2)⁻¹ ^ 2 * ((p k : ℝ)⁻¹ * ((∫ t, f t ^ 2 ∂PY) + ∫ t, f t ^ 2 ∂PZ))
          + (twoSampleLaw (m k) (n k) PY PZ).real
            {x : Fin (m k + n k) → ℝ | ε / 2 ≤ |((m k + n k : ℕ) : ℝ)⁻¹ * (∑ l, f (x l)) - L|} := by
    filter_upwards [hp.eventually_gt_atTop 0, hm.eventually_ge_atTop 2] with k hpk hmk
    have hNk : 2 ≤ m k + n k := le_trans hmk (Nat.le_add_right _ _)
    refine le_trans (avg_measureReal_le_add (twoSampleLaw (m k) (n k) PY PZ)
      (fun σ => {x | ε ≤ |(p k : ℝ)⁻¹ * (∑ i, f ((σ • x) (a k i))) - L|})
      (fun σ => {x | ε / 2 ≤ |(p k : ℝ)⁻¹ * (∑ i, f ((σ • x) (a k i)))
        - ((m k + n k : ℕ) : ℝ)⁻¹ * ∑ l, f (x l)|})
      {x : Fin (m k + n k) → ℝ | ε / 2 ≤ |((m k + n k : ℕ) : ℝ)⁻¹ * (∑ l, f (x l)) - L|}
      (fun σ x hx => ?_)) ?_
    · simp only [Set.mem_setOf_eq, Set.mem_union] at hx ⊢
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have htri := abs_add_le ((p k : ℝ)⁻¹ * (∑ i, f ((σ • x) (a k i)))
          - ((m k + n k : ℕ) : ℝ)⁻¹ * ∑ l, f (x l))
        (((m k + n k : ℕ) : ℝ)⁻¹ * (∑ l, f (x l)) - L)
      have heq : (p k : ℝ)⁻¹ * (∑ i, f ((σ • x) (a k i))) - L
          = ((p k : ℝ)⁻¹ * (∑ i, f ((σ • x) (a k i)))
              - ((m k + n k : ℕ) : ℝ)⁻¹ * ∑ l, f (x l))
            + (((m k + n k : ℕ) : ℝ)⁻¹ * (∑ l, f (x l)) - L) := by ring
      rw [heq] at hx
      linarith
    · exact add_le_add (perm_avg_block_sub_pooled_le (m k) (n k) PY PZ hpk hNk
        (a k) (ha k) f hfm hY2 hZ2 hε2) le_rfl
  -- both terms vanish
  have hinv : Tendsto (fun k => ((p k : ℝ))⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp hp).inv_tendsto_atTop
  have hfirst : Tendsto (fun k => (ε / 2)⁻¹ ^ 2 *
      ((p k : ℝ)⁻¹ * ((∫ t, f t ^ 2 ∂PY) + ∫ t, f t ^ 2 ∂PZ))) atTop (𝓝 0) := by
    have := (hinv.mul_const ((∫ t, f t ^ 2 ∂PY) + ∫ t, f t ^ 2 ∂PZ)).const_mul
      ((ε / 2)⁻¹ ^ 2)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun k => ?_) hbound ?_
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun σ _ => measureReal_nonneg)
  · rw [← hL] at hpool
    have hadd := hfirst.add hpool
    rwa [add_zero] at hadd


/-! ### Truncation: dropping the second-moment hypothesis

Applying the Chebyshev bound above to `f = (·)²` would cost a fourth pooled moment, which
`MemLp id 2` does not supply. The standard remedy for sampling without replacement is to
truncate: the truncated function is bounded, hence square integrable, and the discarded part
is controlled in `L¹` *uniformly in `k`*, because the group average of a permuted block
average of a nonnegative function is exactly the pooled average of that function
(`avg_perm_blockAvg_eq`), whose expectation is the convex combination of the two population
integrals. -/

/-- The truncation of `f` to the band `[-j, j]`. -/
private noncomputable def truncAt (j : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => max (-(j : ℝ)) (min (f t) (j : ℝ))

private lemma measurable_truncAt (j : ℕ) {f : ℝ → ℝ} (hfm : Measurable f) :
    Measurable (truncAt j f) :=
  measurable_const.max (hfm.min measurable_const)

private lemma abs_truncAt_le (j : ℕ) (f : ℝ → ℝ) (t : ℝ) : |truncAt j f t| ≤ (j : ℝ) := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

private lemma truncAt_eq_self {j : ℕ} {f : ℝ → ℝ} {t : ℝ} (h : |f t| ≤ (j : ℝ)) :
    truncAt j f t = f t := by
  rw [abs_le] at h
  rw [truncAt, min_eq_left h.2, max_eq_right h.1]

private lemma abs_sub_truncAt_le (j : ℕ) (f : ℝ → ℝ) (t : ℝ) :
    |f t - truncAt j f t| ≤ |f t| := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  rw [truncAt]
  rcases le_total (f t) (-(j : ℝ)) with h1 | h1
  · rw [min_eq_left (by linarith), max_eq_left h1,
      abs_of_nonpos (by linarith : f t ≤ 0),
      abs_of_nonpos (by linarith : f t - -(j : ℝ) ≤ 0)]
    linarith
  · rcases le_total (f t) (j : ℝ) with h2 | h2
    · rw [min_eq_left h2, max_eq_right h1, sub_self, abs_zero]
      exact abs_nonneg _
    · rw [min_eq_right h2, max_eq_right (by linarith),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ f t - (j : ℝ)),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ f t)]
      linarith

private lemma integrable_truncAt {Q : Measure ℝ} [IsProbabilityMeasure Q] (j : ℕ)
    {f : ℝ → ℝ} (hfm : Measurable f) : Integrable (truncAt j f) Q :=
  (integrable_const (j : ℝ)).mono' (measurable_truncAt j hfm).aestronglyMeasurable
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact abs_truncAt_le j f t)

private lemma integrable_truncAt_sq {Q : Measure ℝ} [IsProbabilityMeasure Q] (j : ℕ)
    {f : ℝ → ℝ} (hfm : Measurable f) : Integrable (fun t => truncAt j f t ^ 2) Q := by
  refine (integrable_const ((j : ℝ) ^ 2)).mono'
    ((measurable_truncAt j hfm).pow_const 2).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (truncAt j f t)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_truncAt_le j f t) 2

/-- **The truncation error vanishes in `L¹`.** -/
private lemma tendsto_integral_sub_truncAt {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (f : ℝ → ℝ) (hfm : Measurable f) (hQ : Integrable f Q) :
    Tendsto (fun j : ℕ => ∫ t, |f t - truncAt j f t| ∂Q) atTop (𝓝 0) := by
  have hzero : ∫ (_ : ℝ), (0 : ℝ) ∂Q = 0 := integral_zero _ _
  have h := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun (j : ℕ) (t : ℝ) => |f t - truncAt j f t|) (f := fun _ : ℝ => (0 : ℝ))
    (bound := fun t => |f t|)
    (fun j => ((hfm.sub (measurable_truncAt j hfm)).abs).aestronglyMeasurable)
    hQ.abs
    (fun j => ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_abs]; exact abs_sub_truncAt_le j f t)
    (ae_of_all _ fun t => ?_)
  · rwa [hzero] at h
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|f t|⌉₊] with j hj
    have hjle : |f t| ≤ (j : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hj)
    rw [truncAt_eq_self hjle, sub_self, abs_zero]

/-- **The truncated integral converges to the integral.** -/
private lemma tendsto_integral_truncAt {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (f : ℝ → ℝ) (hfm : Measurable f) (hQ : Integrable f Q) :
    Tendsto (fun j : ℕ => ∫ t, truncAt j f t ∂Q) atTop (𝓝 (∫ t, f t ∂Q)) := by
  rw [← sub_zero (∫ t, f t ∂Q), Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 (tendsto_integral_sub_truncAt f hfm hQ) δ hδ
  refine ⟨J, fun j hj => ?_⟩
  have hbound := hJ j hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun t => abs_nonneg _)] at hbound
  have hsub : (∫ t, f t ∂Q) - ∫ t, truncAt j f t ∂Q = ∫ t, (f t - truncAt j f t) ∂Q :=
    (integral_sub hQ (integrable_truncAt j hfm)).symm
  have habs : |(∫ t, truncAt j f t ∂Q) - ((∫ t, f t ∂Q) - 0)|
      = |∫ t, (f t - truncAt j f t) ∂Q| := by
    rw [sub_zero, abs_sub_comm, hsub]
  rw [Real.dist_eq, habs]
  refine lt_of_le_of_lt ?_ hbound
  simpa using
    (MeasureTheory.abs_integral_le_integral_abs (μ := Q) (f := fun t => f t - truncAt j f t))

/-! ### The exact group average of a permuted block average -/

/-- **The group average of a permuted block average is the pooled average.** -/
private lemma avg_perm_blockAvg_eq {N p : ℕ} (hp : 0 < p) (a : Fin p → Fin N)
    (c : Fin N → ℝ) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), (p : ℝ)⁻¹ * ∑ i, c (σ⁻¹ (a i))
      = (N : ℝ)⁻¹ * ∑ l, c l := by
  classical
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hstep : ∀ i : Fin p, (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), c (σ⁻¹ (a i)) = (N : ℝ)⁻¹ * ∑ l, c l := by
    intro i
    have hinv : ∑ σ : Equiv.Perm (Fin N), c (σ⁻¹ (a i))
        = ∑ σ : Equiv.Perm (Fin N), c (σ (a i)) :=
      sum_perm_inv (G := Equiv.Perm (Fin N)) (f := fun σ : Equiv.Perm (Fin N) => c (σ (a i)))
    rw [hinv]
    have h := avg_perm_apply (a i) c
    rw [Fintype.card_fin] at h
    exact h
  have hswap : ∑ σ : Equiv.Perm (Fin N), (p : ℝ)⁻¹ * ∑ i, c (σ⁻¹ (a i))
      = (p : ℝ)⁻¹ * ∑ i : Fin p, ∑ σ : Equiv.Perm (Fin N), c (σ⁻¹ (a i)) := by
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_comm
  rw [hswap, ← mul_assoc, mul_comm ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹) ((p : ℝ)⁻¹),
    mul_assoc, Finset.mul_sum, Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hpR.ne',
    one_mul]

/-- Integrability of a single coordinate under the pooled law. -/
private lemma integrable_coord (m n : ℕ) (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (g : ℝ → ℝ) (hgm : Measurable g)
    (hY : Integrable g PY) (hZ : Integrable g PZ) (l : Fin (m + n)) :
    Integrable (fun x : Fin (m + n) → ℝ => g (x l)) (twoSampleLaw m n PY PZ) := by
  refine Fin.addCases (m := m) (n := n)
    (motive := fun l => Integrable (fun x : Fin (m + n) → ℝ => g (x l))
      (twoSampleLaw m n PY PZ)) (fun i => ?_) (fun j => ?_) l
  · exact ((measurePreserving_evalY m n PY PZ i).integrable_comp
      hgm.aestronglyMeasurable).mpr hY
  · exact ((measurePreserving_evalZ m n PY PZ j).integrable_comp
      hgm.aestronglyMeasurable).mpr hZ

/-- **The `L¹` tail bound, uniform in the sample sizes.** For a nonnegative integrable `h`,
the group average of the probability that a permuted block average of `h` exceeds `ε` is at
most `ε⁻¹ (∫h dP_Y + ∫h dP_Z)` — no second moment and no dependence on `m`, `n`. -/
private lemma perm_avg_blockAvg_tail_le (m n : ℕ) (PY PZ : Measure ℝ)
    [IsProbabilityMeasure PY] [IsProbabilityMeasure PZ] {p : ℕ} (hp : 0 < p)
    (a : Fin p → Fin (m + n)) (h : ℝ → ℝ) (hhm : Measurable h) (hnn : ∀ t, 0 ≤ h t)
    (hY : Integrable h PY) (hZ : Integrable h PZ) {ε : ℝ} (hε : 0 < ε) :
    (Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (m + n)), (twoSampleLaw m n PY PZ).real
          {x | ε ≤ (p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))}
      ≤ ε⁻¹ * ((∫ t, h t ∂PY) + ∫ t, h t ∂PZ) := by
  classical
  have hcard : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Fin (m + n))))
  have hpR : (0 : ℝ) ≤ ((p : ℝ))⁻¹ := by positivity
  -- the per-permutation integrand
  have hAmeas : ∀ σ : Equiv.Perm (Fin (m + n)),
      Measurable (fun x : Fin (m + n) → ℝ => (p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))) := by
    intro σ
    simp only [perm_smul_apply]
    exact (Finset.measurable_sum _ fun i _ => hhm.comp (measurable_pi_apply _)).const_mul _
  have hAint : ∀ σ : Equiv.Perm (Fin (m + n)),
      Integrable (fun x : Fin (m + n) → ℝ => (p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i)))
        (twoSampleLaw m n PY PZ) := by
    intro σ
    simp only [perm_smul_apply]
    exact (integrable_finset_sum _ fun i _ =>
      integrable_coord m n PY PZ h hhm hY hZ (σ⁻¹ (a i))).const_mul _
  have hAnn : ∀ (σ : Equiv.Perm (Fin (m + n))) (x : Fin (m + n) → ℝ),
      0 ≤ (p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i)) :=
    fun σ x => mul_nonneg hpR (Finset.sum_nonneg fun i _ => hnn _)
  -- Markov, one permutation at a time
  have hmark : ∀ σ : Equiv.Perm (Fin (m + n)), (twoSampleLaw m n PY PZ).real
      {x | ε ≤ (p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))}
      ≤ ε⁻¹ * ∫ x, ((p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))) ∂(twoSampleLaw m n PY PZ) :=
    fun σ => measureReal_ge_le_integral _ (hAmeas σ) (hAnn σ) (hAint σ) hε
  have hstep1 : (Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin (m + n)), (twoSampleLaw m n PY PZ).real
        {x | ε ≤ (p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))}
      ≤ (Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (m + n)),
          ε⁻¹ * ∫ x, ((p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))) ∂(twoSampleLaw m n PY PZ) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hmark σ) (by positivity)
  refine hstep1.trans ?_
  have heq : (Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (m + n)),
          ε⁻¹ * ∫ x, ((p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))) ∂(twoSampleLaw m n PY PZ)
      = ε⁻¹ * ∫ x, (((m + n : ℕ) : ℝ)⁻¹ * ∑ l, h (x l)) ∂(twoSampleLaw m n PY PZ) := by
    have hexch : ∑ σ : Equiv.Perm (Fin (m + n)),
        ∫ x, ((p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))) ∂(twoSampleLaw m n PY PZ)
        = ∫ x, (∑ σ : Equiv.Perm (Fin (m + n)),
            (p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))) ∂(twoSampleLaw m n PY PZ) :=
      (integral_finset_sum _ fun σ _ => hAint σ).symm
    have hpt : ∀ x : Fin (m + n) → ℝ,
        (Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin (m + n)), (p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))
        = ((m + n : ℕ) : ℝ)⁻¹ * ∑ l, h (x l) := by
      intro x
      simpa only [perm_smul_apply, Fintype.card_fin] using
        avg_perm_blockAvg_eq (N := m + n) hp a (fun l => h (x l))
    calc (Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin (m + n)),
            ε⁻¹ * ∫ x, ((p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))) ∂(twoSampleLaw m n PY PZ)
        = ε⁻¹ * ((Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin (m + n)),
              ∫ x, ((p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))) ∂(twoSampleLaw m n PY PZ)) := by
          rw [← Finset.mul_sum]; ring
      _ = ε⁻¹ * ((Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ *
            ∫ x, (∑ σ : Equiv.Perm (Fin (m + n)),
              (p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))) ∂(twoSampleLaw m n PY PZ)) := by
          rw [hexch]
      _ = ε⁻¹ * ∫ x, ((Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin (m + n)),
              (p : ℝ)⁻¹ * ∑ i, h ((σ • x) (a i))) ∂(twoSampleLaw m n PY PZ) := by
          rw [integral_const_mul]
      _ = ε⁻¹ * ∫ x, (((m + n : ℕ) : ℝ)⁻¹ * ∑ l, h (x l)) ∂(twoSampleLaw m n PY PZ) := by
          congr 1
          exact integral_congr_ae (ae_of_all _ hpt)
  rw [heq]
  · -- and compute the pooled expectation
    have hint := integral_sum_coords m n PY PZ h hhm hY hZ
    have hNcast : ((m + n : ℕ) : ℝ) = (m : ℝ) + n := by push_cast; ring
    have hYnn : (0 : ℝ) ≤ ∫ t, h t ∂PY := integral_nonneg fun t => hnn t
    have hZnn : (0 : ℝ) ≤ ∫ t, h t ∂PZ := integral_nonneg fun t => hnn t
    rw [integral_const_mul, hint]
    rcases Nat.eq_zero_or_pos (m + n) with hN0 | hN0
    · rw [hN0]
      simp only [Nat.cast_zero, inv_zero, zero_mul, mul_zero]
      positivity
    · have hNpos : (0 : ℝ) < ((m + n : ℕ) : ℝ) := by exact_mod_cast hN0
      have hkey : ((m + n : ℕ) : ℝ)⁻¹ * ((m : ℝ) * (∫ t, h t ∂PY)
          + (n : ℝ) * ∫ t, h t ∂PZ) ≤ (∫ t, h t ∂PY) + ∫ t, h t ∂PZ := by
        rw [inv_mul_le_iff₀ hNpos, hNcast]
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        nlinarith
      exact mul_le_mul_of_nonneg_left hkey (by positivity)

/-- A union bound for a group average of probabilities. -/
private lemma avg_measureReal_le_add' {𝓨 : Type*} [MeasurableSpace 𝓨] (P : Measure 𝓨)
    [IsProbabilityMeasure P] {G : Type*} [Fintype G] [Nonempty G]
    (S U V : G → Set 𝓨) (hsub : ∀ g, S g ⊆ U g ∪ V g) :
    (Fintype.card G : ℝ)⁻¹ * ∑ g : G, P.real (S g)
      ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, P.real (U g)
        + (Fintype.card G : ℝ)⁻¹ * ∑ g : G, P.real (V g) := by
  have hle : ∀ g : G, P.real (S g) ≤ P.real (U g) + P.real (V g) := fun g =>
    (measureReal_mono (hsub g) (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  have hstep : (Fintype.card G : ℝ)⁻¹ * ∑ g : G, P.real (S g)
      ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, (P.real (U g) + P.real (V g)) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => hle g) (by positivity)
  refine hstep.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, mul_add]


/-- **The randomized block average converges, assuming only integrability.** This is the
generic hypergeometric input of Theorem 17.3.3: for an integrable `f`, the average of `f`
over a block of `p k` positions of a uniformly permuted pooled sample converges, in the
group-averaged in-probability sense, to the pooled mixture
`λ/(1+λ) · ∫f dP_Y + 1/(1+λ) · ∫f dP_Z`. Applied to `f = id` it gives the block means and to
`f = (·)²` the block second moments, which is all the studentizing scale is made of. -/
private lemma tendstoInProbRandomized_blockAvg (PY PZ : Measure ℝ)
    [IsProbabilityMeasure PY] [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam : ℝ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    (p : ℕ → ℕ) (a : ∀ k, Fin (p k) → Fin (m k + n k)) (ha : ∀ k, Function.Injective (a k))
    (hp : Tendsto p atTop atTop)
    (f : ℝ → ℝ) (hfm : Measurable f) (hY : Integrable f PY) (hZ : Integrable f PZ) :
    ∀ ε > (0 : ℝ), Tendsto (fun k =>
        (Fintype.card (Equiv.Perm (Fin (m k + n k))) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin (m k + n k)), (twoSampleLaw (m k) (n k) PY PZ).real
            {x | ε ≤ |(p k : ℝ)⁻¹ * (∑ i, f ((σ • x) (a k i)))
              - (lam / (1 + lam) * (∫ t, f t ∂PY) + 1 / (1 + lam) * ∫ t, f t ∂PZ)|})
      atTop (𝓝 0) := by
  classical
  intro ε hε
  set L : ℝ := lam / (1 + lam) * (∫ t, f t ∂PY) + 1 / (1 + lam) * ∫ t, f t ∂PZ with hLdef
  have hε3 : (0 : ℝ) < ε / 3 := by positivity
  -- the truncated limits converge to `L`, and the truncation errors vanish in `L¹`
  have hLj : Tendsto (fun j : ℕ => lam / (1 + lam) * (∫ t, truncAt j f t ∂PY)
      + 1 / (1 + lam) * ∫ t, truncAt j f t ∂PZ) atTop (𝓝 L) :=
    ((tendsto_integral_truncAt f hfm hY).const_mul _).add
      ((tendsto_integral_truncAt f hfm hZ).const_mul _)
  have hTail : Tendsto (fun j : ℕ => (ε / 3)⁻¹ *
      ((∫ t, |f t - truncAt j f t| ∂PY) + ∫ t, |f t - truncAt j f t| ∂PZ)) atTop (𝓝 0) := by
    have h := ((tendsto_integral_sub_truncAt f hfm hY).add
      (tendsto_integral_sub_truncAt f hfm hZ)).const_mul ((ε / 3)⁻¹)
    simpa using h
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- choose a truncation level
  obtain ⟨j, hjTail, hjL⟩ : ∃ j : ℕ,
      ((ε / 3)⁻¹ * ((∫ t, |f t - truncAt j f t| ∂PY)
        + ∫ t, |f t - truncAt j f t| ∂PZ) < δ / 2)
      ∧ |(lam / (1 + lam) * (∫ t, truncAt j f t ∂PY)
            + 1 / (1 + lam) * ∫ t, truncAt j f t ∂PZ) - L| < ε / 3 := by
    have e1 := hTail.eventually (eventually_lt_nhds (show (0 : ℝ) < δ / 2 by positivity))
    have e2 := hLj.eventually (Metric.ball_mem_nhds L hε3)
    obtain ⟨j, hj1, hj2⟩ := (e1.and e2).exists
    exact ⟨j, hj1, by rwa [Real.dist_eq] at hj2⟩
  -- the truncated statistic converges, by the square-integrable case
  have htr := tendstoInProbRandomized_blockAvg_of_sq PY PZ m n hm hn hratio hlam p a ha hp
    (truncAt j f) (measurable_truncAt j hfm) (integrable_truncAt j hfm)
    (integrable_truncAt j hfm) (integrable_truncAt_sq j hfm) (integrable_truncAt_sq j hfm)
    (ε / 3) hε3
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 htr (δ / 2) (by positivity)
  refine eventually_atTop.1 ?_
  filter_upwards [eventually_ge_atTop K, hp.eventually_gt_atTop 0] with k hkK hpk
  have hpR : (0 : ℝ) < (p k : ℝ) := by exact_mod_cast hpk
  -- the union bound
  have hsub : ∀ σ : Equiv.Perm (Fin (m k + n k)),
      {x : Fin (m k + n k) → ℝ | ε ≤ |(p k : ℝ)⁻¹ * (∑ i, f ((σ • x) (a k i))) - L|}
      ⊆ {x : Fin (m k + n k) → ℝ | ε / 3 ≤ (p k : ℝ)⁻¹ *
            ∑ i, |f ((σ • x) (a k i)) - truncAt j f ((σ • x) (a k i))|}
        ∪ {x : Fin (m k + n k) → ℝ | ε / 3 ≤ |(p k : ℝ)⁻¹ *
            (∑ i, truncAt j f ((σ • x) (a k i)))
            - (lam / (1 + lam) * (∫ t, truncAt j f t ∂PY)
              + 1 / (1 + lam) * ∫ t, truncAt j f t ∂PZ)|} := by
    intro σ x hx
    simp only [Set.mem_setOf_eq, Set.mem_union] at hx ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    set S1 : ℝ := ∑ i, f ((σ • x) (a k i)) with hS1
    set S2 : ℝ := ∑ i, truncAt j f ((σ • x) (a k i)) with hS2
    set M : ℝ := lam / (1 + lam) * (∫ t, truncAt j f t ∂PY)
      + 1 / (1 + lam) * ∫ t, truncAt j f t ∂PZ with hM
    have hdiffle : |(p k : ℝ)⁻¹ * S1 - (p k : ℝ)⁻¹ * S2|
        ≤ (p k : ℝ)⁻¹ * ∑ i, |f ((σ • x) (a k i)) - truncAt j f ((σ • x) (a k i))| := by
      have hd : (p k : ℝ)⁻¹ * S1 - (p k : ℝ)⁻¹ * S2
          = (p k : ℝ)⁻¹ * ∑ i, (f ((σ • x) (a k i)) - truncAt j f ((σ • x) (a k i))) := by
        rw [hS1, hS2, Finset.sum_sub_distrib, mul_sub]
      rw [hd, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p k : ℝ)⁻¹)]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    have hA := abs_add_le ((p k : ℝ)⁻¹ * S1 - (p k : ℝ)⁻¹ * S2) ((p k : ℝ)⁻¹ * S2 - L)
    have hB := abs_add_le ((p k : ℝ)⁻¹ * S2 - M) (M - L)
    have e1 : (p k : ℝ)⁻¹ * S1 - L
        = ((p k : ℝ)⁻¹ * S1 - (p k : ℝ)⁻¹ * S2) + ((p k : ℝ)⁻¹ * S2 - L) := by ring
    have e2 : (p k : ℝ)⁻¹ * S2 - L = ((p k : ℝ)⁻¹ * S2 - M) + (M - L) := by ring
    have hD2 : |(p k : ℝ)⁻¹ * S2 - L| ≤ |(p k : ℝ)⁻¹ * S2 - M| + |M - L| := by
      rw [e2]; exact hB
    rw [e1] at hx
    linarith
  have hbound := avg_measureReal_le_add' (twoSampleLaw (m k) (n k) PY PZ)
    (fun σ => {x : Fin (m k + n k) → ℝ |
      ε ≤ |(p k : ℝ)⁻¹ * (∑ i, f ((σ • x) (a k i))) - L|})
    (fun σ => {x : Fin (m k + n k) → ℝ | ε / 3 ≤ (p k : ℝ)⁻¹ *
      ∑ i, |f ((σ • x) (a k i)) - truncAt j f ((σ • x) (a k i))|})
    (fun σ => {x : Fin (m k + n k) → ℝ | ε / 3 ≤ |(p k : ℝ)⁻¹ *
      (∑ i, truncAt j f ((σ • x) (a k i)))
      - (lam / (1 + lam) * (∫ t, truncAt j f t ∂PY)
        + 1 / (1 + lam) * ∫ t, truncAt j f t ∂PZ)|}) hsub
  -- the truncation term, by the uniform `L¹` tail bound
  have htail := perm_avg_blockAvg_tail_le (m k) (n k) PY PZ hpk (a k)
    (fun t => |f t - truncAt j f t|) ((hfm.sub (measurable_truncAt j hfm)).abs)
    (fun t => abs_nonneg _) ((hY.sub (integrable_truncAt j hfm)).abs)
    ((hZ.sub (integrable_truncAt j hfm)).abs) hε3
  -- the truncated term, by the square-integrable case
  have hlast := hK k hkK
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun σ _ => measureReal_nonneg))] at hlast
  have hTnn : (0 : ℝ) ≤ (Fintype.card (Equiv.Perm (Fin (m k + n k))) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin (m k + n k)), (twoSampleLaw (m k) (n k) PY PZ).real
        {x | ε ≤ |(p k : ℝ)⁻¹ * (∑ i, f ((σ • x) (a k i))) - L|} :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun σ _ => measureReal_nonneg)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hTnn]
  linarith


/-! ### Two more closure properties of group-averaged convergence -/

/-- Replacing the statistic by an eventually-equal one. -/
private lemma tendstoInProbRandomized_congr {𝓨 : ℕ → Type*} [∀ k, MeasurableSpace (𝓨 k)]
    (G : ℕ → Type*) [∀ k, Group (G k)] [∀ k, Fintype (G k)] [∀ k, MulAction (G k) (𝓨 k)]
    (P : ∀ k, Measure (𝓨 k)) {A B : ∀ k, 𝓨 k → ℝ} {a : ℝ}
    (h : TendstoInProbRandomized G P A a) (hAB : ∀ᶠ k in atTop, ∀ y, A k y = B k y) :
    TendstoInProbRandomized G P B a := by
  intro ε hε
  refine (h ε hε).congr' ?_
  filter_upwards [hAB] with k hk
  have hset : ∀ g : G k, {x | ε ≤ |A k (g • x) - a|} = {x | ε ≤ |B k (g • x) - a|} := by
    intro g; ext x; simp only [Set.mem_setOf_eq, hk]
  simp only [hset]

/-- **Sums pass to the limit at randomized data.** -/
private lemma tendstoInProbRandomized_add {𝓨 : ℕ → Type*} [∀ k, MeasurableSpace (𝓨 k)]
    (G : ℕ → Type*) [∀ k, Group (G k)] [∀ k, Fintype (G k)] [∀ k, MulAction (G k) (𝓨 k)]
    (P : ∀ k, Measure (𝓨 k)) [∀ k, IsProbabilityMeasure (P k)]
    {A B : ∀ k, 𝓨 k → ℝ} {a b : ℝ}
    (hA : TendstoInProbRandomized G P A a) (hB : TendstoInProbRandomized G P B b) :
    TendstoInProbRandomized G P (fun k y => A k y + B k y) (a + b) := by
  intro ε hε
  have hsub : ∀ (k : ℕ) (g : G k),
      {x : 𝓨 k | ε ≤ |(A k (g • x) + B k (g • x)) - (a + b)|}
        ⊆ {x : 𝓨 k | ε / 2 ≤ |A k (g • x) - a|} ∪ {x : 𝓨 k | ε / 2 ≤ |B k (g • x) - b|} := by
    intro k g x hx
    simp only [Set.mem_setOf_eq, Set.mem_union] at hx ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have htri := abs_add_le (A k (g • x) - a) (B k (g • x) - b)
    have heq : (A k (g • x) + B k (g • x)) - (a + b)
        = (A k (g • x) - a) + (B k (g • x) - b) := by ring
    rw [heq] at hx
    linarith
  have hlim : Tendsto (fun k => (Fintype.card (G k) : ℝ)⁻¹ *
        ∑ g : G k, (P k).real {x | ε / 2 ≤ |A k (g • x) - a|}
      + (Fintype.card (G k) : ℝ)⁻¹ *
        ∑ g : G k, (P k).real {x | ε / 2 ≤ |B k (g • x) - b|}) atTop (𝓝 0) := by
    have h2 := (hA (ε / 2) (by positivity)).add (hB (ε / 2) (by positivity))
    rwa [add_zero] at h2
  refine squeeze_zero (fun k => ?_) (fun k => avg_measureReal_le_add' (P k) _ _ _ (hsub k))
    hlim
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun g _ => measureReal_nonneg)

/-- **Multiplication by a deterministic convergent factor, at randomized data.** -/
private lemma tendstoInProbRandomized_const_mul {𝓨 : ℕ → Type*} [∀ k, MeasurableSpace (𝓨 k)]
    (G : ℕ → Type*) [∀ k, Group (G k)] [∀ k, Fintype (G k)] [∀ k, MulAction (G k) (𝓨 k)]
    (P : ∀ k, Measure (𝓨 k)) [∀ k, IsProbabilityMeasure (P k)]
    {A : ∀ k, 𝓨 k → ℝ} {c : ℕ → ℝ} {a cl : ℝ}
    (hc : Tendsto c atTop (𝓝 cl)) (hA : TendstoInProbRandomized G P A a) :
    TendstoInProbRandomized G P (fun k y => c k * A k y) (cl * a) := by
  intro ε hε
  have hpos : (0 : ℝ) < |cl| + 1 := by positivity
  set ρ : ℝ := ε / (2 * (|cl| + 1)) with hρdef
  have hρpos : 0 < ρ := by positivity
  have hev1 : ∀ᶠ k in atTop, |c k| ≤ |cl| + 1 := by
    have := hc.abs.eventually (eventually_lt_nhds (show |cl| < |cl| + 1 by linarith))
    exact this.mono fun k hk => hk.le
  have hev2 : ∀ᶠ k in atTop, |c k - cl| * |a| < ε / 2 := by
    have hlim : Tendsto (fun k => |c k - cl| * |a|) atTop (𝓝 0) := by
      have h0 : Tendsto (fun k => c k - cl) atTop (𝓝 0) := by simpa using hc.sub_const cl
      simpa using (h0.abs).mul_const |a|
    exact hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity))
  have hbound : ∀ᶠ k in atTop, (Fintype.card (G k) : ℝ)⁻¹ *
      ∑ g : G k, (P k).real {x | ε ≤ |c k * A k (g • x) - cl * a|}
      ≤ (Fintype.card (G k) : ℝ)⁻¹ *
        ∑ g : G k, (P k).real {x | ρ ≤ |A k (g • x) - a|} := by
    filter_upwards [hev1, hev2] with k hk1 hk2
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => ?_) (by positivity)
    refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_contra hcon
    push Not at hcon
    have hsplit : c k * A k (g • x) - cl * a
        = c k * (A k (g • x) - a) + (c k - cl) * a := by ring
    have h1 : |c k * (A k (g • x) - a)| ≤ (|cl| + 1) * ρ := by
      rw [abs_mul]
      exact mul_le_mul hk1 hcon.le (abs_nonneg _) (by positivity)
    have h2 : (|cl| + 1) * ρ = ε / 2 := by rw [hρdef]; field_simp
    have h3 : |(c k - cl) * a| < ε / 2 := by rw [abs_mul]; exact hk2
    have htri := abs_add_le (c k * (A k (g • x) - a)) ((c k - cl) * a)
    rw [hsplit] at hx
    linarith
  refine squeeze_zero' (Eventually.of_forall fun k => ?_) hbound (hA ρ hρpos)
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun g _ => measureReal_nonneg)

/-! ### The randomized studentizing scale

Under a uniform permutation of the pooled data each block is a sample **without
replacement** from the pooled `N = m + n` values, so — unlike the unconditional scale of
`tendstoInProb_twoSampleScale`, which converges to `s² = σ²(P_Y) + λσ²(P_Z)` — *both* block
variances converge to the same pooled variance
$$ \bar v = \frac{\lambda \sigma^2(P_Y) + \sigma^2(P_Z)}{1 + \lambda} , $$
whence `D_{m,n}(π·)² = S²_Y(π·) + (m/n) S²_Z(π·) → (1 + λ)\bar v = τ²`. The two limits differ
exactly when `λ ≠ 1` and the variances differ — the failure of the *unstudentized* test —
and dividing by the scale sends both to `N(0,1)`, which is the content of this file. -/

/-- **The studentizing scale, evaluated at randomized data, is consistent for `τ`**, the
permutation scale `τ² = λσ²(P_Y) + σ²(P_Z)`. -/
private lemma tendstoInProbRandomized_twoSampleScale (PY PZ : Measure ℝ)
    [IsProbabilityMeasure PY] [IsProbabilityMeasure PZ] (m n : ℕ → ℕ)
    {lam varY varZ μ τ : ℝ}
    -- USER-INPUT: both sample sizes grow; the asymptotic regime
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: `m/n → λ`, with a nondegenerate limit
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: equal means; the null hypothesis under test
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances, not assumed equal, both nonzero
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ)
    -- LEAN-ONLY: positive square root of the permutation variance
    (hτpos : 0 < τ) (hτ : τ ^ 2 = lam * varY + varZ) :
    TendstoInProbRandomized (fun k => Equiv.Perm (Fin (m k + n k)))
      (fun k => twoSampleLaw (m k) (n k) PY PZ)
      (fun k x => twoSampleScale (m k) (n k) x) τ := by
  -- **The hypergeometric half of Theorem 17.3.3** (wave 8, closed here).
  -- Route, exactly as the wave-5 note laid it out:
  -- (a) the group-average calculus (`tendstoInProbRandomized_add`, `_const_mul`, `_comp`,
  --     `_congr`) reduces the square root, the sum and the factor `m/n` to the two block
  --     variances;
  -- (b) `ForMathlib/PermutationMarginals` supplies the exact `O(1/p)` variance of a
  --     permuted block average and the Chebyshev step over the group;
  -- (c) recentring against the pooled mean is `perm_avg_indicator_blockAvg_inv_sub_mean_le`
  --     and the exchange of the group average with the data law is
  --     `avg_measureReal_eq_integral_avg_indicator`; the resulting integral is bounded
  --     uniformly by `perm_avg_block_sub_pooled_le`, whence
  --     `tendstoInProbRandomized_blockAvg_of_sq`;
  -- (d) the fourth-moment obstruction for the block SECOND moments is removed by
  --     truncation: `tendstoInProbRandomized_blockAvg` pays for the discarded part with the
  --     `L¹` tail bound `perm_avg_blockAvg_tail_le`, which is uniform in `k` because the
  --     group average of a permuted block average is *exactly* the pooled average
  --     (`avg_perm_blockAvg_eq`);
  -- (e) the pooled empirical moments converge by `tendstoInProb_pooledAvg`, giving the same
  --     limit `v̄ = (λ varY + varZ)/(1 + λ)` for BOTH blocks and `τ² = (1 + λ) v̄`.
  classical
  have hne : (1 : ℝ) + lam ≠ 0 := by positivity
  have hidY : Integrable (fun t : ℝ => t) PY := by simpa using! hYL2.integrable (by norm_num)
  have hidZ : Integrable (fun t : ℝ => t) PZ := by simpa using! hZL2.integrable (by norm_num)
  have hsqY : Integrable (fun t : ℝ => t ^ 2) PY := by simpa using hYL2.integrable_sq
  have hsqZ : Integrable (fun t : ℝ => t ^ 2) PZ := by simpa using hZL2.integrable_sq
  -- (i) the four randomized block averages
  have hYmean : TendstoInProbRandomized (fun k => Equiv.Perm (Fin (m k + n k)))
      (fun k => twoSampleLaw (m k) (n k) PY PZ)
      (fun k y => (m k : ℝ)⁻¹ * ∑ i : Fin (m k), y (Fin.castAdd (n k) i))
      (lam / (1 + lam) * (∫ t, t ∂PY) + 1 / (1 + lam) * ∫ t, t ∂PZ) :=
    tendstoInProbRandomized_blockAvg PY PZ m n hm hn hratio hlam m
      (fun k => Fin.castAdd (n k)) (fun k => Fin.castAdd_injective _ _) hm
      (fun t : ℝ => t) measurable_id hidY hidZ
  have hZmean : TendstoInProbRandomized (fun k => Equiv.Perm (Fin (m k + n k)))
      (fun k => twoSampleLaw (m k) (n k) PY PZ)
      (fun k y => (n k : ℝ)⁻¹ * ∑ j : Fin (n k), y (Fin.natAdd (m k) j))
      (lam / (1 + lam) * (∫ t, t ∂PY) + 1 / (1 + lam) * ∫ t, t ∂PZ) :=
    tendstoInProbRandomized_blockAvg PY PZ m n hm hn hratio hlam n
      (fun k => Fin.natAdd (m k)) (fun k => Fin.natAdd_injective _ _) hn
      (fun t : ℝ => t) measurable_id hidY hidZ
  have hYsq : TendstoInProbRandomized (fun k => Equiv.Perm (Fin (m k + n k)))
      (fun k => twoSampleLaw (m k) (n k) PY PZ)
      (fun k y => (m k : ℝ)⁻¹ * ∑ i : Fin (m k), y (Fin.castAdd (n k) i) ^ 2)
      (lam / (1 + lam) * (∫ t, t ^ 2 ∂PY) + 1 / (1 + lam) * ∫ t, t ^ 2 ∂PZ) :=
    tendstoInProbRandomized_blockAvg PY PZ m n hm hn hratio hlam m
      (fun k => Fin.castAdd (n k)) (fun k => Fin.castAdd_injective _ _) hm
      (fun t : ℝ => t ^ 2) (by fun_prop) hsqY hsqZ
  have hZsq : TendstoInProbRandomized (fun k => Equiv.Perm (Fin (m k + n k)))
      (fun k => twoSampleLaw (m k) (n k) PY PZ)
      (fun k y => (n k : ℝ)⁻¹ * ∑ j : Fin (n k), y (Fin.natAdd (m k) j) ^ 2)
      (lam / (1 + lam) * (∫ t, t ^ 2 ∂PY) + 1 / (1 + lam) * ∫ t, t ^ 2 ∂PZ) :=
    tendstoInProbRandomized_blockAvg PY PZ m n hm hn hratio hlam n
      (fun k => Fin.natAdd (m k)) (fun k => Fin.natAdd_injective _ _) hn
      (fun t : ℝ => t ^ 2) (by fun_prop) hsqY hsqZ
  -- (ii) the two block variances, as (second moment) − (mean)²
  have hYneg := tendstoInProbRandomized_comp (fun k => Equiv.Perm (Fin (m k + n k)))
    (fun k => twoSampleLaw (m k) (n k) PY PZ) (φ := fun u : ℝ => -(u ^ 2))
    (by fun_prop) hYmean
  have hZneg := tendstoInProbRandomized_comp (fun k => Equiv.Perm (Fin (m k + n k)))
    (fun k => twoSampleLaw (m k) (n k) PY PZ) (φ := fun u : ℝ => -(u ^ 2))
    (by fun_prop) hZmean
  have hYvar0 := tendstoInProbRandomized_add (fun k => Equiv.Perm (Fin (m k + n k)))
    (fun k => twoSampleLaw (m k) (n k) PY PZ) hYsq hYneg
  have hZvar0 := tendstoInProbRandomized_add (fun k => Equiv.Perm (Fin (m k + n k)))
    (fun k => twoSampleLaw (m k) (n k) PY PZ) hZsq hZneg
  have hYvar : TendstoInProbRandomized (fun k => Equiv.Perm (Fin (m k + n k)))
      (fun k => twoSampleLaw (m k) (n k) PY PZ)
      (fun k y => twoSampleVarY (m k) (n k) y)
      ((lam / (1 + lam) * (∫ t, t ^ 2 ∂PY) + 1 / (1 + lam) * ∫ t, t ^ 2 ∂PZ)
        + -((lam / (1 + lam) * (∫ t, t ∂PY) + 1 / (1 + lam) * ∫ t, t ∂PZ) ^ 2)) := by
    refine tendstoInProbRandomized_congr _ _ hYvar0 ?_
    filter_upwards [hm.eventually_gt_atTop 0] with k hmk y
    exact (twoSampleVarY_eq hmk y).symm
  have hZvar : TendstoInProbRandomized (fun k => Equiv.Perm (Fin (m k + n k)))
      (fun k => twoSampleLaw (m k) (n k) PY PZ)
      (fun k y => twoSampleVarZ (m k) (n k) y)
      ((lam / (1 + lam) * (∫ t, t ^ 2 ∂PY) + 1 / (1 + lam) * ∫ t, t ^ 2 ∂PZ)
        + -((lam / (1 + lam) * (∫ t, t ∂PY) + 1 / (1 + lam) * ∫ t, t ∂PZ) ^ 2)) := by
    refine tendstoInProbRandomized_congr _ _ hZvar0 ?_
    filter_upwards [hn.eventually_gt_atTop 0] with k hnk y
    exact (twoSampleVarZ_eq hnk y).symm
  -- (iii) assemble the squared scale
  have hZscaled := tendstoInProbRandomized_const_mul
    (fun k => Equiv.Perm (Fin (m k + n k)))
    (fun k => twoSampleLaw (m k) (n k) PY PZ) hratio hZvar
  have hsq := tendstoInProbRandomized_add (fun k => Equiv.Perm (Fin (m k + n k)))
    (fun k => twoSampleLaw (m k) (n k) PY PZ) hYvar hZscaled
  have hlimeq : ((lam / (1 + lam) * (∫ t, t ^ 2 ∂PY) + 1 / (1 + lam) * ∫ t, t ^ 2 ∂PZ)
        + -((lam / (1 + lam) * (∫ t, t ∂PY) + 1 / (1 + lam) * ∫ t, t ∂PZ) ^ 2))
      + lam * ((lam / (1 + lam) * (∫ t, t ^ 2 ∂PY) + 1 / (1 + lam) * ∫ t, t ^ 2 ∂PZ)
        + -((lam / (1 + lam) * (∫ t, t ∂PY) + 1 / (1 + lam) * ∫ t, t ∂PZ) ^ 2)) = τ ^ 2 := by
    have hQYv : (∫ t, t ^ 2 ∂PY) = varY + μ ^ 2 := by
      have h := var_eq_second_sub_sq hYL2 hmeanY hvarY; linarith
    have hQZv : (∫ t, t ^ 2 ∂PZ) = varZ + μ ^ 2 := by
      have h := var_eq_second_sub_sq hZL2 hmeanZ hvarZ; linarith
    rw [hQYv, hQZv, hmeanY, hmeanZ, hτ]
    field_simp
    ring
  rw [hlimeq] at hsq
  -- (iv) take the square root
  have hscale := tendstoInProbRandomized_comp (fun k => Equiv.Perm (Fin (m k + n k)))
    (fun k => twoSampleLaw (m k) (n k) PY PZ) (φ := Real.sqrt)
    Real.continuous_sqrt.continuousAt hsq
  rw [Real.sqrt_sq hτpos.le] at hscale
  exact hscale

/-! ### Asymptotic validity under unequal variances -/

/-- The permutation action `σ • x = x ∘ σ⁻¹` is measurable in `x`. (A local copy: the
`TwoSamplePermutation` version is `private` to that module.) -/
private lemma measurable_perm_smul' (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    Measurable (fun x : Fin N → ℝ => σ • x) := by
  have hfun : (fun x : Fin N → ℝ => σ • x) = fun x i => x (σ⁻¹ i) := by
    ext x i; exact perm_smul_apply σ x i
  rw [hfun]
  exact measurable_pi_lambda _ fun i => measurable_pi_apply _

/-- The c.d.f. of an atomless probability measure on `ℝ` is continuous. (A local copy: the
`TwoSamplePermutation` and `SignChange` versions are `private` to those modules.) -/
private lemma continuousAt_cdf_of_noAtoms' (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (t : ℝ) : ContinuousAt (cdf ν) t := by
  have hmono : Monotone (cdf ν) := monotone_cdf ν
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  have hright : Function.rightLim (cdf ν) t = cdf ν t :=
    (hmono.continuousWithinAt_Ioi_iff_rightLim_eq).1
      (((cdf ν).right_continuous t).mono Set.Ioi_subset_Ici_self)
  have hle : Function.leftLim (cdf ν) t ≤ cdf ν t := hmono.leftLim_le le_rfl
  have hge : cdf ν t ≤ Function.leftLim (cdf ν) t := by
    have h0 := (cdf ν).measure_singleton t
    rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos] at h0
    exact h0
  rw [le_antisymm hle hge, hright]

/-- **The studentized randomization distribution converges to the standard normal.**
Under equal means, finite nonzero (and possibly **different**) population variances, and
`m/n → λ ∈ (0, ∞)`,
$$ \hat R^{\tilde T}_{m,n}(t) \;\xrightarrow{P}\; \Phi(t) . $$
The limit carries no unknown parameter — that is what studentization buys. -/
theorem randDist_studentized_tendstoInProb (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ μ : ℝ}
    -- USER-INPUT: both sample sizes grow; the asymptotic regime
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: `m/n → λ`, with a nondegenerate limit
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: the two populations have the same mean; the null hypothesis under test
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances; note they are **not** assumed equal
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    -- USER-INPUT: both variances are nonzero
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ) (t : ℝ) :
    TendstoInProbTriangular (fun k => twoSampleLaw (m k) (n k) PY PZ)
      (fun k x => randDist (Equiv.Perm (Fin (m k + n k)))
        (studentizedTwoSample (m k) (n k)) x t)
      (cdf (gaussianReal 0 1) t) := by
  -- `studentizedTwoSample = (1/twoSampleScale) · twoSampleMeanDiff + 0`, so this is the
  -- Slutsky transfer `randDist_affine_tendstoInProb` with `A = 1/scale → 1/τ`, `B = 0`, joint
  -- law from `weakConverges_randPairLaw_twoSample`, and limit c.d.f.
  -- `cdf ((N(0,τ²)).map (τ⁻¹ · )) = cdf (N(0,1))`.
  -- The two debts are named: the permutation CLT
  -- (`TwoSamplePermutation.weakConverges_randPairLaw_twoSample`, Hoeffding's combinatorial
  -- CLT, out of scope) and the randomized scale consistency
  -- (`tendstoInProbRandomized_twoSampleScale` above).
  classical
  have hposτ : (0 : ℝ) < lam * varY + varZ := by positivity
  set τ : ℝ := Real.sqrt (lam * varY + varZ) with hτdef
  have hτpos : 0 < τ := Real.sqrt_pos.2 hposτ
  have hτne : τ ≠ 0 := hτpos.ne'
  have hτ : τ ^ 2 = lam * varY + varZ := Real.sq_sqrt hposτ.le
  set R : Measure ℝ := gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ)) with hRdef
  -- The affine image of the permutation limit is the standard normal.
  have hmapR : R.map (fun u : ℝ => τ⁻¹ * u + 0) = gaussianReal 0 1 := by
    have hfun : (fun u : ℝ => τ⁻¹ * u + 0) = (τ⁻¹ * ·) := by funext u; rw [add_zero]
    rw [hRdef, hfun, gaussianReal_map_const_mul]
    congr 1
    · rw [mul_zero]
    · refine NNReal.coe_injective ?_
      simp only [NNReal.coe_mul, NNReal.coe_one, NNReal.coe_mk]
      field_simp
  haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hcont : ContinuousAt (cdf (R.map (fun u : ℝ => τ⁻¹ * u + 0))) t := by
    rw [hmapR]; exact continuousAt_cdf_of_noAtoms' _ t
  -- The three measurability side conditions, and the two convergence inputs.
  have hTmeas : ∀ k, Measurable (twoSampleMeanDiff (m k) (n k)) := by
    intro k; unfold twoSampleMeanDiff; fun_prop
  have hAmeas : ∀ k, Measurable (fun x : Fin (m k + n k) → ℝ =>
      (twoSampleScale (m k) (n k) x)⁻¹) := by
    intro k
    unfold twoSampleScale twoSampleVarY twoSampleVarZ twoSampleMeanY twoSampleMeanZ
    fun_prop
  have hjoint := weakConverges_randPairLaw_twoSample PY PZ m n hm hn hratio hlam hYL2 hZL2
    hmeanY hmeanZ hvarY hvarZ hvarYpos hvarZpos hτpos hτ
  rw [← hRdef] at hjoint
  have hscale := tendstoInProbRandomized_twoSampleScale PY PZ m n hm hn hratio hlam hYL2 hZL2
    hmeanY hmeanZ hvarY hvarZ hvarYpos hvarZpos hτpos hτ
  have hA := tendstoInProbRandomized_comp (fun k => Equiv.Perm (Fin (m k + n k)))
    (fun k => twoSampleLaw (m k) (n k) PY PZ) (φ := fun y : ℝ => y⁻¹)
    (continuousAt_inv₀ hτne) hscale
  have hB := tendstoInProbRandomized_zero (fun k => Equiv.Perm (Fin (m k + n k)))
    (fun k => twoSampleLaw (m k) (n k) PY PZ)
  have hmain := randDist_affine_tendstoInProb (G := fun k => Equiv.Perm (Fin (m k + n k)))
    (fun k => twoSampleLaw (m k) (n k) PY PZ)
    (fun k => twoSampleMeanDiff (m k) (n k))
    (fun k x => (twoSampleScale (m k) (n k) x)⁻¹) (fun _ _ => (0 : ℝ)) R
    (a := τ⁻¹) (b := 0) (t := t) hTmeas hAmeas (fun k => measurable_const)
    (fun k g => measurable_perm_smul' _ g) hjoint hA hB hcont
  rw [hmapR] at hmain
  -- The transformed statistic *is* the studentized statistic.
  have hstat : ∀ (k : ℕ) (x : Fin (m k + n k) → ℝ),
      randDist (Equiv.Perm (Fin (m k + n k)))
          (fun y => (twoSampleScale (m k) (n k) y)⁻¹ * twoSampleMeanDiff (m k) (n k) y + 0) x t
        = randDist (Equiv.Perm (Fin (m k + n k))) (studentizedTwoSample (m k) (n k)) x t := by
    intro k x
    have hfun : (fun y : Fin (m k + n k) → ℝ =>
        (twoSampleScale (m k) (n k) y)⁻¹ * twoSampleMeanDiff (m k) (n k) y + 0)
        = studentizedTwoSample (m k) (n k) := by
      refine funext fun y => ?_
      change (twoSampleScale (m k) (n k) y)⁻¹ * twoSampleMeanDiff (m k) (n k) y + 0
        = twoSampleMeanDiff (m k) (n k) y / twoSampleScale (m k) (n k) y
      rw [add_zero, div_eq_inv_mul]
    rw [hfun]
  intro ε hε
  refine (hmain ε hε).congr fun k => ?_
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, hstat k x]

/-- **The unconditional law of the studentized statistic is asymptotically standard
normal.** Together with the previous statement, the randomization distribution and the
true sampling distribution have the *same* limit — the matching that the unstudentized
statistic fails to achieve. -/
theorem weakConverges_studentizedTwoSample (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ μ : ℝ}
    -- USER-INPUT: both sample sizes grow
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: `m/n → λ`, with a nondegenerate limit
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: equal means; the null hypothesis under test
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances, not assumed equal, both nonzero
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ) :
    WeakConverges
      (fun k => (twoSampleLaw (m k) (n k) PY PZ).map (studentizedTwoSample (m k) (n k)))
      (gaussianReal 0 1) := by
  classical
  -- The unconditional variance, and the numerator's limit.
  have hposs : 0 < varY + lam * varZ := by positivity
  set s : ℝ := Real.sqrt (varY + lam * varZ) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.2 hposs
  have hs : s ^ 2 = varY + lam * varZ := Real.sq_sqrt hposs.le
  have hTlaw := weakConverges_twoSampleMeanDiff PY PZ m n hm hn hratio hlam hYL2 hZL2
    hmeanY hmeanZ hvarY hvarZ hvarYpos hvarZpos hspos hs
  have hTmeas : ∀ k, Measurable (twoSampleMeanDiff (m k) (n k)) := by
    intro k; unfold twoSampleMeanDiff; fun_prop
  have hSmeas : ∀ k, Measurable (studentizedTwoSample (m k) (n k)) := by
    intro k
    unfold studentizedTwoSample twoSampleScale twoSampleVarY twoSampleVarZ
      twoSampleMeanY twoSampleMeanZ twoSampleMeanDiff
    fun_prop
  haveI hprobT : ∀ k, IsProbabilityMeasure
      ((twoSampleLaw (m k) (n k) PY PZ).map (twoSampleMeanDiff (m k) (n k))) := fun k =>
    Measure.isProbabilityMeasure_map (hTmeas k).aemeasurable
  -- Dividing the numerator's Gaussian limit by `s` gives the standard normal.
  have hgauss : (gaussianReal 0 (NNReal.mk (s ^ 2) (sq_nonneg s))).map (fun y : ℝ => y / s)
      = gaussianReal 0 1 := by
    have hfun : (fun y : ℝ => y / s) = fun y : ℝ => y * s⁻¹ := by
      funext y; rw [div_eq_mul_inv]
    rw [hfun, gaussianReal_map_mul_const]
    congr 1
    · ring
    · refine NNReal.coe_injective ?_
      simp only [NNReal.coe_mul, NNReal.coe_one, NNReal.coe_mk]
      field_simp
  have hXlaw : WeakConverges
      (fun k => (twoSampleLaw (m k) (n k) PY PZ).map
        (fun x => twoSampleMeanDiff (m k) (n k) x / s)) (gaussianReal 0 1) := by
    have hmapped := hTlaw.map (f := fun y : ℝ => y / s) (by fun_prop) (by fun_prop)
    rw [hgauss] at hmapped
    have heq : ∀ k, ((twoSampleLaw (m k) (n k) PY PZ).map
          (twoSampleMeanDiff (m k) (n k))).map (fun y : ℝ => y / s)
        = (twoSampleLaw (m k) (n k) PY PZ).map
          (fun x => twoSampleMeanDiff (m k) (n k) x / s) := fun k =>
      Measure.map_map (by fun_prop) (hTmeas k)
    simpa only [heq] using hmapped
  -- The scale is consistent, hence so is its reciprocal.
  have hscale := tendstoInProb_twoSampleScale PY PZ m n hm hn hratio hYL2 hZL2 hmeanY hmeanZ
    hvarY hvarZ hs hspos.le
  have hinv := tendstoInProb_comp (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
    (φ := fun y : ℝ => y⁻¹) (continuousAt_inv₀ hspos.ne') hscale
  -- Slutsky: the studentized statistic differs from `T/s` by a vanishing remainder.
  refine AsymptoticStatistics.WeakConverges.slutsky_of_tendstoInMeasure_dist
    (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
    (X := fun k x => twoSampleMeanDiff (m k) (n k) x / s)
    (Y := fun k => studentizedTwoSample (m k) (n k))
    (fun k => ((hTmeas k).div_const s).aemeasurable)
    (fun k => (hSmeas k).aemeasurable) hXlaw ?_
  intro δ hδ
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨M, hMpos, hMev⟩ :=
    exists_tight_bound_of_weakConverges hTlaw (show (0 : ℝ) < ε / 2 by positivity)
  have hinvev := (hinv (δ / M) (by positivity)).eventually
    (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity))
  filter_upwards [hMev, hinvev] with k hk0 hk1
  have hmeasM : MeasurableSet {y : ℝ | M ≤ |y|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hTval : ((twoSampleLaw (m k) (n k) PY PZ).map (twoSampleMeanDiff (m k) (n k))).real
        {y : ℝ | M ≤ |y|}
      = (twoSampleLaw (m k) (n k) PY PZ).real
        {x : Fin (m k + n k) → ℝ | M ≤ |twoSampleMeanDiff (m k) (n k) x|} := by
    rw [Measure.real, Measure.map_apply (hTmeas k) hmeasM]
    rfl
  rw [hTval] at hk0
  have hincl : {x : Fin (m k + n k) → ℝ |
        δ ≤ dist (twoSampleMeanDiff (m k) (n k) x / s) (studentizedTwoSample (m k) (n k) x)}
      ⊆ {x : Fin (m k + n k) → ℝ | M ≤ |twoSampleMeanDiff (m k) (n k) x|}
        ∪ {x : Fin (m k + n k) → ℝ |
            δ / M ≤ |(twoSampleScale (m k) (n k) x)⁻¹ - s⁻¹|} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Real.dist_eq] at hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have heq : twoSampleMeanDiff (m k) (n k) x / s - studentizedTwoSample (m k) (n k) x
        = twoSampleMeanDiff (m k) (n k) x * ((twoSampleScale (m k) (n k) x)⁻¹ - s⁻¹) * (-1) := by
      unfold studentizedTwoSample
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [heq, abs_mul, abs_mul] at hx
    have hlt : |twoSampleMeanDiff (m k) (n k) x|
        * |(twoSampleScale (m k) (n k) x)⁻¹ - s⁻¹| < δ := by
      calc |twoSampleMeanDiff (m k) (n k) x| * |(twoSampleScale (m k) (n k) x)⁻¹ - s⁻¹|
          ≤ M * |(twoSampleScale (m k) (n k) x)⁻¹ - s⁻¹| :=
            mul_le_mul_of_nonneg_right h1.le (abs_nonneg _)
        _ < M * (δ / M) := mul_lt_mul_of_pos_left h2 hMpos
        _ = δ := by field_simp
    simp only [abs_neg, abs_one, mul_one] at hx
    linarith
  have hbound := (measureReal_mono (μ := twoSampleLaw (m k) (n k) PY PZ) hincl
    (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  linarith

/-! ### From the two limits to the rejection probability

The remaining ingredients are combinatorial and measure-theoretic rather than
probabilistic. Several of them exist in `Randomization/ExactLevel`,
`Randomization/Asymptotics` and `Randomization/SignChange` but are `private` there, so they
are re-derived here; each is marked as such. -/

/-- Order statistics against counts: `T^{(j)} ≤ a ↔ j < #{orbit values ≤ a}` (a local copy of
the `ExactLevel` helper). -/
private lemma orderStat_le_iff_card_lt' {d : ℕ} (v : Fin d → ℝ) (j : Fin d) (a : ℝ) :
    orderStat v j ≤ a ↔ j.val < (Finset.univ.filter (fun i => v i ≤ a)).card := by
  have h_card : (Finset.univ.filter (fun i : Fin d => orderStat v i ≤ a)).card =
      (Finset.univ.filter (fun i : Fin d => v i ≤ a)).card :=
    Finset.card_bij' (fun i _ => Tuple.sort v i) (fun i _ => (Tuple.sort v).symm i)
      (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi)
      (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        simp only [orderStat, Equiv.apply_symm_apply]; exact hi)
      (fun i _ => by simp [Equiv.symm_apply_apply])
      (fun i _ => by simp [Equiv.apply_symm_apply])
  rw [show orderStat v j ≤ a ↔ j.val < (Finset.univ.filter (fun i => orderStat v i ≤ a)).card
    from (Tuple.lt_card_le_iff_apply_le_of_monotone (Tuple.monotone_sort v)).symm, h_card]

section Sandwich

variable {G 𝓧 : Type*} [Group G] [Fintype G] [MeasurableSpace 𝓧] [MulAction G 𝓧]

omit [MeasurableSpace 𝓧] in
/-- Counting over the group equals counting over the orbit tuple (a local copy of the
`ExactLevel` helper). -/
private lemma card_filter_orbit' (p : ℝ → Prop) [DecidablePred p] (T : 𝓧 → ℝ) (x : 𝓧) :
    (Finset.univ.filter fun g : G => p (T (g • x))).card
      = (Finset.univ.filter fun i : Fin (Fintype.card G) => p (orbitValues G T x i)).card := by
  refine Finset.card_bij' (fun g _ => Fintype.equivFin G g)
    (fun i _ => (Fintype.equivFin G).symm i) ?_ ?_ ?_ ?_
  · intro g hg
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨Finset.mem_univ _, by simpa only [orbitValues, Equiv.symm_apply_apply] using hg.2⟩
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, by simpa only [orbitValues] using hi.2⟩
  · intro g _; simp
  · intro i _; simp

/-- The randomization distribution is a measurable function of the data (a local copy of the
`Asymptotics` helper). -/
private lemma measurable_randDist' (T : 𝓧 → ℝ) (t : ℝ) (hT : Measurable T)
    (hsmul : ∀ g : G, Measurable (fun x : 𝓧 => g • x)) :
    Measurable (fun x : 𝓧 => randDist G T x t) := by
  classical
  simp only [randDist]
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun g _ => ?_
  have hmset : MeasurableSet {x : 𝓧 | T (g • x) ≤ t} :=
    measurableSet_le (hT.comp (hsmul g)) measurable_const
  have hind : (fun x : 𝓧 => if T (g • x) ≤ t then (1 : ℝ) else 0)
      = Set.indicator {x | T (g • x) ≤ t} 1 := by
    funext x; simp [Set.indicator_apply]
  rw [hind]
  exact measurable_const.indicator hmset

/-- `j ↦ orderStat · ⟨j, h⟩` is measurable (a local copy of the `ExactLevel` helper). -/
private lemma measurable_orderStat_eval' {d : ℕ} (j : ℕ) (h : j < d) :
    Measurable (fun v : Fin d → ℝ => orderStat v ⟨j, h⟩) := by
  classical
  apply measurable_of_Iic
  intro a
  have hset : (fun v : Fin d → ℝ => orderStat v ⟨j, h⟩) ⁻¹' Set.Iic a
      = {v | j < ((Finset.univ : Finset (Fin d)).filter (fun i => v i ≤ a)).card} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    exact orderStat_le_iff_card_lt' v ⟨j, h⟩ a
  rw [hset]
  apply measurableSet_lt measurable_const
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.measurable_sum _ fun i _ =>
    Measurable.ite (measurableSet_le (measurable_pi_apply i) measurable_const)
      measurable_const measurable_const

/-- The randomization test is a measurable function of the data (a local copy of the
`ExactLevel` chain `measurable_randCritValue` → `measurable_randTest`). -/
private lemma measurable_randTest' (T : 𝓧 → ℝ) (α : ℝ) (hT : Measurable T)
    (hsmul : ∀ g : G, Measurable (fun x : 𝓧 => g • x)) :
    Measurable (randTest G T α) := by
  classical
  have hv : Measurable (fun x : 𝓧 => randCritValue G T α x) := by
    unfold randCritValue orbitOrderStat
    by_cases hk : randCritIndex G α - 1 < Fintype.card G
    · simp only [dif_pos hk]
      have hov : Measurable
          (fun x : 𝓧 => (orbitValues G T x : Fin (Fintype.card G) → ℝ)) := by
        rw [measurable_pi_iff]
        exact fun i => hT.comp (hsmul ((Fintype.equivFin G).symm i))
      exact (measurable_orderStat_eval' (randCritIndex G α - 1) hk).comp hov
    · simp only [dif_neg hk]; exact measurable_const
  have hplus : Measurable (fun x : 𝓧 => ((randPlusCount G T α x : ℕ) : ℝ)) := by
    unfold randPlusCount
    simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    refine Finset.measurable_sum _ fun g _ => ?_
    exact Measurable.ite (measurableSet_lt hv (hT.comp (hsmul g)))
      measurable_const measurable_const
  have hzero : Measurable (fun x : 𝓧 => ((randZeroCount G T α x : ℕ) : ℝ)) := by
    unfold randZeroCount
    simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    refine Finset.measurable_sum _ fun g _ => ?_
    exact Measurable.ite (measurableSet_eq_fun (hT.comp (hsmul g)) hv)
      measurable_const measurable_const
  have hgamma : Measurable (fun x : 𝓧 => randGamma G T α x) := by
    unfold randGamma
    exact Measurable.div (measurable_const.sub hplus) hzero
  unfold randTest
  refine Measurable.ite (measurableSet_lt hv hT) measurable_const ?_
  exact Measurable.ite (measurableSet_eq_fun hT hv) hgamma measurable_const

omit [MeasurableSpace 𝓧] in
/-- **The critical value against the randomization distribution.** The critical value is the
`k`-th smallest orbit value with `k = M − ⌊Mα⌋`, so it lies at or below a threshold `z`
exactly when the randomization distribution has already accumulated the fraction `k/M` by
`z`. This is the finite-sample identity that lets a *fixed* threshold control the test. -/
private lemma randCritValue_le_iff_le_randDist (T : 𝓧 → ℝ) {α : ℝ}
    -- USER-INPUT: nominal level strictly between `0` and `1`; the calibration range
    (hα₀ : 0 < α) (hα₁ : α < 1) (x : 𝓧) (z : ℝ) :
    randCritValue G T α x ≤ z ↔
      (randCritIndex G α : ℝ) / (Fintype.card G : ℝ) ≤ randDist G T x z := by
  classical
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  have hcardR : (0 : ℝ) < Fintype.card G := by exact_mod_cast hcard
  have hfl : ⌊(Fintype.card G : ℝ) * α⌋₊ < Fintype.card G :=
    (Nat.floor_lt (mul_nonneg hcardR.le hα₀.le)).2 (mul_lt_of_lt_one_right hcardR hα₁)
  have hk : randCritIndex G α - 1 < Fintype.card G := by unfold randCritIndex; omega
  have hkpos : 1 ≤ randCritIndex G α := by unfold randCritIndex; omega
  have hcount : randDist G T x z
      = (Fintype.card G : ℝ)⁻¹
        * ((Finset.univ.filter fun g : G => T (g • x) ≤ z).card : ℝ) := by
    rw [randDist, Finset.sum_boole]
  have hcf : (Finset.univ.filter fun g : G => T (g • x) ≤ z).card
      = (Finset.univ.filter fun i : Fin (Fintype.card G) =>
          orbitValues G T x i ≤ z).card := card_filter_orbit' (fun r => r ≤ z) T x
  have hiff : ∀ a b : ℝ, (a / (Fintype.card G : ℝ) ≤ (Fintype.card G : ℝ)⁻¹ * b) ↔ a ≤ b := by
    intro a b
    rw [div_eq_inv_mul]
    exact ⟨fun h => le_of_mul_le_mul_left h (by positivity),
      fun h => mul_le_mul_of_nonneg_left h (by positivity)⟩
  rw [randCritValue, orbitOrderStat, dif_pos hk, hcount, hiff,
    orderStat_le_iff_card_lt' (orbitValues G T x) ⟨randCritIndex G α - 1, hk⟩ z, ← hcf,
    Nat.cast_le]
  have hval : ((⟨randCritIndex G α - 1, hk⟩ : Fin (Fintype.card G)) : ℕ)
      = randCritIndex G α - 1 := rfl
  rw [hval]
  omega

/-- **Two-sided sandwich for the power of a randomization test at a fixed threshold.**
At any threshold `z`, the test rejects on `{z < T} ∩ {k/M ≤ R̂(z)}` and accepts off
`{z < T} ∪ {k/M ≤ R̂(z)}`, by `randCritValue_le_iff_le_randDist`. The two events are the
ones whose limits the asymptotic theory supplies: a tail probability of the statistic and a
deviation probability of the randomization distribution. -/
private lemma powerAgainst_randTest_sandwich (P : Measure 𝓧) [IsProbabilityMeasure P]
    (T : 𝓧 → ℝ)
    -- USER-INPUT: the statistic is measurable; the action is measurable (data regularity)
    (hT : Measurable T) (hsmul : ∀ g : G, Measurable (fun x : 𝓧 => g • x)) {α : ℝ}
    -- USER-INPUT: nominal level strictly between `0` and `1`; the calibration range
    (hα₀ : 0 < α) (hα₁ : α < 1) (z : ℝ) :
    P.real {x | z < T x}
        - P.real {x | randDist G T x z < (randCritIndex G α : ℝ) / (Fintype.card G : ℝ)}
        ≤ powerAgainst P (randTest G T α)
      ∧ powerAgainst P (randTest G T α)
        ≤ P.real {x | z < T x}
          + P.real {x | (randCritIndex G α : ℝ) / (Fintype.card G : ℝ) ≤ randDist G T x z} := by
  classical
  set q : ℝ := (randCritIndex G α : ℝ) / (Fintype.card G : ℝ) with hqdef
  set A : Set 𝓧 := {x | z < T x} with hAdef
  set B : Set 𝓧 := {x | q ≤ randDist G T x z} with hBdef
  set Bc : Set 𝓧 := {x | randDist G T x z < q} with hBcdef
  have hrdmeas : Measurable (fun x : 𝓧 => randDist G T x z) := measurable_randDist' T z hT hsmul
  have hAmeas : MeasurableSet A := measurableSet_lt measurable_const hT
  have hBmeas : MeasurableSet B := measurableSet_le measurable_const hrdmeas
  have hBcmeas : MeasurableSet Bc := measurableSet_lt hrdmeas measurable_const
  have hABmeas : MeasurableSet (A ∪ B) := hAmeas.union hBmeas
  have hAB'meas : MeasurableSet (A ∩ B) := hAmeas.inter hBmeas
  -- the test is a bounded measurable critical function
  have hφmeas : Measurable (randTest G T α) := measurable_randTest' T α hT hsmul
  have hφIcc : ∀ x : 𝓧, randTest G T α x ∈ Set.Icc (0 : ℝ) 1 := fun x =>
    randTest_mem_Icc (G := G) T hα₀ hα₁ x
  have hφint : Integrable (randTest G T α) P :=
    (integrable_const (1 : ℝ)).mono' hφmeas.aestronglyMeasurable
      (ae_of_all P fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hφIcc x).1]; exact (hφIcc x).2)
  -- off `A ∪ B` the test accepts; on `A ∩ B` it rejects
  have hzero : ∀ x : 𝓧, x ∉ A ∪ B → randTest G T α x = 0 := by
    intro x hx
    rw [Set.mem_union, hAdef, hBdef, Set.mem_setOf_eq, Set.mem_setOf_eq, not_or, not_lt,
      not_le] at hx
    obtain ⟨hTx, hrd⟩ := hx
    have hcz : ¬ (randCritValue G T α x ≤ z) := by
      rw [randCritValue_le_iff_le_randDist T hα₀ hα₁ x z, ← hqdef]
      exact not_le.2 hrd
    have hlt : T x < randCritValue G T α x := lt_of_le_of_lt hTx (not_le.1 hcz)
    unfold randTest
    rw [if_neg (not_lt.2 hlt.le), if_neg (ne_of_lt hlt)]
  have hone : ∀ x : 𝓧, x ∈ A ∩ B → randTest G T α x = 1 := by
    intro x hx
    obtain ⟨hxA, hxB⟩ := hx
    rw [hAdef, Set.mem_setOf_eq] at hxA
    rw [hBdef, Set.mem_setOf_eq] at hxB
    have hcz : randCritValue G T α x ≤ z := by
      rw [randCritValue_le_iff_le_randDist T hα₀ hα₁ x z, ← hqdef]; exact hxB
    unfold randTest
    rw [if_pos (lt_of_le_of_lt hcz hxA)]
  refine ⟨?_, ?_⟩
  · -- lower bound
    have hle : ∀ x : 𝓧, Set.indicator (A ∩ B) (fun _ => (1 : ℝ)) x ≤ randTest G T α x := by
      intro x
      by_cases hx : x ∈ A ∩ B
      · rw [Set.indicator_of_mem hx, hone x hx]
      · rw [Set.indicator_of_notMem hx]; exact (hφIcc x).1
    have hintAB : ∫ x, Set.indicator (A ∩ B) (fun _ => (1 : ℝ)) x ∂P = P.real (A ∩ B) := by
      rw [integral_indicator hAB'meas, setIntegral_const, smul_eq_mul, mul_one]
    have hstep : P.real (A ∩ B) ≤ powerAgainst P (randTest G T α) := by
      have h := integral_mono ((integrable_const (1 : ℝ)).indicator hAB'meas) hφint hle
      rwa [hintAB] at h
    have hsub : A ⊆ (A ∩ B) ∪ Bc := by
      intro x hx
      by_cases hxB : x ∈ B
      · exact Set.mem_union_left _ ⟨hx, hxB⟩
      · refine Set.mem_union_right _ ?_
        rw [hBdef, Set.mem_setOf_eq, not_le] at hxB
        exact hxB
    have hsplit : P.real A ≤ P.real (A ∩ B) + P.real Bc :=
      (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    linarith
  · -- upper bound
    have hle : ∀ x : 𝓧, randTest G T α x ≤ Set.indicator (A ∪ B) (fun _ => (1 : ℝ)) x := by
      intro x
      by_cases hx : x ∈ A ∪ B
      · rw [Set.indicator_of_mem hx]; exact (hφIcc x).2
      · rw [Set.indicator_of_notMem hx, hzero x hx]
    have hintAB : ∫ x, Set.indicator (A ∪ B) (fun _ => (1 : ℝ)) x ∂P = P.real (A ∪ B) := by
      rw [integral_indicator hABmeas, setIntegral_const, smul_eq_mul, mul_one]
    have hstep : powerAgainst P (randTest G T α) ≤ P.real (A ∪ B) := by
      have h := integral_mono hφint ((integrable_const (1 : ℝ)).indicator hABmeas) hle
      rwa [hintAB] at h
    exact hstep.trans (measureReal_union_le _ _)

end Sandwich

/-- The critical fraction `k/M = 1 − ⌊Mα⌋/M` converges to `1 − α` along any array whose
group cardinalities tend to infinity. -/
private lemma tendsto_randCritIndex_div {G : ℕ → Type*} [∀ k, Group (G k)] [∀ k, Fintype (G k)]
    {α : ℝ}
    -- USER-INPUT: nominal level strictly between `0` and `1`; the calibration range
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: the groups grow
    (hcard : Tendsto (fun k => (Fintype.card (G k) : ℝ)) atTop atTop) :
    Tendsto (fun k => (randCritIndex (G k) α : ℝ) / (Fintype.card (G k) : ℝ)) atTop
      (𝓝 (1 - α)) := by
  have hbound : ∀ k, |(randCritIndex (G k) α : ℝ) / (Fintype.card (G k) : ℝ) - (1 - α)|
      ≤ (Fintype.card (G k) : ℝ)⁻¹ := by
    intro k
    have hcardR : (0 : ℝ) < Fintype.card (G k) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (G k))
    have hfl : ⌊(Fintype.card (G k) : ℝ) * α⌋₊ ≤ Fintype.card (G k) :=
      le_of_lt ((Nat.floor_lt (mul_nonneg hcardR.le hα₀.le)).2
        (mul_lt_of_lt_one_right hcardR hα₁))
    have hcast : ((randCritIndex (G k) α : ℕ) : ℝ)
        = (Fintype.card (G k) : ℝ) - (⌊(Fintype.card (G k) : ℝ) * α⌋₊ : ℝ) := by
      unfold randCritIndex; rw [Nat.cast_sub hfl]
    have h1 : ((⌊(Fintype.card (G k) : ℝ) * α⌋₊ : ℝ)) ≤ (Fintype.card (G k) : ℝ) * α :=
      Nat.floor_le (mul_nonneg hcardR.le hα₀.le)
    have h2 : (Fintype.card (G k) : ℝ) * α < (⌊(Fintype.card (G k) : ℝ) * α⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    rw [hcast]
    have hkey : ((Fintype.card (G k) : ℝ) - (⌊(Fintype.card (G k) : ℝ) * α⌋₊ : ℝ))
          / (Fintype.card (G k) : ℝ) - (1 - α)
        = ((Fintype.card (G k) : ℝ) * α - (⌊(Fintype.card (G k) : ℝ) * α⌋₊ : ℝ))
          / (Fintype.card (G k) : ℝ) := by
      field_simp
      ring
    rw [hkey, abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤
        (Fintype.card (G k) : ℝ) * α - (⌊(Fintype.card (G k) : ℝ) * α⌋₊ : ℝ)),
      abs_of_nonneg hcardR.le, div_le_iff₀ hcardR, inv_mul_cancel₀ hcardR.ne']
    linarith
  have hlim : Tendsto
      (fun k => |(randCritIndex (G k) α : ℝ) / (Fintype.card (G k) : ℝ) - (1 - α)|) atTop
      (𝓝 0) := squeeze_zero (fun k => abs_nonneg _) hbound hcard.inv_tendsto_atTop
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Real.dist_eq] using hlim

/-- **Portmanteau, `Measure.real` form** on `ℝ` (a local copy of the `Asymptotics` helper). -/
private lemma tendsto_measureReal_of_weakConverges {νs : ℕ → Measure ℝ} {ν : Measure ℝ}
    [∀ k, IsProbabilityMeasure (νs k)] [IsProbabilityMeasure ν]
    (h : WeakConverges νs ν) {s : Set ℝ} (hs : ν (frontier s) = 0) :
    Tendsto (fun k => (νs k).real s) atTop (𝓝 (ν.real s)) := by
  let pn : ℕ → ProbabilityMeasure ℝ := fun k => ⟨νs k, inferInstance⟩
  let pμ : ProbabilityMeasure ℝ := ⟨ν, inferInstance⟩
  have hpm : Tendsto pn atTop (𝓝 pμ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f; simpa [pn, pμ] using h f
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hpm
    (E := s) (by simpa [pμ] using hs)
  have h2 := (ENNReal.tendsto_toReal (measure_ne_top ν s)).comp key
  simpa [Measure.real, pn, pμ] using! h2

/-- The c.d.f. of a nondegenerate centred Gaussian is strictly increasing (a local copy of
the `SignChange` helper). -/
private lemma strictMono_cdf_gaussianReal' {v : ℝ≥0} (hv : v ≠ 0) :
    StrictMono (cdf (gaussianReal 0 v)) := by
  intro y z hyz
  rw [cdf_eq_real, cdf_eq_real]
  have hpos : 0 < gaussianReal 0 v (Set.Ioc y z) := by
    rw [pos_iff_ne_zero]; intro h0
    have hvol := (gaussianReal_absolutelyContinuous' 0 hv) h0
    rw [Real.volume_Ioc] at hvol
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne' hvol
  have hdisj : gaussianReal 0 v (Set.Iic z)
      = gaussianReal 0 v (Set.Iic y) + gaussianReal 0 v (Set.Ioc y z) := by
    rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic hyz.le]
  rw [measureReal_def, measureReal_def, hdisj,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hp2 : 0 < (gaussianReal 0 v (Set.Ioc y z)).toReal :=
    ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  linarith

/-- Every level in `(0,1)` is attained by the c.d.f. of an atomless law (a local copy of the
`SignChange` helper). -/
private lemma exists_cdf_eq' (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : ∃ q, cdf ν q = p := by
  have hcont : Continuous (cdf ν) :=
    continuous_iff_continuousAt.mpr (fun x => continuousAt_cdf_of_noAtoms' ν x)
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot ν).eventually (eventually_lt_nhds hp0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop ν).eventually (eventually_gt_nhds hp1)).exists
  have hab : min a b ≤ max a b := min_le_max
  have hca' : cdf ν (min a b) < p := lt_of_le_of_lt (monotone_cdf (μ := ν) (min_le_left a b)) ha
  have hcb' : p < cdf ν (max a b) := lt_of_lt_of_le hb (monotone_cdf (μ := ν) (le_max_right a b))
  obtain ⟨q, _, hq⟩ := intermediate_value_Icc hab hcont.continuousOn ⟨hca'.le, hcb'.le⟩
  exact ⟨q, hq⟩

/-- **The studentized permutation test is pointwise consistent in level.** Its rejection
probability tends to the nominal level,
$$ E_{P_Y^m \times P_Z^n}\bigl[\phi_{m,n}\bigr] \;\longrightarrow\; \alpha , $$
for testing equality of means, with no equal-variance and no balanced-sample-size
assumption. (If the two populations coincide, the randomization hypothesis holds and the
test is exactly level `α` at every finite sample size.) -/
theorem studentizedPermTest_asymptotic_level (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ μ α : ℝ}
    -- USER-INPUT: both sample sizes grow
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: `m/n → λ`, with a nondegenerate limit
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: equal means; the null hypothesis under test
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances, not assumed equal, both nonzero
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ)
    -- USER-INPUT: nominal level strictly between `0` and `1`; the calibration range
    (hα₀ : 0 < α) (hα₁ : α < 1) :
    Tendsto (fun k => powerAgainst (twoSampleLaw (m k) (n k) PY PZ)
        (randTest (Equiv.Perm (Fin (m k + n k))) (studentizedTwoSample (m k) (n k)) α))
      atTop (𝓝 α) := by
  -- Route (re-derived this session, wave 5). The critical value is *not* passed through
  -- `randQuantile_tendstoInProb`: the test's critical index `k = M − ⌊Mα⌋` gives the
  -- randomization quantile at the *moving* level `k/M`, and `randQuantile_tendstoInProb` is
  -- stated at the fixed level `1 − α`. The finite-sample identity
  -- `randCritValue_le_iff_le_randDist` replaces it, and lets a *fixed* threshold `z` control
  -- the test: the test rejects on `{z < T̃} ∩ {k/M ≤ R̂(z)}` and accepts off
  -- `{z < T̃} ∪ {k/M ≤ R̂(z)}` (`powerAgainst_randTest_sandwich`). Since `k/M → 1 − α`, the
  -- randomization-distribution event has probability tending to `0` for `Φ(z) < 1 − α` and to
  -- `1` for `Φ(z) > 1 − α` (by `randDist_studentized_tendstoInProb`), while the tail event has
  -- probability tending to `1 − Φ(z)` (portmanteau on `Ioi z`, whose frontier is a
  -- `N(0,1)`-null point, applied to `weakConverges_studentizedTwoSample`). Bracketing the
  -- `(1−α)`-quantile of `Φ` by two continuity/strict-monotonicity thresholds `z₁ < q₀ < z₂`
  -- squeezes the power between `1 − Φ(z₂)` and `1 − Φ(z₁)`, both within `ε` of `α`.
  classical
  have hSmeas : ∀ k, Measurable (studentizedTwoSample (m k) (n k)) := by
    intro k
    unfold studentizedTwoSample twoSampleScale twoSampleVarY twoSampleVarZ
      twoSampleMeanY twoSampleMeanZ twoSampleMeanDiff
    fun_prop
  have hsmul : ∀ (k : ℕ) (g : Equiv.Perm (Fin (m k + n k))),
      Measurable (fun x : Fin (m k + n k) → ℝ => g • x) := fun _ g => measurable_perm_smul' _ g
  haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  -- (i) the studentized randomization distribution converges in probability to `Φ`
  have hrd : ∀ z : ℝ, TendstoInProbTriangular (fun k => twoSampleLaw (m k) (n k) PY PZ)
      (fun k x => randDist (Equiv.Perm (Fin (m k + n k)))
        (studentizedTwoSample (m k) (n k)) x z) (cdf (gaussianReal 0 1) z) := fun z =>
    randDist_studentized_tendstoInProb PY PZ m n hm hn hratio hlam hYL2 hZL2 hmeanY hmeanZ
      hvarY hvarZ hvarYpos hvarZpos z
  -- (ii) the unconditional law converges weakly to `N(0,1)`
  have hlaw := weakConverges_studentizedTwoSample PY PZ m n hm hn hratio hlam hYL2 hZL2
    hmeanY hmeanZ hvarY hvarZ hvarYpos hvarZpos
  haveI hprob : ∀ k, IsProbabilityMeasure ((twoSampleLaw (m k) (n k) PY PZ).map
      (studentizedTwoSample (m k) (n k))) := fun k =>
    Measure.isProbabilityMeasure_map (hSmeas k).aemeasurable
  -- (iii) the critical fraction `k/M` converges to `1 − α` (`M = N!  → ∞`)
  have hcardNat : Tendsto (fun k => Fintype.card (Equiv.Perm (Fin (m k + n k)))) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) hm
    calc m k ≤ m k + n k := Nat.le_add_right _ _
      _ ≤ Nat.factorial (m k + n k) := Nat.self_le_factorial _
      _ = Fintype.card (Equiv.Perm (Fin (m k + n k))) := by
          rw [Fintype.card_perm, Fintype.card_fin]
  have hq := tendsto_randCritIndex_div (G := fun k => Equiv.Perm (Fin (m k + n k))) hα₀ hα₁
    (tendsto_natCast_atTop_atTop.comp hcardNat)
  -- (iv) the tail probabilities of the statistic
  have htail : ∀ z : ℝ, Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x | z < studentizedTwoSample (m k) (n k) x}) atTop
      (𝓝 (1 - cdf (gaussianReal 0 1) z)) := by
    intro z
    have hfr : (gaussianReal 0 1) (frontier (Set.Ioi z)) = 0 := by
      rw [frontier_Ioi]; exact measure_singleton z
    have h1 := tendsto_measureReal_of_weakConverges hlaw hfr
    have hval : (gaussianReal 0 1).real (Set.Ioi z) = 1 - cdf (gaussianReal 0 1) z := by
      have hc := measureReal_add_measureReal_compl (μ := gaussianReal 0 1) (s := Set.Iic z)
        measurableSet_Iic
      rw [probReal_univ] at hc
      rw [cdf_eq_real, ← Set.compl_Iic]
      linarith
    rw [hval] at h1
    refine h1.congr fun k => ?_
    rw [measureReal_def, measureReal_def, Measure.map_apply (hSmeas k) measurableSet_Ioi]
    rfl
  -- (v) below the quantile the randomization event is asymptotically impossible
  have hB : ∀ z : ℝ, cdf (gaussianReal 0 1) z < 1 - α →
      Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
        {x | (randCritIndex (Equiv.Perm (Fin (m k + n k))) α : ℝ)
              / (Fintype.card (Equiv.Perm (Fin (m k + n k))) : ℝ)
            ≤ randDist (Equiv.Perm (Fin (m k + n k)))
              (studentizedTwoSample (m k) (n k)) x z}) atTop (𝓝 0) := by
    intro z hz
    have hδpos : 0 < (1 - α - cdf (gaussianReal 0 1) z) / 2 := by linarith
    have hev := hq.eventually (eventually_gt_nhds
      (show cdf (gaussianReal 0 1) z + (1 - α - cdf (gaussianReal 0 1) z) / 2 < 1 - α by
        linarith))
    refine squeeze_zero' (Eventually.of_forall fun k => measureReal_nonneg) ?_
      (hrd z _ hδpos)
    filter_upwards [hev] with k hk
    refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [le_abs]
    left
    linarith
  -- (vi) above the quantile it is asymptotically certain
  have hBc : ∀ z : ℝ, 1 - α < cdf (gaussianReal 0 1) z →
      Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
        {x | randDist (Equiv.Perm (Fin (m k + n k)))
              (studentizedTwoSample (m k) (n k)) x z
            < (randCritIndex (Equiv.Perm (Fin (m k + n k))) α : ℝ)
              / (Fintype.card (Equiv.Perm (Fin (m k + n k))) : ℝ)}) atTop (𝓝 0) := by
    intro z hz
    have hδpos : 0 < (cdf (gaussianReal 0 1) z - (1 - α)) / 2 := by linarith
    have hev := hq.eventually (eventually_lt_nhds
      (show (1 : ℝ) - α < cdf (gaussianReal 0 1) z - (cdf (gaussianReal 0 1) z - (1 - α)) / 2 by
        linarith))
    refine squeeze_zero' (Eventually.of_forall fun k => measureReal_nonneg) ?_
      (hrd z _ hδpos)
    filter_upwards [hev] with k hk
    refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [le_abs]
    right
    linarith
  -- (vii) bracket the `1 − α` quantile of `Φ` and squeeze
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨q₀, hq₀⟩ := exists_cdf_eq' (gaussianReal 0 1) (show (0 : ℝ) < 1 - α by linarith)
    (show (1 : ℝ) - α < 1 by linarith)
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.continuousAt_iff.mp
    (continuousAt_cdf_of_noAtoms' (gaussianReal 0 1) q₀) (ε / 2) (by positivity)
  have hSM : StrictMono (cdf (gaussianReal 0 1)) := strictMono_cdf_gaussianReal' one_ne_zero
  have hd₁ : |cdf (gaussianReal 0 1) (q₀ - ρ / 2) - (1 - α)| < ε / 2 := by
    have hdist := hρ (show dist (q₀ - ρ / 2) q₀ < ρ by
      rw [Real.dist_eq]; rw [show q₀ - ρ / 2 - q₀ = -(ρ / 2) by ring, abs_neg,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ρ / 2)]; linarith)
    rwa [Real.dist_eq, hq₀] at hdist
  have hd₂ : |cdf (gaussianReal 0 1) (q₀ + ρ / 2) - (1 - α)| < ε / 2 := by
    have hdist := hρ (show dist (q₀ + ρ / 2) q₀ < ρ by
      rw [Real.dist_eq]; rw [show q₀ + ρ / 2 - q₀ = ρ / 2 by ring,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ρ / 2)]; linarith)
    rwa [Real.dist_eq, hq₀] at hdist
  have hlt₁ : cdf (gaussianReal 0 1) (q₀ - ρ / 2) < 1 - α := by
    rw [← hq₀]; exact hSM (by linarith)
  have hlt₂ : (1 : ℝ) - α < cdf (gaussianReal 0 1) (q₀ + ρ / 2) := by
    rw [← hq₀]; exact hSM (by linarith)
  -- the two eventual bounds
  have hupev := ((htail (q₀ - ρ / 2)).add (hB _ hlt₁)).eventually (eventually_lt_nhds
    (show 1 - cdf (gaussianReal 0 1) (q₀ - ρ / 2) + 0
        < 1 - cdf (gaussianReal 0 1) (q₀ - ρ / 2) + ε / 2 by linarith))
  have hloev := ((htail (q₀ + ρ / 2)).sub (hBc _ hlt₂)).eventually (eventually_gt_nhds
    (show 1 - cdf (gaussianReal 0 1) (q₀ + ρ / 2) - ε / 2
        < 1 - cdf (gaussianReal 0 1) (q₀ + ρ / 2) - 0 by linarith))
  refine eventually_atTop.1 ?_
  filter_upwards [hupev, hloev] with k hkup hklo
  obtain ⟨hlo, hup⟩ := powerAgainst_randTest_sandwich (twoSampleLaw (m k) (n k) PY PZ)
    (studentizedTwoSample (m k) (n k)) (hSmeas k) (hsmul k) hα₀ hα₁ (q₀ - ρ / 2)
  obtain ⟨hlo', _⟩ := powerAgainst_randTest_sandwich (twoSampleLaw (m k) (n k) PY PZ)
    (studentizedTwoSample (m k) (n k)) (hSmeas k) (hsmul k) hα₀ hα₁ (q₀ + ρ / 2)
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at hd₁ hd₂
  constructor
  · linarith
  · linarith

end StatLean.HypothesisTesting
