module
public import StatLean.HypothesisTesting.Randomization.Asymptotics
public import StatLean.HypothesisTesting.Randomization.PairCLT
public import StatLean.HypothesisTesting.ForMathlib.LindebergCLT
public import StatLean.HypothesisTesting.ForMathlib.HypergeometricMoments
public import StatLean.HypothesisTesting.ForMathlib.CombinatorialCLT
public import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Probability.Independence.CharacteristicFunction

@[expose] public section

/-!
# The two-sample permutation central limit theorem

Two independent samples $Y_1, \dots, Y_m \sim P_Y$ and $Z_1, \dots, Z_n \sim P_Z$ are
pooled into $X = (Y_1, \dots, Y_m, Z_1, \dots, Z_n)$ of length $N = m + n$, and the
permutation group of $\{1, \dots, N\}$ acts by relabelling coordinates. The statistic is
the scaled difference of sample means
$$ T_{m,n} = m^{1/2}\bigl(\bar Y_m - \bar Z_n\bigr) . $$

Assume $m/n \to \lambda \in (0, \infty)$, finite nonzero variances, and equal means
$\mu(P_Y) = \mu(P_Z)$. The **permutation** limit is
$$ \bigl(T_{m,n}(\pi X),\, T_{m,n}(\pi' X)\bigr) \;\xrightarrow{d}\;
   N(0, \tau^2) \otimes N(0, \tau^2), \qquad
   \tau^2 = \lambda\,\sigma^2(P_Y) + \sigma^2(P_Z) , $$
for two independent uniform random permutations $\pi, \pi'$, so the randomization
distribution satisfies $\hat R_{m,n}(t) \xrightarrow{P} \Phi(t/\tau)$.

The **unconditional** limit is a different Gaussian,
$$ T_{m,n} \;\xrightarrow{d}\; N\bigl(0, \sigma^2(P_Y) + \lambda\,\sigma^2(P_Z)\bigr) , $$
with the roles of $\lambda$ and the two variances exchanged. The two variances coincide
exactly when $\lambda = 1$ or $\sigma^2(P_Y) = \sigma^2(P_Z)$ — which is precisely why the
unstudentized permutation test can fail to be asymptotically level $\alpha$ for testing
equality of *means* when the variances differ and the sample sizes are unbalanced, and why
the studentized version of the companion file is needed.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 17 (Permutation and
Randomization Tests), §17.3 (Two-Sample Permutation Tests), Theorem 17.3.1 (the two-sample
permutation central limit theorem). (`TSH4 §17.3 Thm 17.3.1`.)

**Proof formalization notes.**
* *The permutation action.* `Equiv.Perm (Fin N)` acts on `Fin N → ℝ` through Mathlib's
  `arrowAction`, declared here as a scoped instance since Mathlib deliberately leaves it a
  plain definition. This gives `(σ • x) i = x (σ⁻¹ i)`, whereas the classical display
  writes `(σ • x) i = x (σ i)`. The two conventions differ by inversion, a bijection of the
  group, so every group-averaged object — `randDist`, `randTest`, `randPValue`,
  `randPairLaw` — is literally unchanged; only the labelling of individual summands moves.
* *The pooled law.* `twoSampleLaw` is the product measure on `Fin (m + n) → ℝ` whose first
  `m` coordinates are `P_Y` and whose last `n` are `P_Z`, assembled with `Fin.addCases`.
  Independence within and across the two samples is exactly the product structure.
* *Degenerate corners.* `twoSampleMeanDiff` uses `(m : ℝ)⁻¹` and `(n : ℝ)⁻¹`, which are
  `0` when the sample is empty; the statistic is therefore total, with junk value at
  `m = 0` or `n = 0`. The theorems send both sample sizes to infinity, so those corners are
  never reached.
* *Both scales are carried explicitly.* `τ` is the permutation scale and `s` the
  unconditional one, each introduced with its defining equation (`τ² = λσ²_Y + σ²_Z`,
  `s² = σ²_Y + λσ²_Z`) and a positivity hypothesis. Writing them as separate parameters
  keeps the asymmetry — the whole content of the comparison — visible in the signatures.
* *Route to the limit.* Conditionally on the permutation weights, the statistic is a
  weighted sum of independent terms; the Cramér–Wold device reduces the bivariate claim to
  a scalar one, and the weighted i.i.d. central limit theorem of the sibling brick
  `StatLean.HypothesisTesting.ForMathlib.LindebergCLT` supplies the scalar limit. The
  weights are indicators of sampling **without replacement**, so their moments — the
  variance of the weight average and the covariance across two independent permutations —
  come from the sibling brick
  `StatLean.HypothesisTesting.ForMathlib.HypergeometricMoments`.
* The statement is deliberately given in the `WeakConverges`-to-a-product form, so that it
  plugs directly into the joint hypothesis of
  `randDist_tendstoInProb_cdf` in `Randomization/Asymptotics`.

**Bibliographic comments.** The permutation test for the two-sample problem is due to
R. A. Fisher (*The Design of Experiments*, Oliver & Boyd, Edinburgh, 1935) and
E. J. G. Pitman ("Significance tests which may be applied to samples from any
populations," *J. R. Statist. Soc. Suppl.* **4** (1937), 119–130); exactness under the
group formulation is E. L. Lehmann and C. Stein ("On the theory of some non-parametric
hypotheses," *Ann. Math. Statist.* **20** (1949), 28–45), and the sampled-group variant is
M. Dwass ("Modified randomization tests for nonparametric hypotheses," *Ann. Math.
Statist.* **28** (1957), 181–187). The large-sample theory of permutation statistics is
W. Hoeffding ("The large-sample power of tests based on permutations of observations,"
*Ann. Math. Statist.* **23** (1952), 169–192). That the unstudentized two-sample
permutation test can fail asymptotically under unequal variances was established by
J. P. Romano ("On the behavior of randomization tests without a group invariance
assumption," *J. Amer. Statist. Assoc.* **85** (1990), 686–692; see also "Bootstrap and
randomization tests of some nonparametric hypotheses," *Ann. Statist.* **17** (1989),
141–159), with the general theory in E. Chung and J. P. Romano ("Exact and asymptotically
robust permutation tests," *Ann. Statist.* **41** (2013), 484–507).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)

/-! ### The permutation group acting on pooled data -/

/-- Coordinate relabelling: `Equiv.Perm (Fin N)` acts on data vectors `Fin N → ℝ` by
`(σ • x) i = x (σ⁻¹ i)`. Mathlib supplies this action as a definition (`arrowAction`)
rather than an instance; it is registered here, scoped to this area. -/
scoped instance permCoordAction (N : ℕ) : MulAction (Equiv.Perm (Fin N)) (Fin N → ℝ) :=
  arrowAction

/-- The permutation action, written out. -/
lemma perm_smul_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ) (i : Fin N) :
    (σ • x) i = x (σ⁻¹ i) := rfl

/-! ### The two-sample model and statistic -/

/-- The **pooled two-sample law** on `Fin (m + n) → ℝ`: the first `m` coordinates are
i.i.d. `P_Y`, the last `n` are i.i.d. `P_Z`, and the two blocks are independent. -/
noncomputable def twoSampleLaw (m n : ℕ) (PY PZ : Measure ℝ) :
    Measure (Fin (m + n) → ℝ) :=
  Measure.pi (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ))

/-- The **scaled difference of sample means** `T_{m,n} = √m (Ȳ_m − Z̄_n)`, read off the
pooled data vector. Total: an empty sample contributes mean `0` (junk), a corner the
theorems never reach. -/
noncomputable def twoSampleMeanDiff (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  Real.sqrt (m : ℝ) * ((m : ℝ)⁻¹ * ∑ i : Fin m, x (Fin.castAdd n i)
    - (n : ℝ)⁻¹ * ∑ j : Fin n, x (Fin.natAdd m j))

/-! ### Measurability and probability-measure bricks -/

/-- The difference-of-means statistic is measurable: a fixed linear combination of coordinate
projections. -/
private lemma measurable_twoSampleMeanDiff (m n : ℕ) :
    Measurable (twoSampleMeanDiff m n) := by
  unfold twoSampleMeanDiff
  fun_prop

/-- The permutation action `σ • x = x ∘ σ⁻¹` is measurable in `x` (coordinate relabelling). -/
private lemma measurable_perm_smul (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    Measurable (fun x : Fin N → ℝ => σ • x) := by
  have hfun : (fun x : Fin N → ℝ => σ • x) = fun x i => x (σ⁻¹ i) := by
    ext x i; exact perm_smul_apply σ x i
  rw [hfun]
  exact measurable_pi_lambda _ fun i => measurable_pi_apply _

/-- The pooled two-sample law is a probability measure. -/
instance isProbabilityMeasure_twoSampleLaw (m n : ℕ) (PY PZ : Measure ℝ)
    [IsProbabilityMeasure PY] [IsProbabilityMeasure PZ] :
    IsProbabilityMeasure (twoSampleLaw m n PY PZ) := by
  unfold twoSampleLaw
  haveI : ∀ i, IsProbabilityMeasure
      (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i) := by
    intro i
    refine Fin.addCases (m := m) (n := n)
      (motive := fun i => IsProbabilityMeasure
        (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i))
      (fun j => ?_) (fun j => ?_) i
    · first
        | infer_instance
        | · simp only [Fin.addCases_left]; infer_instance
    · first
        | infer_instance
        | · simp only [Fin.addCases_right]; infer_instance
  infer_instance

/-! ### The permuted statistic as a block sum

Under a uniform permutation the two-sample statistic is *exactly* a fixed positive multiple
of the sum of the **centred** pooled data over a block of `m` positions — that is, of a
simple random sample of size `m` drawn without replacement from the pooled population. This
is what puts the whole two-sample chain in the scope of the combinatorial central limit
theorem `ForMathlib/CombinatorialCLT.tendsto_perm_cdf_blockSum`: the sample means of the two
blocks are not independent, but their difference is an affine function of one block sum, and
the pooled total drops out because it is permutation invariant. -/

/-- The **centred pooled data** `d(x)_l = x_l − x̄`, where `x̄` is the mean of all `N = m + n`
pooled observations. This is the finite population from which a permutation samples. -/
private noncomputable def pooledCentred (m n : ℕ) (x : Fin (m + n) → ℝ) : Fin (m + n) → ℝ :=
  fun l => x l - ((m + n : ℕ) : ℝ)⁻¹ * ∑ l', x l'

/-- The centred pooled data sums to zero — the hypothesis `hcent` of the combinatorial
central limit theorem. -/
private lemma sum_pooledCentred (m n : ℕ) (hmn : 0 < m + n) (x : Fin (m + n) → ℝ) :
    ∑ l, pooledCentred m n x l = 0 := by
  have hN : ((m + n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hmn.ne'
  simp only [pooledCentred]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hN, one_mul, sub_self]

/-- **The permuted two-sample statistic is a multiple of a permuted block sum.** With
`N = m + n` and `d = pooledCentred m n x`,
$$ T_{m,n}(\sigma \cdot x) \;=\; \frac{\sqrt m\, N}{m n} \sum_{i<m} d\bigl(\sigma^{-1}(i)\bigr) .$$
The pooled total cancels: the coefficient of `x̄` in the first block is `√m N/(mn) \cdot m`
and in the second `√m/n \cdot N`, and these agree. -/
private lemma twoSampleMeanDiff_smul_eq_blockSum (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (x : Fin (m + n) → ℝ) (σ : Equiv.Perm (Fin (m + n))) :
    twoSampleMeanDiff m n (σ • x)
      = Real.sqrt m * ((m + n : ℕ) : ℝ) / ((m : ℝ) * n)
        * ∑ i : Fin m, pooledCentred m n x (σ⁻¹ (Fin.castAdd n i)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNcast : ((m + n : ℕ) : ℝ) = (m : ℝ) + n := by push_cast; ring
  -- The permutation preserves the pooled total, so the second block sum is the complement.
  have htot : (∑ i : Fin m, x (σ⁻¹ (Fin.castAdd n i)))
      + (∑ j : Fin n, x (σ⁻¹ (Fin.natAdd m j))) = ∑ l, x l := by
    rw [← Fin.sum_univ_add (f := fun l => x (σ⁻¹ l))]
    exact Equiv.sum_comp (σ⁻¹ : Equiv.Perm (Fin (m + n))) x
  have hblock : ∑ i : Fin m, pooledCentred m n x (σ⁻¹ (Fin.castAdd n i))
      = (∑ i : Fin m, x (σ⁻¹ (Fin.castAdd n i)))
        - (m : ℝ) * (((m + n : ℕ) : ℝ)⁻¹ * ∑ l, x l) := by
    simp only [pooledCentred]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hBeq : ∑ j : Fin n, x (σ⁻¹ (Fin.natAdd m j))
      = (∑ l, x l) - ∑ i : Fin m, x (σ⁻¹ (Fin.castAdd n i)) := by linarith
  rw [hblock]
  unfold twoSampleMeanDiff
  simp only [perm_smul_apply]
  rw [hBeq, hNcast]
  field_simp
  ring

/-- **The two-sample randomization distribution is the c.d.f. of a permuted block sum.**
Dividing the identity of `twoSampleMeanDiff_smul_eq_blockSum` by the positive constant
`√m N/(mn)` turns `randDist` into exactly the group average appearing in
`ForMathlib/CombinatorialCLT.tendsto_perm_cdf_blockSum`; the inversion `σ ↦ σ⁻¹` — the gap
between the action convention `(σ • x) i = x (σ⁻¹ i)` and the marginal bricks, which are
written with `σ` — is absorbed by `sum_perm_inv`. -/
private lemma randDist_twoSampleMeanDiff_eq (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (x : Fin (m + n) → ℝ) (t : ℝ) :
    randDist (Equiv.Perm (Fin (m + n))) (twoSampleMeanDiff m n) x t
      = (Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (m + n)),
          (if ∑ i : Fin m, pooledCentred m n x (σ (Fin.castAdd n i))
              ≤ t * ((m : ℝ) * n / (Real.sqrt m * ((m + n : ℕ) : ℝ))) then (1 : ℝ) else 0) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNcast : ((m + n : ℕ) : ℝ) = (m : ℝ) + n := by push_cast; ring
  set c : ℝ := Real.sqrt m * ((m + n : ℕ) : ℝ) / ((m : ℝ) * n) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef, hNcast]
    have : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.2 hmR
    positivity
  have hthr : t * ((m : ℝ) * n / (Real.sqrt m * ((m + n : ℕ) : ℝ))) = t / c := by
    rw [hcdef, hNcast]
    have hs : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.2 hmR
    field_simp
  have hkey : ∀ B : ℝ, (c * B ≤ t)
      ↔ (B ≤ t * ((m : ℝ) * n / (Real.sqrt m * ((m + n : ℕ) : ℝ)))) := by
    intro B
    rw [hthr, le_div_iff₀ hcpos, mul_comm B c]
  unfold randDist
  congr 1
  rw [← sum_perm_inv (G := Equiv.Perm (Fin (m + n)))
    (f := fun σ : Equiv.Perm (Fin (m + n)) =>
      if ∑ i : Fin m, pooledCentred m n x (σ (Fin.castAdd n i))
        ≤ t * ((m : ℝ) * n / (Real.sqrt m * ((m + n : ℕ) : ℝ))) then (1 : ℝ) else 0)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [twoSampleMeanDiff_smul_eq_blockSum m n hm hn x σ, ← hcdef]
  exact if_congr (hkey _) rfl rfl

/-! ### Gaussian c.d.f. helpers -/

/-- The c.d.f. of an atomless probability measure on `ℝ` is continuous. -/
private lemma continuousAt_cdf_of_noAtoms (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (t : ℝ) : ContinuousAt (cdf μ) t := by
  have hmono : Monotone (cdf μ) := monotone_cdf μ
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  have hright : Function.rightLim (cdf μ) t = cdf μ t :=
    (hmono.continuousWithinAt_Ioi_iff_rightLim_eq).1
      (((cdf μ).right_continuous t).mono Set.Ioi_subset_Ici_self)
  have hle : Function.leftLim (cdf μ) t ≤ cdf μ t := hmono.leftLim_le le_rfl
  have hge : cdf μ t ≤ Function.leftLim (cdf μ) t := by
    have h0 := (cdf μ).measure_singleton t
    rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos] at h0
    exact h0
  rw [le_antisymm hle hge, hright]

/-- Gaussian scaling of the c.d.f.: `cdf (N(0,τ²)) t = cdf (N(0,1)) (t/τ)` for `τ > 0`. -/
private lemma cdf_gaussianReal_scale {τ : ℝ} (hτ : 0 < τ) (t : ℝ) :
    cdf (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ))) t = cdf (gaussianReal 0 1) (t / τ) := by
  have hmap : gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ))
      = (gaussianReal 0 1).map (fun x => τ * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · rw [mul_zero]
    · rw [mul_one]
  have hset : (fun x : ℝ => τ * x) ⁻¹' Set.Iic t = Set.Iic (t / τ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, le_div_iff₀ hτ, mul_comm τ x]
  rw [cdf_eq_real, cdf_eq_real, hmap, measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Iic, hset]


/-- **The two-sample randomization distribution as a *standardized* permuted block sum.**
Dividing the centred pooled population by a deterministic `√v > 0` and dividing the threshold
of `randDist_twoSampleMeanDiff_eq` by the same constant puts the left-hand side in exactly the
shape of `ForMathlib/CombinatorialCLT.tendsto_perm_cdf_blockSum`, whose hypotheses ask for a
population normalized in the second moment and a threshold measured in units of
`blockSumScale`. The resulting threshold is
`θ = t √(n/N) / √v`, and `θ → t/τ` precisely when `v → v̄ = τ²/(1+λ)` and `n/N → 1/(1+λ)`. -/
private lemma randDist_twoSampleMeanDiff_eq_std (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    {v : ℝ} (hv : 0 < v) (x : Fin (m + n) → ℝ) (t : ℝ) :
    randDist (Equiv.Perm (Fin (m + n))) (twoSampleMeanDiff m n) x t
      = (Fintype.card (Equiv.Perm (Fin (m + n))) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (m + n)),
          (if ∑ i : Fin m, (Real.sqrt v)⁻¹ * pooledCentred m n x (σ (Fin.castAdd n i))
              ≤ t * Real.sqrt ((n : ℝ) / ((m + n : ℕ) : ℝ)) / Real.sqrt v
                * blockSumScale (m + n) m then (1 : ℝ) else 0) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNcast : ((m + n : ℕ) : ℝ) = (m : ℝ) + n := by push_cast; ring
  have hNpos : (0 : ℝ) < ((m + n : ℕ) : ℝ) := by rw [hNcast]; linarith
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hsv : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.2 hv
  -- the standardizing scale, factored
  have hbss : blockSumScale (m + n) m
      = Real.sqrt ((n : ℝ) / ((m + n : ℕ) : ℝ)) * Real.sqrt (m : ℝ) := by
    rw [blockSumScale, ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [hNcast]
    field_simp
    ring
  -- the threshold identity
  have hkey : t * Real.sqrt ((n : ℝ) / ((m + n : ℕ) : ℝ)) / Real.sqrt v
        * blockSumScale (m + n) m
      = (Real.sqrt v)⁻¹ * (t * ((m : ℝ) * n / (Real.sqrt (m : ℝ) * ((m + n : ℕ) : ℝ)))) := by
    rw [hbss]
    have hA : Real.sqrt ((n : ℝ) / ((m + n : ℕ) : ℝ))
        * Real.sqrt ((n : ℝ) / ((m + n : ℕ) : ℝ)) = (n : ℝ) / ((m + n : ℕ) : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hS : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
      Real.mul_self_sqrt hmR.le
    set N' : ℝ := ((m + n : ℕ) : ℝ) with hN'
    set A : ℝ := Real.sqrt ((n : ℝ) / N') with hAdef
    set S : ℝ := Real.sqrt (m : ℝ) with hSdef
    have hn' : (n : ℝ) = A * A * N' := by rw [hA]; field_simp
    rw [← hS, hn']
    field_simp
  rw [randDist_twoSampleMeanDiff_eq m n hm hn x t]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  refine if_congr ?_ rfl rfl
  rw [← Finset.mul_sum, hkey]
  constructor
  · intro h
    exact mul_le_mul_of_nonneg_left h (by positivity)
  · intro h
    exact le_of_mul_le_mul_left h (by positivity)

/-! ### The combinatorial central limit theorem at a moving threshold

The two-sample statistic reaches the combinatorial central limit theorem through a threshold
that depends on the stage — the sample sizes and the pooled dispersion both move with `k` —
so the fixed-threshold form of `ForMathlib/CombinatorialCLT.tendsto_perm_cdf_blockSum` is
squeezed here between its values at `t ∓ ε`. The indicator is monotone in the threshold and
`blockSumScale` is nonnegative, so the sandwich is immediate, and the limit `Φ` is Lipschitz,
hence continuous, so the two brackets close. -/

/-- **The combinatorial central limit theorem with a convergent threshold.** -/
private lemma tendsto_perm_cdf_blockSum_varying {N m : ℕ → ℕ}
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
    -- USER-INPUT: a convergent sequence of thresholds
    {θ : ℕ → ℝ} {t : ℝ} (hθ : Tendsto θ atTop (𝓝 t)) :
    Tendsto (fun k => (Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (N k)),
          (if ∑ i, d k (σ (a k i)) ≤ θ k * blockSumScale (N k) (m k) then (1 : ℝ) else 0))
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
  classical
  have hcont : ContinuousAt (fun s : ℝ => cdf (gaussianReal 0 1) s) t :=
    lipschitzWith_cdf_gaussianReal.continuous.continuousAt
  -- the indicator is monotone in the threshold, `blockSumScale` being nonnegative
  have hmono : ∀ (u v : ℝ), u ≤ v → ∀ (k : ℕ) (σ : Equiv.Perm (Fin (N k))),
      (if ∑ i, d k (σ (a k i)) ≤ u * blockSumScale (N k) (m k) then (1 : ℝ) else 0)
        ≤ (if ∑ i, d k (σ (a k i)) ≤ v * blockSumScale (N k) (m k) then (1 : ℝ) else 0) := by
    intro u v huv k σ
    have hs : (0 : ℝ) ≤ blockSumScale (N k) (m k) := Real.sqrt_nonneg _
    by_cases h : ∑ i, d k (σ (a k i)) ≤ u * blockSumScale (N k) (m k)
    · rw [if_pos h, if_pos (le_trans h (mul_le_mul_of_nonneg_right huv hs))]
    · rw [if_neg h]
      split_ifs <;> norm_num
  have havg : ∀ (u v : ℝ), u ≤ v → ∀ k : ℕ,
      (Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (N k)),
          (if ∑ i, d k (σ (a k i)) ≤ u * blockSumScale (N k) (m k) then (1 : ℝ) else 0)
        ≤ (Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (N k)),
          (if ∑ i, d k (σ (a k i)) ≤ v * blockSumScale (N k) (m k) then (1 : ℝ) else 0) :=
    fun u v huv k =>
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hmono u v huv k σ)
        (by positivity)
  refine tendsto_of_squeeze_continuousAt hcont ?_
  intro ε hε
  have hlo := tendsto_perm_cdf_blockSum a ha d hcent hm hNm hvar hlind (t - ε)
  have hhi := tendsto_perm_cdf_blockSum a ha d hcent hm hNm hvar hlind (t + ε)
  have hlo' := hlo.eventually (eventually_gt_nhds
    (show cdf (gaussianReal 0 1) (t - ε) - ε < cdf (gaussianReal 0 1) (t - ε) by linarith))
  have hhi' := hhi.eventually (eventually_lt_nhds
    (show cdf (gaussianReal 0 1) (t + ε) < cdf (gaussianReal 0 1) (t + ε) + ε by linarith))
  have hθ1 := hθ.eventually (eventually_gt_nhds (show t - ε < t by linarith))
  have hθ2 := hθ.eventually (eventually_lt_nhds (show t < t + ε by linarith))
  filter_upwards [hlo', hhi', hθ1, hθ2] with k h1 h2 h3 h4
  exact ⟨le_trans h1.le (havg (t - ε) (θ k) h3.le k),
    le_trans (havg (θ k) (t + ε) h4.le k) h2.le⟩

/-! ### From deterministic arrays to random arrays

The combinatorial central limit theorem is a statement about a *fixed* sequence of finite
populations, whereas the population a two-sample permutation test acts on is the observed
pooled sample, so its hypotheses hold only **in probability**. The following brick performs
that transfer once and for all, and it is exactly the step the wave-6 status note described:
no measurable selection is involved, only existence.

Given two nonnegative "hypothesis functionals" `A k`, `B k` that tend to `0` in probability,
and a bounded functional `F k` with the property that `F` converges to `L` along *every*
subsequence of deterministic points on which `A` and `B` vanish, one concludes that `F`
converges to `L` in probability. The proof is a contradiction: if `F` failed, a frequency
`δ > 0` of failures would persist, while the good sets `{A < 1/(j+1)} ∩ {B < 1/(j+1)}`
eventually have probability greater than `1 - 2δ/3`; the failure set therefore meets the good
set, which produces a deterministic sequence of points contradicting the hypothesis. -/

/-- **Deterministic-array to random-array transfer.** -/
private lemma tendstoInProb_of_deterministic {𝓧 : ℕ → Type*} [∀ k, MeasurableSpace (𝓧 k)]
    (P : ∀ k, Measure (𝓧 k)) [∀ k, IsProbabilityMeasure (P k)]
    (A B F : ∀ k, 𝓧 k → ℝ) (L : ℝ)
    -- USER-INPUT: the two hypothesis functionals are nonnegative
    (hAnn : ∀ k x, 0 ≤ A k x) (hBnn : ∀ k x, 0 ≤ B k x)
    -- USER-INPUT: they vanish in probability
    (hA : ∀ η > (0 : ℝ), Tendsto (fun k => (P k).real {x | η ≤ A k x}) atTop (𝓝 0))
    (hB : ∀ η > (0 : ℝ), Tendsto (fun k => (P k).real {x | η ≤ B k x}) atTop (𝓝 0))
    -- USER-INPUT: the deterministic statement, along an arbitrary subsequence
    (hdet : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ y : ∀ j, 𝓧 (φ j),
      Tendsto (fun j => A (φ j) (y j)) atTop (𝓝 0) →
      Tendsto (fun j => B (φ j) (y j)) atTop (𝓝 0) →
      Tendsto (fun j => F (φ j) (y j)) atTop (𝓝 L)) :
    ∀ ε > (0 : ℝ), Tendsto (fun k => (P k).real {x | ε ≤ |F k x - L|}) atTop (𝓝 0) := by
  intro ε hε
  by_contra hcon
  rw [Metric.tendsto_atTop] at hcon
  push Not at hcon
  obtain ⟨δ, hδ, hfreq⟩ := hcon
  -- the good sets eventually have probability at least `1 - 2δ/3`
  have hKex : ∀ j : ℕ, ∃ K : ℕ, ∀ k ≥ K,
      (P k).real {x | 1 / ((j : ℝ) + 1) ≤ A k x} < δ / 3
      ∧ (P k).real {x | 1 / ((j : ℝ) + 1) ≤ B k x} < δ / 3 := by
    intro j
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    obtain ⟨K₁, hK₁⟩ := Metric.tendsto_atTop.1 (hA _ hpos) (δ / 3) (by positivity)
    obtain ⟨K₂, hK₂⟩ := Metric.tendsto_atTop.1 (hB _ hpos) (δ / 3) (by positivity)
    refine ⟨max K₁ K₂, fun k hk => ⟨?_, ?_⟩⟩
    · have h := hK₁ k (le_trans (le_max_left _ _) hk)
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h
    · have h := hK₂ k (le_trans (le_max_right _ _) hk)
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h
  choose K hK using hKex
  -- at every level `j` and beyond every stage `M` there is a bad-but-good point
  have hpick : ∀ j M : ℕ, ∃ k : ℕ, M ≤ k ∧ ∃ x : 𝓧 k,
      ε ≤ |F k x - L| ∧ A k x < 1 / ((j : ℝ) + 1) ∧ B k x < 1 / ((j : ℝ) + 1) := by
    intro j M
    obtain ⟨k, hk1, hk2⟩ := hfreq (max M (K j))
    have hkM : M ≤ k := le_trans (le_max_left _ _) hk1
    have hkK : K j ≤ k := le_trans (le_max_right _ _) hk1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hk2
    obtain ⟨hA', hB'⟩ := hK j k hkK
    refine ⟨k, hkM, ?_⟩
    by_contra hempty
    push Not at hempty
    -- the failure set is then covered by the two bad sets
    have hsub : {x : 𝓧 k | ε ≤ |F k x - L|}
        ⊆ {x : 𝓧 k | 1 / ((j : ℝ) + 1) ≤ A k x} ∪ {x : 𝓧 k | 1 / ((j : ℝ) + 1) ≤ B k x} := by
      intro x hx
      simp only [Set.mem_setOf_eq, Set.mem_union] at hx ⊢
      by_contra hno
      push Not at hno
      exact absurd (hempty x hx hno.1) (not_le.2 hno.2)
    have hle := (measureReal_mono hsub (measure_ne_top (P k) _)).trans
      (measureReal_union_le (μ := P k) _ _)
    linarith
  choose pick hpickM y hy1 hy2 hy3 using hpick
  -- the stages, chosen strictly increasing
  obtain ⟨M, hM0, hMs⟩ : ∃ M : ℕ → ℕ, M 0 = 0 ∧ ∀ j, M (j + 1) = pick j (M j) + 1 :=
    ⟨fun j => Nat.rec 0 (fun i prev => pick i prev + 1) j, rfl, fun j => rfl⟩
  have hmono : StrictMono (fun j => pick j (M j)) := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    have h := hpickM (j + 1) (M (j + 1))
    have h2 : pick j (M j) + 1 ≤ pick (j + 1) (M (j + 1)) := by rw [← hMs j]; exact h
    exact h2
  -- the two hypothesis functionals vanish along the chosen points
  have hinv : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hAlim : Tendsto (fun j => A (pick j (M j)) (y j (M j))) atTop (𝓝 0) :=
    squeeze_zero (fun j => hAnn _ _) (fun j => (hy2 j (M j)).le) hinv
  have hBlim : Tendsto (fun j => B (pick j (M j)) (y j (M j))) atTop (𝓝 0) :=
    squeeze_zero (fun j => hBnn _ _) (fun j => (hy3 j (M j)).le) hinv
  -- but then the deterministic statement applies, contradicting the persistent failure
  have hF := hdet (fun j => pick j (M j)) hmono (fun j => y j (M j)) hAlim hBlim
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hF ε hε
  have hbad := hy1 J (M J)
  have hgood := hJ J le_rfl
  rw [Real.dist_eq] at hgood
  linarith

/-! ### A reusable `L¹` law of large numbers on `Measure.pi`

The randomization limits in this directory are all statements about product measures
`Measure.pi (fun _ : Fin n => P)` whose summands are only `L¹` — sample second moments of an
`L²` observation, for instance — so Chebyshev's inequality is unavailable and the honest
route is Kolmogorov's strong law. The following brick packages that route once: it lifts the
`Fin n` product to the Kolmogorov extension `Measure.infinitePi` on `ℕ → Ω`, applies
`ProbabilityTheory.strong_law_ae_real`, converts a.e. convergence to convergence in measure,
and pulls the resulting sets back along
`AsymptoticStatistics.pi_meas_eq_infinitePi_meas_of_truncate`.

It is stated in the `Measure.real` form the randomization `hrem` hypotheses consume, and is
used by `Randomization/MultivariateQuadratic` (consistency of the uncentred second-moment
matrix) and by `Randomization/Studentized` (consistency of the studentizing scale). -/

/-- **`L¹` weak law of large numbers on a finite product measure.** For an integrable `f`,
the empirical mean of `f` along the coordinates converges to `∫ f ∂P` in
`Measure.pi (fun _ : Fin n => P)`-probability as `n → ∞`.

Note the two-parameter structure: the *measure* and the *statistic* both depend on `n`, so
this is a triangular-array statement rather than a limit along a single probability space;
that is exactly why it goes through the Kolmogorov extension rather than through
`ProbabilityTheory.strong_law_ae_real` directly. -/
lemma tendsto_pi_real_lln {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    -- USER-INPUT: the summand has a finite first moment; the classical hypothesis
    (f : Ω → ℝ) (hf : Integrable f P) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)).real
        {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (x i)) - ∫ ω, f ω ∂P|})
      atTop (𝓝 0) := by
  classical
  set μ_inf : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P) with hμ_inf
  have hf_aesm : AEStronglyMeasurable f P := hf.aestronglyMeasurable
  set f' : Ω → ℝ := hf_aesm.mk f with hf'_def
  have hf'_meas : Measurable f' := hf_aesm.measurable_mk
  have hff' : f =ᵐ[P] f' := hf_aesm.ae_eq_mk
  have hf'_int : Integrable f' P := hf.congr hff'
  have hf_integral : ∫ ω, f' ω ∂P = ∫ ω, f ω ∂P := integral_congr_ae hff'.symm
  set Y : ℕ → (ℕ → Ω) → ℝ := fun i ω => f' (ω i) with hY_def
  have hY_meas : ∀ i, Measurable (Y i) := fun i => hf'_meas.comp (measurable_pi_apply i)
  have hMP : ∀ i : ℕ, MeasurePreserving (Function.eval i : (ℕ → Ω) → Ω) μ_inf P :=
    fun i => measurePreserving_eval_infinitePi (μ := fun _ : ℕ => P) i
  have hY0_int : Integrable (Y 0) μ_inf := by
    have := (hMP 0).integrable_comp hf'_meas.aestronglyMeasurable
    simpa [Y, Function.eval] using! this.mpr hf'_int
  have h_iIndep : ProbabilityTheory.iIndepFun Y μ_inf := by
    simpa [Y, Function.eval] using
      (ProbabilityTheory.iIndepFun_infinitePi (Ω := fun _ : ℕ => Ω)
        (P := fun _ : ℕ => P) (X := fun _ : ℕ => f') (fun _ => hf'_meas))
  have h_pair :
      Pairwise (Function.onFun
        (fun X₁ X₂ : (ℕ → Ω) → ℝ => ProbabilityTheory.IndepFun X₁ X₂ μ_inf) Y) :=
    fun i j hij => h_iIndep.indepFun hij
  have hY_map : ∀ i, Measure.map (Y i) μ_inf = Measure.map f' P := by
    intro i
    have h_comp : Y i = f' ∘ (Function.eval i : (ℕ → Ω) → Ω) := by funext ω; rfl
    rw [h_comp, ← Measure.map_map hf'_meas (measurable_pi_apply i), (hMP i).map_eq]
  have h_ident : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ_inf μ_inf := fun i =>
    { aemeasurable_fst := (hY_meas i).aemeasurable
      aemeasurable_snd := (hY_meas 0).aemeasurable
      map_eq := by rw [hY_map i, hY_map 0] }
  have h_mean : ∫ ω, Y 0 ω ∂μ_inf = ∫ ω, f ω ∂P := by
    have h_int : ∫ ω, f' ω ∂P = ∫ ω, Y 0 ω ∂μ_inf := by
      have hP_eq : P = Measure.map (Function.eval 0 : (ℕ → Ω) → Ω) μ_inf := (hMP 0).map_eq.symm
      calc ∫ ω, f' ω ∂P
          = ∫ ω, f' ω ∂Measure.map (Function.eval 0 : (ℕ → Ω) → Ω) μ_inf := by rw [← hP_eq]
        _ = ∫ ω, f' ((Function.eval 0 : (ℕ → Ω) → Ω) ω) ∂μ_inf := by
            refine MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable ?_
            exact hf'_meas.aestronglyMeasurable
        _ = ∫ ω, Y 0 ω ∂μ_inf := by rfl
    rw [← h_int, hf_integral]
  have h_sllN : ∀ᵐ ω ∂μ_inf,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, Y i ω) / n) atTop (𝓝 (∫ ω, Y 0 ω ∂μ_inf)) :=
    ProbabilityTheory.strong_law_ae_real Y hY0_int h_pair h_ident
  have h_ae_eq : ∀ᵐ ω ∂μ_inf, ∀ i : ℕ, f (ω i) = f' (ω i) := by
    rw [ae_all_iff]
    intro i
    exact ((hMP i).quasiMeasurePreserving).ae_eq hff'
  have h_target_ae : ∀ᵐ ω ∂μ_inf,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i))) atTop (𝓝 (∫ ω, f ω ∂P)) := by
    filter_upwards [h_sllN, h_ae_eq] with ω h_lim h_eq_all
    have h_seq_eq : ∀ n : ℕ,
        (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) = (∑ i ∈ Finset.range n, Y i ω) / n := by
      intro n
      have h_sum : (∑ i : Fin n, f (ω i)) = ∑ i ∈ Finset.range n, Y i ω := by
        rw [← Fin.sum_univ_eq_sum_range fun i => Y i ω]
        exact Finset.sum_congr rfl fun i _ => h_eq_all i.val
      rw [h_sum]; ring
    rw [funext h_seq_eq, ← h_mean]
    exact h_lim
  have hF_meas : ∀ n : ℕ,
      AEStronglyMeasurable (fun ω : ℕ → Ω => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i))) μ_inf := by
    intro n
    refine AEStronglyMeasurable.const_mul ?_ _
    refine Finset.aestronglyMeasurable_fun_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun i ω => f (ω i.val)) (μ := μ_inf) (fun i _ => ?_)
    exact hf_aesm.comp_measurePreserving (hMP i.val)
  have h_in_meas : MeasureTheory.TendstoInMeasure μ_inf
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i))) atTop (fun _ => ∫ ω, f ω ∂P) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_ae hF_meas h_target_ae
  have h_norm := (MeasureTheory.tendstoInMeasure_iff_norm (μ := μ_inf) (l := atTop)
      (f := fun (n : ℕ) ω => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)))
      (g := fun _ => ∫ ω, f ω ∂P)).mp h_in_meas
  have h_inf := h_norm ε hε
  have h_set_eq : ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => P))
        {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (x i)) - ∫ ω, f ω ∂P|}
      = μ_inf {ω : ℕ → Ω |
          ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖} := by
    intro n
    have h_pi_ae : (fun (x : Fin n → Ω) i => f (x i)) =ᵐ[Measure.pi (fun _ : Fin n => P)]
        fun (x : Fin n → Ω) i => f' (x i) :=
      MeasureTheory.Measure.ae_eq_pi (μ := fun _ : Fin n => P)
        (f := fun _ => f) (f' := fun _ => f') (fun _ => hff')
    have h_pi_set_eq :
        (Measure.pi (fun _ : Fin n => P))
          {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (x i)) - ∫ ω, f ω ∂P|}
        = (Measure.pi (fun _ : Fin n => P))
          {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (x i)) - ∫ ω, f ω ∂P|} := by
      apply MeasureTheory.measure_congr
      filter_upwards [h_pi_ae] with x hx
      have h_sum_eq : (∑ i : Fin n, f (x i)) = (∑ i : Fin n, f' (x i)) :=
        Finset.sum_congr rfl fun i _ => congrFun hx i
      change (ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (x i)) - ∫ ω, f ω ∂P|) =
             (ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (x i)) - ∫ ω, f ω ∂P|)
      rw [h_sum_eq]
    have hms_f' : MeasurableSet
        {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (x i)) - ∫ ω, f ω ∂P|} := by
      refine measurableSet_le measurable_const ?_
      refine (Measurable.sub ?_ measurable_const).abs
      exact (Finset.measurable_sum _ fun i _ => hf'_meas.comp (measurable_pi_apply i)).const_mul _
    have hbridge_f' :=
      AsymptoticStatistics.pi_meas_eq_infinitePi_meas_of_truncate (ν := P) n hms_f'
    have h_inf_set_eq :
        μ_inf {ω : ℕ → Ω | (fun i : Fin n => ω i.val) ∈
              {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (x i)) - ∫ ω, f ω ∂P|}}
          = μ_inf {ω : ℕ → Ω |
            ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖} := by
      apply MeasureTheory.measure_congr
      filter_upwards [h_ae_eq] with ω hω
      have h_sum_eq : (∑ i : Fin n, f' (ω i.val)) = (∑ i : Fin n, f (ω i)) :=
        Finset.sum_congr rfl fun i _ => (hω i.val).symm
      change (ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (ω i.val)) - ∫ ω, f ω ∂P|) =
             (ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖)
      rw [Real.norm_eq_abs, h_sum_eq]
    rw [h_pi_set_eq, hbridge_f', h_inf_set_eq]
  have hreal : ∀ n : ℕ, (Measure.pi (fun _ : Fin n => P)).real
        {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (x i)) - ∫ ω, f ω ∂P|}
      = (μ_inf {ω : ℕ → Ω |
          ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖}).toReal := by
    intro n; rw [Measure.real, h_set_eq n]
  simp_rw [hreal]
  have := (ENNReal.tendsto_toReal (by simp)).comp h_inf
  simpa using! this

/-! ### Shared bricks: the pooled empirical average

The pooled-population hypotheses of the combinatorial central limit theorem are a pure
law-of-large-numbers statement about the *pooled empirical moments*, and the companion
file `Randomization/Studentized` needs exactly the same inputs for the studentizing
scale. They are therefore recorded here, below both consumers in the import graph: a
three-lemma calculus for convergence in probability along a triangular array, the two
block laws of large numbers obtained by pushing the pooled law onto each block, the two
deterministic weights `m/N → λ/(1+λ)` and `n/N → 1/(1+λ)`, and the pooled average
itself. -/

/-! ### A small calculus for convergence in probability along a triangular array

The studentizing scale is built from the sample moments by four operations — sum, product
with a deterministic factor, square root, reciprocal — and the argument needs each of them to
pass to the limit *in probability*, on a space that changes with `n`. Mathlib's continuous
mapping theorems are for a fixed space, so the three closure properties are recorded here in
the `TendstoInProbTriangular`-style `Measure.real` form used throughout this directory. -/

/-- **Continuous mapping in probability.** Composing with a map continuous at the limit
preserves convergence in probability. -/
lemma tendstoInProb_comp {𝓧 : ℕ → Type*} [∀ n, MeasurableSpace (𝓧 n)]
    {P : ∀ n, Measure (𝓧 n)} [∀ n, IsProbabilityMeasure (P n)]
    {f : ∀ n, 𝓧 n → ℝ} {a : ℝ} {φ : ℝ → ℝ}
    (hφ : ContinuousAt φ a)
    (h : ∀ ε > (0 : ℝ), Tendsto (fun n => (P n).real {x | ε ≤ |f n x - a|}) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ),
      Tendsto (fun n => (P n).real {x | ε ≤ |φ (f n x) - φ a|}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.continuousAt_iff.mp hφ ε hε
  refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) (h ρ hρpos)
  refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
  simp only [Set.mem_setOf_eq] at hx ⊢
  by_contra hcon
  push Not at hcon
  have hd : dist (f n x) a < ρ := by rwa [Real.dist_eq]
  have := hρ hd
  rw [Real.dist_eq] at this
  linarith

/-- **Sums pass to the limit in probability.** -/
lemma tendstoInProb_add {𝓧 : ℕ → Type*} [∀ n, MeasurableSpace (𝓧 n)]
    {P : ∀ n, Measure (𝓧 n)} [∀ n, IsProbabilityMeasure (P n)]
    {f g : ∀ n, 𝓧 n → ℝ} {a b : ℝ}
    (hf : ∀ ε > (0 : ℝ), Tendsto (fun n => (P n).real {x | ε ≤ |f n x - a|}) atTop (𝓝 0))
    (hg : ∀ ε > (0 : ℝ), Tendsto (fun n => (P n).real {x | ε ≤ |g n x - b|}) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => (P n).real
      {x | ε ≤ |(f n x + g n x) - (a + b)|}) atTop (𝓝 0) := by
  intro ε hε
  have hbound : ∀ n : ℕ, (P n).real {x | ε ≤ |(f n x + g n x) - (a + b)|}
      ≤ (P n).real {x | ε / 2 ≤ |f n x - a|} + (P n).real {x | ε / 2 ≤ |g n x - b|} := by
    intro n
    have hincl : {x : 𝓧 n | ε ≤ |(f n x + g n x) - (a + b)|}
        ⊆ {x | ε / 2 ≤ |f n x - a|} ∪ {x | ε / 2 ≤ |g n x - b|} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
      obtain ⟨h1, h2⟩ := hcon
      have htri := abs_add_le (f n x - a) (g n x - b)
      have heq : (f n x + g n x) - (a + b) = (f n x - a) + (g n x - b) := by ring
      rw [heq] at hx
      linarith
    exact (measureReal_mono hincl (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  refine squeeze_zero (fun n => measureReal_nonneg) hbound ?_
  simpa using (hf (ε / 2) (by positivity)).add (hg (ε / 2) (by positivity))

/-- **Multiplication by a deterministic convergent factor.** This is where the sample-size
ratio `m/n → λ` enters the studentizing scale. -/
lemma tendstoInProb_const_mul {𝓧 : ℕ → Type*} [∀ n, MeasurableSpace (𝓧 n)]
    {P : ∀ n, Measure (𝓧 n)} [∀ n, IsProbabilityMeasure (P n)]
    {f : ∀ n, 𝓧 n → ℝ} {c : ℕ → ℝ} {a cl : ℝ}
    (hc : Tendsto c atTop (𝓝 cl))
    (hf : ∀ ε > (0 : ℝ), Tendsto (fun n => (P n).real {x | ε ≤ |f n x - a|}) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => (P n).real
      {x | ε ≤ |c n * f n x - cl * a|}) atTop (𝓝 0) := by
  intro ε hε
  have hpos : (0 : ℝ) < |cl| + 1 := by positivity
  set ρ : ℝ := ε / (2 * (|cl| + 1)) with hρdef
  have hρpos : 0 < ρ := by positivity
  have hev1 : ∀ᶠ n in atTop, |c n| ≤ |cl| + 1 := by
    have := hc.abs.eventually (eventually_lt_nhds (show |cl| < |cl| + 1 by linarith))
    exact this.mono fun n hn => hn.le
  have hev2 : ∀ᶠ n in atTop, |c n - cl| * |a| < ε / 2 := by
    have hlim : Tendsto (fun n => |c n - cl| * |a|) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => c n - cl) atTop (𝓝 0) := by
        simpa using hc.sub_const cl
      simpa using (h0.abs).mul_const |a|
    exact hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity))
  have hbound : ∀ᶠ n in atTop, (P n).real {x | ε ≤ |c n * f n x - cl * a|}
      ≤ (P n).real {x | ρ ≤ |f n x - a|} := by
    filter_upwards [hev1, hev2] with n hn1 hn2
    refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_contra hcon
    push Not at hcon
    have hsplit : c n * f n x - cl * a = c n * (f n x - a) + (c n - cl) * a := by ring
    have h1 : |c n * (f n x - a)| ≤ (|cl| + 1) * ρ := by
      rw [abs_mul]
      exact mul_le_mul hn1 hcon.le (abs_nonneg _) (by positivity)
    have h2 : (|cl| + 1) * ρ = ε / 2 := by rw [hρdef]; field_simp
    have h3 : |(c n - cl) * a| < ε / 2 := by rw [abs_mul]; exact hn2
    have htri := abs_add_le (c n * (f n x - a)) ((c n - cl) * a)
    rw [hsplit] at hx
    linarith
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) hbound ?_
  exact hf ρ hρpos

/-! ### The two blocks of the pooled law -/

/-- The `Y`-block coordinates of the pooled sample are an i.i.d. `P_Y` sample: the block
projection pushes the pooled law forward onto the `Y`-product. -/
lemma map_projY (m n : ℕ) (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] :
    (twoSampleLaw m n PY PZ).map
        (fun x : Fin (m + n) → ℝ => fun i : Fin m => x (Fin.castAdd n i))
      = Measure.pi (fun _ : Fin m => PY) := by
  classical
  haveI hfam : ∀ i : Fin (m + n), IsProbabilityMeasure
      (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i) := by
    intro i
    refine Fin.addCases (m := m) (n := n)
      (motive := fun i => IsProbabilityMeasure
        (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i))
      (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using (inferInstance : IsProbabilityMeasure PY)
    · simpa only [Fin.addCases_right] using (inferInstance : IsProbabilityMeasure PZ)
  have hmeas : Measurable (fun x : Fin (m + n) → ℝ => fun i : Fin m => x (Fin.castAdd n i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  refine (Measure.pi_eq (μ := fun _ : Fin m => PY) (fun s hs => ?_)).symm
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : Fin (m + n) → ℝ => fun i : Fin m => x (Fin.castAdd n i)) ⁻¹'
      (Set.univ.pi s)
      = Set.univ.pi (Fin.addCases (motive := fun _ => Set ℝ) s (fun _ => Set.univ)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h l
      refine Fin.addCases (m := m) (n := n)
        (motive := fun l => x l ∈ Fin.addCases (motive := fun _ => Set ℝ) s
          (fun _ => Set.univ) l) (fun i => ?_) (fun j => ?_) l
      · simpa only [Fin.addCases_left] using h i
      · simp only [Fin.addCases_right]; exact Set.mem_univ _
    · intro h i
      simpa only [Fin.addCases_left] using h (Fin.castAdd n i)
  rw [hpre, twoSampleLaw, Measure.pi_pi, Fin.prod_univ_add]
  simp

/-- The `Z`-block twin of `map_projY`. -/
lemma map_projZ (m n : ℕ) (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] :
    (twoSampleLaw m n PY PZ).map
        (fun x : Fin (m + n) → ℝ => fun j : Fin n => x (Fin.natAdd m j))
      = Measure.pi (fun _ : Fin n => PZ) := by
  classical
  haveI hfam : ∀ i : Fin (m + n), IsProbabilityMeasure
      (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i) := by
    intro i
    refine Fin.addCases (m := m) (n := n)
      (motive := fun i => IsProbabilityMeasure
        (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i))
      (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using (inferInstance : IsProbabilityMeasure PY)
    · simpa only [Fin.addCases_right] using (inferInstance : IsProbabilityMeasure PZ)
  have hmeas : Measurable (fun x : Fin (m + n) → ℝ => fun j : Fin n => x (Fin.natAdd m j)) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  refine (Measure.pi_eq (μ := fun _ : Fin n => PZ) (fun s hs => ?_)).symm
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : Fin (m + n) → ℝ => fun j : Fin n => x (Fin.natAdd m j)) ⁻¹'
      (Set.univ.pi s)
      = Set.univ.pi (Fin.addCases (motive := fun _ => Set ℝ) (fun _ => Set.univ) s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h l
      refine Fin.addCases (m := m) (n := n)
        (motive := fun l => x l ∈ Fin.addCases (motive := fun _ => Set ℝ)
          (fun _ => Set.univ) s l) (fun i => ?_) (fun j => ?_) l
      · simp only [Fin.addCases_left]; exact Set.mem_univ _
      · simpa only [Fin.addCases_right] using h j
    · intro h j
      simpa only [Fin.addCases_right] using h (Fin.natAdd m j)
  rw [hpre, twoSampleLaw, Measure.pi_pi, Fin.prod_univ_add]
  simp

/-- **The `L¹` law of large numbers on the `Y` block.** The block coordinates are i.i.d.
`P_Y`, so the generic product-measure law of large numbers transports along the projection. -/
lemma tendsto_lln_blockY (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (f : ℝ → ℝ) (hfm : Measurable f) (hf : Integrable f PY) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
        {x : Fin (m k + n k) → ℝ | ε ≤ |((m k : ℝ))⁻¹ *
          (∑ i : Fin (m k), f (x (Fin.castAdd (n k) i))) - ∫ t, f t ∂PY|})
      atTop (𝓝 0) := by
  have hbase := (tendsto_pi_real_lln (P := PY) f hf hε).comp hm
  refine hbase.congr fun k => ?_
  have hmeas : Measurable
      (fun x : Fin (m k + n k) → ℝ => fun i : Fin (m k) => x (Fin.castAdd (n k) i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hms : MeasurableSet {y : Fin (m k) → ℝ |
      ε ≤ |((m k : ℝ))⁻¹ * (∑ i : Fin (m k), f (y i)) - ∫ t, f t ∂PY|} := by
    refine measurableSet_le measurable_const ((Measurable.sub ?_ measurable_const).abs)
    exact (Finset.measurable_sum _ fun i _ => hfm.comp (measurable_pi_apply i)).const_mul _
  have hval : (Measure.pi fun _ : Fin (m k) => PY) {y : Fin (m k) → ℝ |
        ε ≤ |((m k : ℝ))⁻¹ * (∑ i : Fin (m k), f (y i)) - ∫ t, f t ∂PY|}
      = twoSampleLaw (m k) (n k) PY PZ {x : Fin (m k + n k) → ℝ |
        ε ≤ |((m k : ℝ))⁻¹ * (∑ i : Fin (m k), f (x (Fin.castAdd (n k) i)))
          - ∫ t, f t ∂PY|} := by
    rw [← map_projY (m k) (n k) PY PZ, Measure.map_apply hmeas hms]
    rfl
  simp only [Measure.real, Function.comp_apply, hval]

/-- **The `L¹` law of large numbers on the `Z` block.** -/
lemma tendsto_lln_blockZ (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (f : ℝ → ℝ) (hfm : Measurable f) (hf : Integrable f PZ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
        {x : Fin (m k + n k) → ℝ | ε ≤ |((n k : ℝ))⁻¹ *
          (∑ j : Fin (n k), f (x (Fin.natAdd (m k) j))) - ∫ t, f t ∂PZ|})
      atTop (𝓝 0) := by
  have hbase := (tendsto_pi_real_lln (P := PZ) f hf hε).comp hn
  refine hbase.congr fun k => ?_
  have hmeas : Measurable
      (fun x : Fin (m k + n k) → ℝ => fun j : Fin (n k) => x (Fin.natAdd (m k) j)) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hms : MeasurableSet {y : Fin (n k) → ℝ |
      ε ≤ |((n k : ℝ))⁻¹ * (∑ j : Fin (n k), f (y j)) - ∫ t, f t ∂PZ|} := by
    refine measurableSet_le measurable_const ((Measurable.sub ?_ measurable_const).abs)
    exact (Finset.measurable_sum _ fun j _ => hfm.comp (measurable_pi_apply j)).const_mul _
  have hval : (Measure.pi fun _ : Fin (n k) => PZ) {y : Fin (n k) → ℝ |
        ε ≤ |((n k : ℝ))⁻¹ * (∑ j : Fin (n k), f (y j)) - ∫ t, f t ∂PZ|}
      = twoSampleLaw (m k) (n k) PY PZ {x : Fin (m k + n k) → ℝ |
        ε ≤ |((n k : ℝ))⁻¹ * (∑ j : Fin (n k), f (x (Fin.natAdd (m k) j)))
          - ∫ t, f t ∂PZ|} := by
    rw [← map_projZ (m k) (n k) PY PZ, Measure.map_apply hmeas hms]
    rfl
  simp only [Measure.real, Function.comp_apply, hval]

/-! ### The pooled empirical average

Both block averages of a permuted pooled vector concentrate around the **pooled** average, so
the limit of the randomized scale is governed by the pooled empirical moments; those in turn
obey the law of large numbers, being fixed convex combinations of the two block averages with
weights `m/N → λ/(1+λ)` and `n/N → 1/(1+λ)`. -/

/-- The `Y`-block weight `m/N` converges to `λ/(1+λ)`. -/
lemma tendsto_weightY {lam : ℝ} (m n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam) :
    Tendsto (fun k => (m k : ℝ) / ((m k + n k : ℕ) : ℝ)) atTop (𝓝 (lam / (1 + lam))) := by
  have hne : (1 : ℝ) + lam ≠ 0 := by positivity
  have hbase : Tendsto (fun k => (m k : ℝ) / n k / (1 + (m k : ℝ) / n k)) atTop
      (𝓝 (lam / (1 + lam))) := hratio.div (hratio.const_add 1) hne
  refine hbase.congr' ?_
  filter_upwards [hn.eventually_gt_atTop 0] with k hk
  have hnR : (0 : ℝ) < (n k : ℝ) := by exact_mod_cast hk
  have hNcast : ((m k + n k : ℕ) : ℝ) = (m k : ℝ) + n k := by push_cast; ring
  rw [hNcast]
  field_simp
  ring

/-- The `Z`-block weight `n/N` converges to `1/(1+λ)`. -/
lemma tendsto_weightZ {lam : ℝ} (m n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam) :
    Tendsto (fun k => (n k : ℝ) / ((m k + n k : ℕ) : ℝ)) atTop (𝓝 (1 / (1 + lam))) := by
  have hne : (1 : ℝ) + lam ≠ 0 := by positivity
  have hbase : Tendsto (fun k => (1 : ℝ) / (1 + (m k : ℝ) / n k)) atTop
      (𝓝 (1 / (1 + lam))) := tendsto_const_nhds.div (hratio.const_add 1) hne
  refine hbase.congr' ?_
  filter_upwards [hn.eventually_gt_atTop 0] with k hk
  have hnR : (0 : ℝ) < (n k : ℝ) := by exact_mod_cast hk
  have hNcast : ((m k + n k : ℕ) : ℝ) = (m k : ℝ) + n k := by push_cast; ring
  rw [hNcast]
  field_simp
  ring

/-- **The pooled empirical average obeys the law of large numbers.** The pooled average of
`f` over all `N = m + n` coordinates converges in probability to the mixture
`λ/(1+λ) · ∫f dP_Y + 1/(1+λ) · ∫f dP_Z`. -/
lemma tendstoInProb_pooledAvg (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam : ℝ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    (f : ℝ → ℝ) (hfm : Measurable f) (hY : Integrable f PY) (hZ : Integrable f PZ) :
    ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |((m k + n k : ℕ) : ℝ)⁻¹ * (∑ l, f (x l))
        - (lam / (1 + lam) * (∫ t, f t ∂PY) + 1 / (1 + lam) * ∫ t, f t ∂PZ)|})
      atTop (𝓝 0) := by
  have hblkY := fun ε hε => tendsto_lln_blockY PY PZ m n hm f hfm hY (ε := ε) hε
  have hblkZ := fun ε hε => tendsto_lln_blockZ PY PZ m n hn f hfm hZ (ε := ε) hε
  have hwY := tendstoInProb_const_mul (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
    (tendsto_weightY m n hn hratio hlam) hblkY
  have hwZ := tendstoInProb_const_mul (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
    (tendsto_weightZ m n hn hratio hlam) hblkZ
  have hsum := tendstoInProb_add (P := fun k => twoSampleLaw (m k) (n k) PY PZ) hwY hwZ
  intro ε hε
  refine (hsum ε hε).congr' ?_
  filter_upwards [hm.eventually_gt_atTop 0, hn.eventually_gt_atTop 0] with k hmk hnk
  have hmR : (0 : ℝ) < (m k : ℝ) := by exact_mod_cast hmk
  have hnR : (0 : ℝ) < (n k : ℝ) := by exact_mod_cast hnk
  have hNcast : ((m k + n k : ℕ) : ℝ) = (m k : ℝ) + n k := by push_cast; ring
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  have hid : (m k : ℝ) / ((m k + n k : ℕ) : ℝ) *
        ((m k : ℝ)⁻¹ * ∑ i : Fin (m k), f (x (Fin.castAdd (n k) i)))
      + (n k : ℝ) / ((m k + n k : ℕ) : ℝ) *
        ((n k : ℝ)⁻¹ * ∑ j : Fin (n k), f (x (Fin.natAdd (m k) j)))
      = ((m k + n k : ℕ) : ℝ)⁻¹ * ∑ l, f (x l) := by
    rw [Fin.sum_univ_add (f := fun l => f (x l)), hNcast]
    field_simp
  rw [hid]

/-- The population variance as (second moment) − (mean)². -/
lemma var_eq_second_sub_sq {Q : Measure ℝ} [IsProbabilityMeasure Q] {μ v : ℝ}
    (hQ2 : MemLp id 2 Q) (hmeanQ : ∫ t, t ∂Q = μ) (hvarQ : ∫ t, (t - μ) ^ 2 ∂Q = v) :
    (∫ t, t ^ 2 ∂Q) + -(μ ^ 2) = v := by
  have hid : Integrable (fun t : ℝ => t) Q := by simpa using! hQ2.integrable (by norm_num)
  have hsq : Integrable (fun t : ℝ => t ^ 2) Q := by simpa using hQ2.integrable_sq
  have hlin : Integrable (fun t : ℝ => 2 * μ * t) Q := hid.const_mul _
  have h1 : Integrable (fun t : ℝ => t ^ 2 - 2 * μ * t) Q := hsq.sub hlin
  have hfun : (fun t : ℝ => (t - μ) ^ 2) = fun t => (t ^ 2 - 2 * μ * t) + μ ^ 2 := by
    funext t; ring
  rw [← hvarQ, hfun, integral_add h1 (integrable_const _), integral_sub hsq hlin,
    integral_const_mul, hmeanQ]
  simp
  ring

/-! ### The standardized pooled population and its two hypothesis functionals

The combinatorial central limit theorem asks for a centred population normalized in the
second moment and satisfying Hájek's Lindeberg condition. The pooled data supply the first
after division by the deterministic constant `√v̄`, `v̄ = (λ varY + varZ)/(1+λ)`; the second
holds only in probability, and — since the transfer brick above consumes a *single* scalar
functional rather than a family indexed by `ε` — it is packaged here as the single
**Lindeberg defect**
`Λ = N⁻¹ ∑ e² min(1, |e|/R)`, `R = √(min (m, N − m))`,
which dominates every member of the family: on `{|e| ≥ εR}` one has
`min(1, |e|/R) ≥ min(1, ε)`. -/

/-- The centred pooled data, normalized by a deterministic scale. -/
private noncomputable def pooledStd (m n : ℕ) (v : ℝ) (x : Fin (m + n) → ℝ) :
    Fin (m + n) → ℝ := fun l => (Real.sqrt v)⁻¹ * pooledCentred m n x l

/-- The **normalization defect**: how far the normalized second moment is from `1`. -/
private noncomputable def normDefect (m n : ℕ) (v : ℝ) (x : Fin (m + n) → ℝ) : ℝ :=
  |((m + n : ℕ) : ℝ)⁻¹ * ∑ l, pooledStd m n v x l ^ 2 - 1|

/-- The **Lindeberg defect** at Hájek's scale `√(min (m, N − m))`. -/
private noncomputable def lindebergDefect (m n : ℕ) (v : ℝ) (x : Fin (m + n) → ℝ) : ℝ :=
  ((m + n : ℕ) : ℝ)⁻¹ * ∑ l, pooledStd m n v x l ^ 2 *
    min 1 (|pooledStd m n v x l| /
      Real.sqrt (min (m : ℝ) (((m + n : ℕ) : ℝ) - (m : ℝ))))

private lemma lindebergDefect_nonneg (m n : ℕ) (v : ℝ) (x : Fin (m + n) → ℝ) :
    0 ≤ lindebergDefect m n v x := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => ?_)
  exact mul_nonneg (sq_nonneg _) (le_min zero_le_one (by positivity))

/-- The centred pooled data sums to zero — with no nonemptiness hypothesis. -/
private lemma sum_pooledCentred' (m n : ℕ) (x : Fin (m + n) → ℝ) :
    ∑ l, pooledCentred m n x l = 0 := by
  rcases Nat.eq_zero_or_pos (m + n) with h0 | hpos
  · have huniv : (Finset.univ : Finset (Fin (m + n))) = ∅ := by
      rw [← Finset.card_eq_zero, Finset.card_univ, Fintype.card_fin, h0]
    simp [pooledCentred, huniv]
  · exact sum_pooledCentred m n hpos x

/-- **The Lindeberg defect dominates Hájek's Lindeberg condition**, member by member. -/
private lemma lindeberg_le_lindebergDefect {N : ℕ} (d : Fin N → ℝ) {R : ℝ} (hR : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    (N : ℝ)⁻¹ * ∑ l, (if ε * R ≤ |d l| then d l ^ 2 else 0)
      ≤ (min 1 ε)⁻¹ * ((N : ℝ)⁻¹ * ∑ l, d l ^ 2 * min 1 (|d l| / R)) := by
  have hmin : (0 : ℝ) < min 1 ε := lt_min zero_lt_one hε
  have hpt : ∀ l : Fin N, (if ε * R ≤ |d l| then d l ^ 2 else 0)
      ≤ (min 1 ε)⁻¹ * (d l ^ 2 * min 1 (|d l| / R)) := by
    intro l
    by_cases h : ε * R ≤ |d l|
    · rw [if_pos h]
      have hge : min 1 ε ≤ min 1 (|d l| / R) := by
        refine le_min (min_le_left _ _) (le_trans (min_le_right _ _) ?_)
        rw [le_div_iff₀ hR]
        exact h
      have := mul_le_mul_of_nonneg_left hge (sq_nonneg (d l))
      calc d l ^ 2 = (min 1 ε)⁻¹ * (d l ^ 2 * min 1 ε) := by field_simp
        _ ≤ (min 1 ε)⁻¹ * (d l ^ 2 * min 1 (|d l| / R)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
    · rw [if_neg h]
      have hnn : (0 : ℝ) ≤ min 1 (|d l| / R) := le_min zero_le_one (by positivity)
      positivity
  calc (N : ℝ)⁻¹ * ∑ l, (if ε * R ≤ |d l| then d l ^ 2 else 0)
      ≤ (N : ℝ)⁻¹ * ∑ l, (min 1 ε)⁻¹ * (d l ^ 2 * min 1 (|d l| / R)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => hpt l) (by positivity)
    _ = (min 1 ε)⁻¹ * ((N : ℝ)⁻¹ * ∑ l, d l ^ 2 * min 1 (|d l| / R)) := by
        rw [← Finset.mul_sum]; ring

/-! ### The pooled empirical moments and the tail second moment

The two hypothesis functionals are, after dividing out the deterministic scale `v̄`, built
from three pooled empirical averages: the pooled mean `x̄`, the pooled variance
`N⁻¹ ∑ (x_l − x̄)²`, and — for the Lindeberg defect — the **tail second moment**
`N⁻¹ ∑ x_l² 1{|x_l| ≥ K}`. All three are instances of `tendstoInProb_pooledAvg`, and the
tail one converges, as `K → ∞`, to a limit that vanishes by dominated convergence. That is
the only place where `MemLp id 2` is used, and it is why no moment beyond `L²` is needed. -/

/-- The **pooled sample mean** `x̄ = N⁻¹ ∑_l x_l`. -/
private noncomputable def pooledMean (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  ((m + n : ℕ) : ℝ)⁻¹ * ∑ l, x l

/-- The **pooled sample variance** `N⁻¹ ∑_l (x_l − x̄)²`. -/
private noncomputable def pooledVar (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  ((m + n : ℕ) : ℝ)⁻¹ * ∑ l, (x l - pooledMean m n x) ^ 2

private lemma pooledVar_nonneg (m n : ℕ) (x : Fin (m + n) → ℝ) : 0 ≤ pooledVar m n x :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => sq_nonneg _)

/-- The pooled variance as (second moment) − (mean)², the form the law of large numbers
reaches it in. -/
private lemma pooledVar_eq {m n : ℕ} (hmn : 0 < m + n) (x : Fin (m + n) → ℝ) :
    pooledVar m n x
      = ((m + n : ℕ) : ℝ)⁻¹ * (∑ l, x l ^ 2) + -(pooledMean m n x ^ 2) := by
  have hN : (0 : ℝ) < ((m + n : ℕ) : ℝ) := by exact_mod_cast hmn
  have hsum : ∑ l, x l = ((m + n : ℕ) : ℝ) * pooledMean m n x := by
    rw [pooledMean, ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
  have hexp : ∀ l : Fin (m + n), (x l - pooledMean m n x) ^ 2
      = x l ^ 2 - 2 * pooledMean m n x * x l + pooledMean m n x ^ 2 := fun l => by ring
  rw [pooledVar]
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum]
  field_simp
  ring

/-- The **tail square** `t² 1{K ≤ |t|}`: the integrand of the tail second moment. -/
private noncomputable def tailSq (K : ℝ) : ℝ → ℝ := fun t => if K ≤ |t| then t ^ 2 else 0

private lemma tailSq_nonneg (K t : ℝ) : 0 ≤ tailSq K t := by
  unfold tailSq; split
  · positivity
  · exact le_rfl

private lemma tailSq_le_sq (K t : ℝ) : tailSq K t ≤ t ^ 2 := by
  unfold tailSq; split
  · exact le_rfl
  · positivity

private lemma measurable_tailSq (K : ℝ) : Measurable (tailSq K) := by
  unfold tailSq
  exact Measurable.ite (measurableSet_le measurable_const measurable_id.abs)
    (measurable_id.pow_const 2) measurable_const

private lemma integrable_tailSq {Q : Measure ℝ} (K : ℝ)
    (hQ : Integrable (fun t : ℝ => t ^ 2) Q) : Integrable (tailSq K) Q := by
  refine hQ.mono' (measurable_tailSq K).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tailSq_nonneg K t)]
  exact tailSq_le_sq K t

/-- **The tail second moment vanishes.** Plain dominated convergence, dominated by `t²`
itself; this is the only use of the second-moment hypothesis. -/
private lemma tendsto_integral_tailSq {Q : Measure ℝ}
    (hQ : Integrable (fun t : ℝ => t ^ 2) Q) :
    Tendsto (fun j : ℕ => ∫ t, tailSq (j : ℝ) t ∂Q) atTop (𝓝 0) := by
  have hzero : ∫ (_ : ℝ), (0 : ℝ) ∂Q = 0 := integral_zero _ _
  have h := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun (j : ℕ) (t : ℝ) => tailSq (j : ℝ) t) (f := fun _ : ℝ => (0 : ℝ))
    (bound := fun t : ℝ => t ^ 2)
    (fun j => (measurable_tailSq _).aestronglyMeasurable) hQ
    (fun j => ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tailSq_nonneg _ t)]
      exact tailSq_le_sq _ t)
    (ae_of_all _ fun t => ?_)
  · rwa [hzero] at h
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ⌈|t|⌉₊] with j hj
    have hlt : |t| < (j : ℝ) := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hj)
    unfold tailSq
    rw [if_neg (not_le.mpr hlt)]

/-! ### The two hypothesis functionals, rewritten -/

/-- The normalization defect is the pooled variance, rescaled. -/
private lemma normDefect_eq {m n : ℕ} {v : ℝ} (hv : 0 < v) (x : Fin (m + n) → ℝ) :
    normDefect m n v x = |v⁻¹ * pooledVar m n x - 1| := by
  have hsq : (Real.sqrt v)⁻¹ ^ 2 = v⁻¹ := by rw [inv_pow, Real.sq_sqrt hv.le]
  have hterm : ∀ l : Fin (m + n),
      pooledStd m n v x l ^ 2 = v⁻¹ * (x l - pooledMean m n x) ^ 2 := by
    intro l
    have hpc : pooledStd m n v x l = (Real.sqrt v)⁻¹ * (x l - pooledMean m n x) := rfl
    rw [hpc, mul_pow, hsq]
  rw [normDefect, Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hterm l),
    ← Finset.mul_sum, pooledVar]
  congr 1
  ring

/-- The Lindeberg defect, with the deterministic scale `√v̄` moved into the threshold. -/
private lemma lindebergDefect_eq {m n : ℕ} {v : ℝ} (hv : 0 < v) (x : Fin (m + n) → ℝ) :
    lindebergDefect m n v x
      = v⁻¹ * (((m + n : ℕ) : ℝ)⁻¹ * ∑ l, (x l - pooledMean m n x) ^ 2 *
          min 1 (|x l - pooledMean m n x| /
            (Real.sqrt v * Real.sqrt (min (m : ℝ) (((m + n : ℕ) : ℝ) - (m : ℝ)))))) := by
  have hsv : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hsq : (Real.sqrt v)⁻¹ ^ 2 = v⁻¹ := by rw [inv_pow, Real.sq_sqrt hv.le]
  have hterm : ∀ l : Fin (m + n),
      pooledStd m n v x l ^ 2 *
          min 1 (|pooledStd m n v x l| /
            Real.sqrt (min (m : ℝ) (((m + n : ℕ) : ℝ) - (m : ℝ))))
        = v⁻¹ * ((x l - pooledMean m n x) ^ 2 *
            min 1 (|x l - pooledMean m n x| /
              (Real.sqrt v * Real.sqrt (min (m : ℝ) (((m + n : ℕ) : ℝ) - (m : ℝ)))))) := by
    intro l
    have hpc : pooledStd m n v x l = (Real.sqrt v)⁻¹ * (x l - pooledMean m n x) := rfl
    have habs : |pooledStd m n v x l| = (Real.sqrt v)⁻¹ * |x l - pooledMean m n x| := by
      rw [hpc, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hsv))]
    have hdiv : (Real.sqrt v)⁻¹ * |x l - pooledMean m n x| /
          Real.sqrt (min (m : ℝ) (((m + n : ℕ) : ℝ) - (m : ℝ)))
        = |x l - pooledMean m n x| /
          (Real.sqrt v * Real.sqrt (min (m : ℝ) (((m + n : ℕ) : ℝ) - (m : ℝ)))) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
      ring
    rw [habs, hdiv, hpc, mul_pow, hsq, mul_assoc]
  rw [lindebergDefect, Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hterm l),
    ← Finset.mul_sum]
  ring

/-! ### The deterministic Lindeberg split

Off the tail `{|t| ≥ K}` the truncation factor `min(1, |x_l − x̄|/r)` is at most
`(K + |x̄|)/r`, which is deterministic and `o(1)` because `r = √v̄ · √(min(m,n)) → ∞`; on the
tail it is at most `1`, and `(x_l − x̄)² ≤ 2x_l² + 2x̄² ≤ 2(1 + x̄²) x_l²` there, because
`K ≥ 1` forces `x_l² ≥ 1`. No probability is involved. -/

private lemma tailSq_lindeberg_bound {b r K : ℝ} (hr : 0 < r) (hK : 1 ≤ K) (u : ℝ) :
    (u - b) ^ 2 * min 1 (|u - b| / r)
      ≤ (K + |b|) / r * (u - b) ^ 2 + 2 * (1 + b ^ 2) * tailSq K u := by
  have hbnn : (0 : ℝ) ≤ |b| := abs_nonneg b
  by_cases hge : K ≤ |u|
  · have h1 : tailSq K u = u ^ 2 := by unfold tailSq; rw [if_pos hge]
    have hu2 : (1 : ℝ) ≤ u ^ 2 := by
      have h1u : (1 : ℝ) ≤ |u| := le_trans hK hge
      nlinarith [sq_abs u, abs_nonneg u]
    have hstep : (u - b) ^ 2 * min 1 (|u - b| / r) ≤ (u - b) ^ 2 := by
      nlinarith [min_le_left (1 : ℝ) (|u - b| / r), sq_nonneg (u - b)]
    have hexp : (u - b) ^ 2 ≤ 2 * u ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (u + b)]
    have hfirst : 0 ≤ (K + |b|) / r * (u - b) ^ 2 := by
      have hKb : (0 : ℝ) ≤ K + |b| := by linarith
      positivity
    rw [h1]
    nlinarith [mul_nonneg (sq_nonneg b) (by linarith : (0 : ℝ) ≤ u ^ 2 - 1)]
  · have h0 : tailSq K u = 0 := by unfold tailSq; rw [if_neg hge]
    have hlt : |u| < K := not_le.mp hge
    have hnum : |u - b| ≤ K + |b| := by
      have := abs_sub b u
      calc |u - b| ≤ |u| + |b| := abs_sub _ _
        _ ≤ K + |b| := by linarith
    have hmin : min 1 (|u - b| / r) ≤ (K + |b|) / r := by
      refine le_trans (min_le_right _ _) ?_
      gcongr
    rw [h0, mul_zero, add_zero]
    have := mul_le_mul_of_nonneg_left hmin (sq_nonneg (u - b))
    linarith [this]

private lemma lindeberg_sum_le {N : ℕ} (x : Fin N → ℝ) {b r K : ℝ} (hr : 0 < r)
    (hK : 1 ≤ K) :
    (N : ℝ)⁻¹ * ∑ l, (x l - b) ^ 2 * min 1 (|x l - b| / r)
      ≤ (K + |b|) / r * ((N : ℝ)⁻¹ * ∑ l, (x l - b) ^ 2)
        + 2 * (1 + b ^ 2) * ((N : ℝ)⁻¹ * ∑ l, tailSq K (x l)) := by
  have hstep : ∑ l, (x l - b) ^ 2 * min 1 (|x l - b| / r)
      ≤ ∑ l, ((K + |b|) / r * (x l - b) ^ 2 + 2 * (1 + b ^ 2) * tailSq K (x l)) :=
    Finset.sum_le_sum fun l _ => tailSq_lindeberg_bound hr hK (x l)
  have hmul := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ ((N : ℝ))⁻¹)
  refine hmul.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **The Lindeberg defect is dominated by three pooled empirical averages.** -/
private lemma lindebergDefect_le {m n : ℕ} {v K : ℝ} (hv : 0 < v) (hK : 1 ≤ K)
    (hr : 0 < Real.sqrt (min (m : ℝ) (((m + n : ℕ) : ℝ) - (m : ℝ))))
    (x : Fin (m + n) → ℝ) :
    lindebergDefect m n v x
      ≤ v⁻¹ * ((K + |pooledMean m n x|) /
            (Real.sqrt v * Real.sqrt (min (m : ℝ) (((m + n : ℕ) : ℝ) - (m : ℝ))))
              * pooledVar m n x
          + 2 * (1 + pooledMean m n x ^ 2) *
              (((m + n : ℕ) : ℝ)⁻¹ * ∑ l, tailSq K (x l))) := by
  have hsv : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hrv : (0 : ℝ) < Real.sqrt v *
      Real.sqrt (min (m : ℝ) (((m + n : ℕ) : ℝ) - (m : ℝ))) := mul_pos hsv hr
  rw [lindebergDefect_eq hv x]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  simpa only [pooledVar] using
    lindeberg_sum_le x (b := pooledMean m n x) (K := K) hrv hK

/-- **The pooled population satisfies the hypotheses of the combinatorial central limit
theorem in probability.**

STATUS (wave 9): **CLOSED**, axiom-clean. It was the last debt of the two-sample permutation
chain, and it is a pure law-of-large-numbers statement about the *pooled empirical moments* —
no permutation, no central limit theorem, no measurable selection. The two arithmetic
ingredients used to sit in `Randomization/Studentized`, which is *above* this file in the
import graph; they have been moved to the shared section of this file
(`tendstoInProb_pooledAvg` and friends), which was the only obstruction. The proof:

* `tendstoInProb_pooledAvg` gives, for every integrable `f`,
  `N⁻¹ ∑_l f(x_l) → (λ ∫f dP_Y + ∫f dP_Z)/(1+λ)` in probability, through the two block laws
  of large numbers `tendsto_lln_blockY`/`_blockZ` and the deterministic weights
  `m/N → λ/(1+λ)`, `n/N → 1/(1+λ)`. Applied to `f = id` and `f = (·)²` and combined by
  `tendstoInProb_comp`/`_add`, it gives `pooledVar → v̄` in probability
  (`pooledVar_eq` turns the centred sum into second moment minus squared mean, and
  `var_eq_second_sub_sq` identifies the limit as `v̄ = (λ varY + varZ)/(1+λ)`). Dividing by
  the deterministic `v̄` is the first conjunct (`normDefect_eq`).
* For the second conjunct the split is deterministic (`lindebergDefect_le`): with
  `r = √v̄ · √(min(m, N−m))`,
  `Λ ≤ v̄⁻¹ [ (K + |x̄|)/r · pooledVar + 2(1 + x̄²) · N⁻¹ ∑_l x_l² 1{|x_l| ≥ K} ]`
  for every `K ≥ 1` — off the tail `min(1, |x_l − x̄|/r) ≤ (K + |x̄|)/r`, and on the tail
  `(x_l − x̄)² ≤ 2x_l² + 2x̄² ≤ 2(1 + x̄²) x_l²` because `K ≥ 1` forces `x_l² ≥ 1`. The
  first summand is deterministic and `o(1)` on the event `{|x̄ − μ| < 1} ∩ {|v̂ − v̄| < 1}`
  because `r → ∞`; the second is controlled by choosing `K` so that the *limiting* tail
  second moment `(λ ∫_{|t|≥K} t² dP_Y + ∫_{|t|≥K} t² dP_Z)/(1+λ)` is small, which is
  possible by dominated convergence (`tendsto_integral_tailSq`) — the only place where
  `MemLp id 2` is used, and why no moment beyond `L²` is needed. A three-set union bound
  then finishes: `{Λ ≥ η}` is eventually contained in the union of the three failure
  events, each of which has vanishing probability. -/
private lemma tendstoInProb_pooled_hypotheses (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ μ v : ℝ}
    -- USER-INPUT: both sample sizes grow; the asymptotic regime
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: `m/n → λ`, with a nondegenerate limit
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: equal means
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances, both nonzero
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ)
    -- LEAN-ONLY: `v` names the pooled limiting variance
    (hvpos : 0 < v) (hv : v = (lam * varY + varZ) / (1 + lam)) :
    (∀ η > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
        {x | η ≤ normDefect (m k) (n k) v x}) atTop (𝓝 0))
      ∧ (∀ η > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
        {x | η ≤ lindebergDefect (m k) (n k) v x}) atTop (𝓝 0)) := by
  classical
  have hne : (1 : ℝ) + lam ≠ 0 := by positivity
  have hidY : Integrable (fun t : ℝ => t) PY := by simpa using! hYL2.integrable (by norm_num)
  have hidZ : Integrable (fun t : ℝ => t) PZ := by simpa using! hZL2.integrable (by norm_num)
  have hsqY : Integrable (fun t : ℝ => t ^ 2) PY := by simpa using hYL2.integrable_sq
  have hsqZ : Integrable (fun t : ℝ => t ^ 2) PZ := by simpa using hZL2.integrable_sq
  have hsv : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.mpr hvpos
  -- (1) the pooled mean converges in probability to the common mean `μ`
  have hbar : ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |pooledMean (m k) (n k) x - μ|}) atTop (𝓝 0) := by
    intro ε hε
    have h := tendstoInProb_pooledAvg PY PZ m n hm hn hratio hlam (fun t : ℝ => t)
      measurable_id hidY hidZ ε hε
    have hlim : lam / (1 + lam) * μ + 1 / (1 + lam) * μ = μ := by
      field_simp
      ring
    rw [hmeanY, hmeanZ, hlim] at h
    simpa only [pooledMean] using h
  -- (2) the pooled second moment
  have hA : ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |((m k + n k : ℕ) : ℝ)⁻¹ * (∑ l, x l ^ 2)
        - (lam / (1 + lam) * (∫ t, t ^ 2 ∂PY) + 1 / (1 + lam) * ∫ t, t ^ 2 ∂PZ)|})
      atTop (𝓝 0) := fun ε hε =>
    tendstoInProb_pooledAvg PY PZ m n hm hn hratio hlam (fun t : ℝ => t ^ 2) (by fun_prop)
      hsqY hsqZ ε hε
  have hneg := tendstoInProb_comp (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
    (φ := fun y : ℝ => -(y ^ 2)) (by fun_prop) hbar
  have hadd := tendstoInProb_add (P := fun k => twoSampleLaw (m k) (n k) PY PZ) hA hneg
  have hL2 : (lam / (1 + lam) * (∫ t, t ^ 2 ∂PY) + 1 / (1 + lam) * ∫ t, t ^ 2 ∂PZ)
      + -(μ ^ 2) = v := by
    have hY' : (∫ t, t ^ 2 ∂PY) = varY + μ ^ 2 := by
      have h := var_eq_second_sub_sq hYL2 hmeanY hvarY; linarith
    have hZ' : (∫ t, t ^ 2 ∂PZ) = varZ + μ ^ 2 := by
      have h := var_eq_second_sub_sq hZL2 hmeanZ hvarZ; linarith
    rw [hY', hZ', hv]
    field_simp
    ring
  -- (3) the pooled variance converges in probability to `v̄`
  have hSvar : ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |pooledVar (m k) (n k) x - v|}) atTop (𝓝 0) := by
    intro ε hε
    refine (hadd ε hε).congr' ?_
    filter_upwards [hm.eventually_gt_atTop 0] with k hk
    have hmn : 0 < m k + n k := lt_of_lt_of_le hk (Nat.le_add_right _ _)
    rw [hL2]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, pooledVar_eq hmn x]
  refine ⟨?_, ?_⟩
  · -- **The normalization defect.** Divide the pooled variance by the deterministic `v̄`.
    intro η hη
    have hc := tendstoInProb_const_mul (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
      (c := fun _ : ℕ => v⁻¹) (cl := v⁻¹) tendsto_const_nhds hSvar η hη
    refine hc.congr fun k => ?_
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, normDefect_eq hvpos x, inv_mul_cancel₀ hvpos.ne']
  · -- **The Lindeberg defect.**
    intro η hη
    set C : ℝ := 2 * v⁻¹ * (1 + (|μ| + 1) ^ 2) with hCdef
    have hCpos : (0 : ℝ) < C := by rw [hCdef]; positivity
    -- choose the truncation level `K` so that the limiting tail second moment is small
    have htail : Tendsto (fun j : ℕ =>
        C * (lam / (1 + lam) * (∫ t, tailSq (j : ℝ) t ∂PY)
          + 1 / (1 + lam) * ∫ t, tailSq (j : ℝ) t ∂PZ)) atTop (𝓝 0) := by
      have hY := tendsto_integral_tailSq hsqY
      have hZ := tendsto_integral_tailSq hsqZ
      have h := ((hY.const_mul (lam / (1 + lam))).add
        (hZ.const_mul (1 / (1 + lam)))).const_mul C
      simpa using h
    obtain ⟨K, hK1, hKlt⟩ : ∃ K : ℕ, 1 ≤ (K : ℝ) ∧
        C * (lam / (1 + lam) * (∫ t, tailSq (K : ℝ) t ∂PY)
          + 1 / (1 + lam) * ∫ t, tailSq (K : ℝ) t ∂PZ) < η / 4 := by
      have hev := htail.eventually (eventually_lt_nhds (show (0 : ℝ) < η / 4 by positivity))
      obtain ⟨K, hK⟩ := (hev.and (eventually_ge_atTop 1)).exists
      exact ⟨K, by exact_mod_cast hK.2, hK.1⟩
    set cK : ℝ := lam / (1 + lam) * (∫ t, tailSq (K : ℝ) t ∂PY)
      + 1 / (1 + lam) * ∫ t, tailSq (K : ℝ) t ∂PZ with hcKdef
    set ρ : ℝ := η / (4 * C) with hρdef
    have hρpos : (0 : ℝ) < ρ := by rw [hρdef]; positivity
    have hCρ : C * ρ = η / 4 := by
      rw [hρdef]; field_simp
    -- the three vanishing events
    have hE1 := hbar 1 one_pos
    have hE2 := hSvar 1 one_pos
    have hE3 := tendstoInProb_pooledAvg PY PZ m n hm hn hratio hlam (tailSq (K : ℝ))
      (measurable_tailSq _) (integrable_tailSq _ hsqY) (integrable_tailSq _ hsqZ) ρ hρpos
    rw [← hcKdef] at hE3
    -- Hájek's scale tends to infinity
    have hRtop : Tendsto (fun k => Real.sqrt (min (m k : ℝ)
        (((m k + n k : ℕ) : ℝ) - (m k : ℝ)))) atTop atTop := by
      have hmR : Tendsto (fun k => (m k : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hm
      have hnR : Tendsto (fun k => (n k : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hn
      have hmin : Tendsto (fun k => min (m k : ℝ) (((m k + n k : ℕ) : ℝ) - (m k : ℝ)))
          atTop atTop := by
        refine tendsto_atTop.2 fun b => ?_
        filter_upwards [tendsto_atTop.1 hmR b, tendsto_atTop.1 hnR b] with k h1 h2
        have hcast : ((m k + n k : ℕ) : ℝ) - (m k : ℝ) = (n k : ℝ) := by push_cast; ring
        rw [hcast]
        exact le_min h1 h2
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [tendsto_atTop.1 hmin (max b 0 ^ 2)] with k hk
      calc b ≤ max b 0 := le_max_left _ _
        _ = Real.sqrt (max b 0 ^ 2) := (Real.sqrt_sq (le_max_right _ _)).symm
        _ ≤ _ := Real.sqrt_le_sqrt hk
    have hRpos := hRtop.eventually_gt_atTop 0
    have hD : Tendsto (fun k => v⁻¹ * (((K : ℝ) + (|μ| + 1)) /
        (Real.sqrt v * Real.sqrt (min (m k : ℝ) (((m k + n k : ℕ) : ℝ) - (m k : ℝ))))
          * (v + 1))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun k => (Real.sqrt (min (m k : ℝ)
          (((m k + n k : ℕ) : ℝ) - (m k : ℝ))))⁻¹) atTop (𝓝 0) := hRtop.inv_tendsto_atTop
      have h1 := h0.const_mul (v⁻¹ * (((K : ℝ) + (|μ| + 1)) * (Real.sqrt v)⁻¹) * (v + 1))
      rw [mul_zero] at h1
      refine h1.congr fun k => ?_
      rw [div_eq_mul_inv, mul_inv]
      ring
    have hDsmall := hD.eventually (eventually_lt_nhds (show (0 : ℝ) < η / 2 by positivity))
    -- the union bound, eventually in `k`
    have hbound : ∀ᶠ k in atTop, (twoSampleLaw (m k) (n k) PY PZ).real
        {x : Fin (m k + n k) → ℝ | η ≤ lindebergDefect (m k) (n k) v x}
        ≤ ((twoSampleLaw (m k) (n k) PY PZ).real
              {x : Fin (m k + n k) → ℝ | 1 ≤ |pooledMean (m k) (n k) x - μ|}
            + (twoSampleLaw (m k) (n k) PY PZ).real
              {x : Fin (m k + n k) → ℝ | 1 ≤ |pooledVar (m k) (n k) x - v|})
          + (twoSampleLaw (m k) (n k) PY PZ).real
              {x : Fin (m k + n k) → ℝ | ρ ≤ |((m k + n k : ℕ) : ℝ)⁻¹ *
                (∑ l, tailSq (K : ℝ) (x l)) - cK|} := by
      filter_upwards [hDsmall, hRpos] with k hk hRk
      have hsub : {x : Fin (m k + n k) → ℝ | η ≤ lindebergDefect (m k) (n k) v x}
          ⊆ ({x : Fin (m k + n k) → ℝ | 1 ≤ |pooledMean (m k) (n k) x - μ|} ∪
              {x : Fin (m k + n k) → ℝ | 1 ≤ |pooledVar (m k) (n k) x - v|}) ∪
            {x : Fin (m k + n k) → ℝ | ρ ≤ |((m k + n k : ℕ) : ℝ)⁻¹ *
              (∑ l, tailSq (K : ℝ) (x l)) - cK|} := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
        obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
        have hbabs : |pooledMean (m k) (n k) x| ≤ |μ| + 1 := by
          have := abs_sub_abs_le_abs_sub (pooledMean (m k) (n k) x) μ
          linarith
        have hb2 : pooledMean (m k) (n k) x ^ 2 ≤ (|μ| + 1) ^ 2 := by
          nlinarith [abs_nonneg (pooledMean (m k) (n k) x),
            sq_abs (pooledMean (m k) (n k) x), abs_nonneg μ]
        have hWnn : 0 ≤ pooledVar (m k) (n k) x := pooledVar_nonneg _ _ x
        have hWle : pooledVar (m k) (n k) x ≤ v + 1 := by
          have := abs_lt.1 h2; linarith [this.2]
        have hTnn : (0 : ℝ) ≤ ((m k + n k : ℕ) : ℝ)⁻¹ * ∑ l, tailSq (K : ℝ) (x l) :=
          mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => tailSq_nonneg _ _)
        have hTle : ((m k + n k : ℕ) : ℝ)⁻¹ * (∑ l, tailSq (K : ℝ) (x l)) ≤ cK + ρ := by
          have := abs_lt.1 h3; linarith [this.2]
        have hmain := lindebergDefect_le (m := m k) (n := n k) hvpos hK1 hRk x
        have hden : (0 : ℝ) < Real.sqrt v *
            Real.sqrt (min (m k : ℝ) (((m k + n k : ℕ) : ℝ) - (m k : ℝ))) := mul_pos hsv hRk
        have hpart1 : ((K : ℝ) + |pooledMean (m k) (n k) x|) /
              (Real.sqrt v * Real.sqrt (min (m k : ℝ) (((m k + n k : ℕ) : ℝ) - (m k : ℝ))))
                * pooledVar (m k) (n k) x
            ≤ ((K : ℝ) + (|μ| + 1)) /
              (Real.sqrt v * Real.sqrt (min (m k : ℝ) (((m k + n k : ℕ) : ℝ) - (m k : ℝ))))
                * (v + 1) := by
          refine mul_le_mul ?_ hWle hWnn ?_
          · gcongr
          · have hKb : (0 : ℝ) ≤ (K : ℝ) + (|μ| + 1) := by
              have := abs_nonneg μ; linarith
            positivity
        have hpart2 : 2 * (1 + pooledMean (m k) (n k) x ^ 2) *
              (((m k + n k : ℕ) : ℝ)⁻¹ * ∑ l, tailSq (K : ℝ) (x l))
            ≤ 2 * (1 + (|μ| + 1) ^ 2) * (cK + ρ) := by
          refine mul_le_mul (by linarith) hTle hTnn (by positivity)
        have hCval : v⁻¹ * (2 * (1 + (|μ| + 1) ^ 2) * (cK + ρ)) = C * (cK + ρ) := by
          rw [hCdef]; ring
        have hvinv : (0 : ℝ) ≤ v⁻¹ := by positivity
        have hfinal : lindebergDefect (m k) (n k) v x
            ≤ v⁻¹ * (((K : ℝ) + (|μ| + 1)) /
                (Real.sqrt v *
                  Real.sqrt (min (m k : ℝ) (((m k + n k : ℕ) : ℝ) - (m k : ℝ)))) * (v + 1))
              + C * (cK + ρ) := by
          refine hmain.trans ?_
          rw [mul_add, ← hCval]
          exact add_le_add (mul_le_mul_of_nonneg_left hpart1 hvinv)
            (mul_le_mul_of_nonneg_left hpart2 hvinv)
        have hsplit : C * (cK + ρ) = C * cK + C * ρ := by ring
        rw [hCρ] at hsplit
        linarith
      calc (twoSampleLaw (m k) (n k) PY PZ).real
            {x : Fin (m k + n k) → ℝ | η ≤ lindebergDefect (m k) (n k) v x}
          ≤ (twoSampleLaw (m k) (n k) PY PZ).real
              (({x : Fin (m k + n k) → ℝ | 1 ≤ |pooledMean (m k) (n k) x - μ|} ∪
                {x : Fin (m k + n k) → ℝ | 1 ≤ |pooledVar (m k) (n k) x - v|}) ∪
              {x : Fin (m k + n k) → ℝ | ρ ≤ |((m k + n k : ℕ) : ℝ)⁻¹ *
                (∑ l, tailSq (K : ℝ) (x l)) - cK|}) :=
            measureReal_mono hsub (measure_ne_top _ _)
        _ ≤ (twoSampleLaw (m k) (n k) PY PZ).real
              ({x : Fin (m k + n k) → ℝ | 1 ≤ |pooledMean (m k) (n k) x - μ|} ∪
                {x : Fin (m k + n k) → ℝ | 1 ≤ |pooledVar (m k) (n k) x - v|})
            + (twoSampleLaw (m k) (n k) PY PZ).real
              {x : Fin (m k + n k) → ℝ | ρ ≤ |((m k + n k : ℕ) : ℝ)⁻¹ *
                (∑ l, tailSq (K : ℝ) (x l)) - cK|} := measureReal_union_le _ _
        _ ≤ _ := add_le_add (measureReal_union_le _ _) le_rfl
    refine squeeze_zero' (Eventually.of_forall fun k => measureReal_nonneg) hbound ?_
    simpa using (hE1.add hE2).add hE3

/-! ### The permutation limit

The bivariate statement is reduced to a **scalar** one: the `Asymptotics` converse
`weakConverges_randPairLaw_of_randDist_tendstoInProb` says that convergence in probability of
the (one-permutation) randomization distribution to a limiting c.d.f. already forces the
two-permutation joint law to converge to the *product* — the asymptotic independence is
automatic and needs no separate argument. So the whole content is the scalar core below. -/

/-- **The scalar core of the two-sample permutation limit.** The randomization distribution
of the unstudentized statistic converges in probability to the c.d.f. of `N(0, τ²)`, with the
permutation scale `τ² = λ σ²(P_Y) + σ²(P_Z)`.

STATUS (wave 8): PROVED here, over the single named brick
`tendstoInProb_pooled_hypotheses` above (a pure law-of-large-numbers statement about the
pooled empirical moments, with a fully re-derived route note). The three steps that used to
be the mathematical content are now all discharged:

(1) *The combinatorial central limit theorem*, `ForMathlib/CombinatorialCLT`, is consumed
    through its **moving-threshold** form `tendsto_perm_cdf_blockSum_varying` (proved above),
    because the two-sample threshold `t·mn/(√m·N)` carries the moving sample sizes.
(2) *The identification of the statistic.* `randDist_twoSampleMeanDiff_eq_std` (proved above)
    writes the randomization distribution, exactly and at every finite `k`, as the group
    average of the indicator of a **standardized** permuted block sum of the centred pooled
    data, with threshold `θ_k = t√(n/N)/√v̄` in units of `blockSumScale`; and `θ_k → t/τ`
    because `n/N → 1/(1+λ)` and `v̄ = τ²/(1+λ)`.
(3) *The deterministic-array-to-random-array transfer.* `tendstoInProb_of_deterministic`
    (proved above) is the abstract form of the argument the wave-6 note sketched: it takes
    two nonnegative hypothesis functionals vanishing in probability together with the
    deterministic statement along arbitrary subsequences, and returns convergence in
    probability. No measurable selection is involved, only existence. The `ε`-indexed Hájek
    Lindeberg family is compressed into the single functional `lindebergDefect` by
    `lindeberg_le_lindebergDefect`, which is what makes the transfer applicable.

What is left is therefore only the *in-probability* control of the pooled empirical moments,
isolated in `tendstoInProb_pooled_hypotheses`; see its own note. -/
private lemma randDist_twoSample_tendstoInProb_core (PY PZ : Measure ℝ)
    [IsProbabilityMeasure PY] [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ τ μ : ℝ}
    -- USER-INPUT: both sample sizes grow; the asymptotic regime
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: the sample sizes are balanced in the limit, `m/n → λ`
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: the two populations have the same mean
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances, both nonzero
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ)
    -- LEAN-ONLY: `τ` names the positive square root of the permutation variance
    (hτpos : 0 < τ) (hτ : τ ^ 2 = lam * varY + varZ) (t : ℝ) :
    TendstoInProbTriangular (fun k => twoSampleLaw (m k) (n k) PY PZ)
      (fun k x => randDist (Equiv.Perm (Fin (m k + n k)))
        (twoSampleMeanDiff (m k) (n k)) x t)
      (cdf (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ))) t) := by
  classical
  have h1lam : (0 : ℝ) < 1 + lam := by linarith
  have hnum : (0 : ℝ) < lam * varY + varZ := by positivity
  set v : ℝ := (lam * varY + varZ) / (1 + lam) with hvdef
  have hvpos : (0 : ℝ) < v := by rw [hvdef]; positivity
  have hsvpos : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.2 hvpos
  have hs1lam : (0 : ℝ) < Real.sqrt (1 + lam) := Real.sqrt_pos.2 h1lam
  have hsv : Real.sqrt v * Real.sqrt (1 + lam) = τ := by
    rw [← Real.sqrt_mul hvpos.le, hvdef, div_mul_cancel₀ _ h1lam.ne', ← hτ,
      Real.sqrt_sq hτpos.le]
  -- the two hypothesis functionals vanish in probability
  obtain ⟨hnorm, hlindP⟩ := tendstoInProb_pooled_hypotheses PY PZ m n hm hn hratio hlam
    hYL2 hZL2 hmeanY hmeanZ hvarY hvarZ hvarYpos hvarZpos hvpos hvdef
  -- the moving threshold converges to `t/τ`
  have hθlim : Tendsto (fun k => t * Real.sqrt ((n k : ℝ) / ((m k + n k : ℕ) : ℝ))
      / Real.sqrt v) atTop (𝓝 (t / τ)) := by
    have hw := tendsto_weightZ m n hn hratio hlam
    have hsq : Tendsto (fun k => Real.sqrt ((n k : ℝ) / ((m k + n k : ℕ) : ℝ))) atTop
        (𝓝 (Real.sqrt (1 / (1 + lam)))) :=
      (Real.continuous_sqrt.continuousAt (x := 1 / (1 + lam))).tendsto.comp hw
    have hlim := (hsq.const_mul t).div_const (Real.sqrt v)
    have hval : t * Real.sqrt (1 / (1 + lam)) / Real.sqrt v = t / τ := by
      rw [one_div, Real.sqrt_inv, ← hsv]
      field_simp
    rwa [hval] at hlim
  -- the limit c.d.f. is the standard normal one, rescaled
  rw [cdf_gaussianReal_scale hτpos t]
  -- the transfer
  refine tendstoInProb_of_deterministic (fun k => twoSampleLaw (m k) (n k) PY PZ)
    (fun k => normDefect (m k) (n k) v) (fun k => lindebergDefect (m k) (n k) v)
    (fun k x => randDist (Equiv.Perm (Fin (m k + n k)))
      (twoSampleMeanDiff (m k) (n k)) x t)
    (cdf (gaussianReal 0 1) (t / τ))
    (fun k x => abs_nonneg _) (fun k x => lindebergDefect_nonneg _ _ _ _)
    hnorm hlindP ?_
  intro φ hφ y hAlim hBlim
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hmφ : Tendsto (fun j => (m (φ j) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (hm.comp hφtop)
  have hnφ : Tendsto (fun j => (n (φ j) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (hn.comp hφtop)
  have hNmφ : Tendsto (fun j => ((m (φ j) + n (φ j) : ℕ) : ℝ) - (m (φ j) : ℝ))
      atTop atTop := by
    refine hnφ.congr fun j => ?_
    push_cast
    ring
  -- the standardized populations are centred
  have hcent : ∀ j, ∑ l, pooledStd (m (φ j)) (n (φ j)) v (y j) l = 0 := by
    intro j
    simp only [pooledStd, ← Finset.mul_sum, sum_pooledCentred', mul_zero]
  -- their second moment tends to one
  have hvarj : Tendsto (fun j => ((m (φ j) + n (φ j) : ℕ) : ℝ)⁻¹ *
      ∑ l, pooledStd (m (φ j)) (n (φ j)) v (y j) l ^ 2) atTop (𝓝 1) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa only [Real.dist_eq, normDefect] using hAlim
  -- and they satisfy Hájek's Lindeberg condition, member by member
  have hlindj : ∀ ε > (0 : ℝ), Tendsto (fun j => ((m (φ j) + n (φ j) : ℕ) : ℝ)⁻¹ *
      ∑ l, (if ε * Real.sqrt (min (m (φ j) : ℝ)
                (((m (φ j) + n (φ j) : ℕ) : ℝ) - (m (φ j) : ℝ)))
              ≤ |pooledStd (m (φ j)) (n (φ j)) v (y j) l|
            then pooledStd (m (φ j)) (n (φ j)) v (y j) l ^ 2 else 0)) atTop (𝓝 0) := by
    intro ε hε
    have hgo : Tendsto (fun j => (min 1 ε)⁻¹ *
        lindebergDefect (m (φ j)) (n (φ j)) v (y j)) atTop (𝓝 0) := by
      have h := hBlim.const_mul ((min 1 ε)⁻¹)
      rwa [mul_zero] at h
    refine squeeze_zero' (Eventually.of_forall fun j => ?_) ?_ hgo
    · refine mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => ?_)
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl
    · filter_upwards [hmφ.eventually_gt_atTop 0, hNmφ.eventually_gt_atTop 0] with j h1 h2
      have hR : (0 : ℝ) < Real.sqrt (min (m (φ j) : ℝ)
          (((m (φ j) + n (φ j) : ℕ) : ℝ) - (m (φ j) : ℝ))) := Real.sqrt_pos.2 (lt_min h1 h2)
      exact lindeberg_le_lindebergDefect _ hR hε
  -- the combinatorial central limit theorem at the moving threshold
  have hmain := tendsto_perm_cdf_blockSum_varying
    (N := fun j => m (φ j) + n (φ j)) (m := fun j => m (φ j))
    (fun j => Fin.castAdd (n (φ j))) (fun j => Fin.castAdd_injective _ _)
    (fun j => pooledStd (m (φ j)) (n (φ j)) v (y j)) hcent hmφ hNmφ hvarj hlindj
    (hθlim.comp hφtop)
  refine hmain.congr' ?_
  filter_upwards [(hm.comp hφtop).eventually_gt_atTop 0,
    (hn.comp hφtop).eventually_gt_atTop 0] with j hmj hnj
  exact (randDist_twoSampleMeanDiff_eq_std (m (φ j)) (n (φ j)) hmj hnj hvpos (y j) t).symm

/-- **Two-sample permutation central limit theorem.** With `m/n → λ ∈ (0, ∞)`, finite
nonzero variances and equal means, the statistic evaluated at two independent uniform
random permutations converges jointly in law to a bivariate normal with **independent,
identically distributed** marginals `N(0, τ²)`, where
$$ \tau^2 = \lambda\,\sigma^2(P_Y) + \sigma^2(P_Z) . $$
This is exactly the joint hypothesis consumed by the general asymptotic randomization
theorem. -/
theorem weakConverges_randPairLaw_twoSample (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ τ μ : ℝ}
    -- USER-INPUT: both sample sizes grow; the asymptotic regime
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: the sample sizes are balanced in the limit, `m/n → λ`
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam))
    -- USER-INPUT: a nondegenerate limiting ratio
    (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: the two populations have the same mean; the null hypothesis under test
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    -- USER-INPUT: both variances are nonzero
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ)
    -- LEAN-ONLY: `τ` names the positive square root of the permutation variance, so the
    -- limit can be written as a Gaussian with an `ℝ≥0` variance parameter
    (hτpos : 0 < τ) (hτ : τ ^ 2 = lam * varY + varZ) :
    WeakConverges
      (fun k => randPairLaw (Equiv.Perm (Fin (m k + n k)))
        (twoSampleMeanDiff (m k) (n k)) (twoSampleLaw (m k) (n k) PY PZ))
      ((gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ))).prod
        (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ)))) := by
  -- The asymptotic independence of the two permutations is not proved here: the converse
  -- engine `weakConverges_randPairLaw_of_randDist_tendstoInProb` derives the product limit
  -- from the scalar convergence in probability of `randDist` alone. So the whole statement
  -- reduces to `randDist_twoSample_tendstoInProb_core` above.
  exact weakConverges_randPairLaw_of_randDist_tendstoInProb
    (G := fun k => Equiv.Perm (Fin (m k + n k)))
    (fun k => twoSampleLaw (m k) (n k) PY PZ)
    (fun k => twoSampleMeanDiff (m k) (n k))
    (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ)))
    (fun k => measurable_twoSampleMeanDiff (m k) (n k))
    (fun k g => measurable_perm_smul _ g)
    (fun u _ => randDist_twoSample_tendstoInProb_core PY PZ m n hm hn hratio hlam hYL2 hZL2
      hmeanY hmeanZ hvarY hvarZ hvarYpos hvarZpos hτpos hτ u)

/-- **Consequence: the randomization distribution converges to `Φ(·/τ)`.** -/
theorem randDist_twoSample_tendstoInProb (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ τ μ : ℝ}
    -- USER-INPUT: both sample sizes grow
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: `m/n → λ`, with a nondegenerate limit
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: equal means; the null hypothesis under test
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances, both nonzero
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ)
    -- LEAN-ONLY: positive square root of the permutation variance
    (hτpos : 0 < τ) (hτ : τ ^ 2 = lam * varY + varZ) (t : ℝ) :
    TendstoInProbTriangular (fun k => twoSampleLaw (m k) (n k) PY PZ)
      (fun k x => randDist (Equiv.Perm (Fin (m k + n k)))
        (twoSampleMeanDiff (m k) (n k)) x t)
      (cdf (gaussianReal 0 1) (t / τ)) := by
  -- Feed the permutation bivariate CLT into the forward engine `randDist_tendstoInProb_cdf`,
  -- discharging action measurability with `measurable_perm_smul` and continuity of the
  -- Gaussian c.d.f. with `continuousAt_cdf_of_noAtoms`, then rescale via `cdf_gaussianReal_scale`.
  have hjoint := weakConverges_randPairLaw_twoSample PY PZ m n hm hn hratio hlam hYL2 hZL2
    hmeanY hmeanZ hvarY hvarZ hvarYpos hvarZpos hτpos hτ
  have hvne : NNReal.mk (τ ^ 2) (sq_nonneg τ) ≠ 0 :=
    NNReal.coe_ne_zero.mp (by rw [NNReal.coe_mk]; positivity)
  haveI : NullSingletonClass (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ))) := nullSingletonClass_gaussianReal hvne
  have hcont : ContinuousAt (cdf (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ)))) t :=
    continuousAt_cdf_of_noAtoms _ t
  have hmain := randDist_tendstoInProb_cdf (G := fun k => Equiv.Perm (Fin (m k + n k)))
    (fun k => twoSampleLaw (m k) (n k) PY PZ) (fun k => twoSampleMeanDiff (m k) (n k))
    (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ)))
    (fun k => measurable_twoSampleMeanDiff (m k) (n k))
    (fun k g => measurable_perm_smul _ g) hjoint hcont
  rwa [cdf_gaussianReal_scale hτpos t] at hmain

/-! ### Varying-exponent power limits

The unconditional two-sample limit needs `(1 + gₖ)^{Nₖ} → exp z` with the exponent `Nₖ` an
*arbitrary* sequence tending to infinity (the second sample size `n k`), whereas Mathlib's
`Complex.tendsto_one_add_pow_exp_of_tendsto` forces the exponent to be the index itself.
That, together with a varying characteristic-function argument, is supplied here. -/

/-- **Varying-exponent form of `Complex.tendsto_one_add_pow_exp_of_tendsto`.** If the
exponents `N k` tend to infinity and `N k · g k → z`, then `(1 + g k) ^ (N k) → exp z`. -/
private lemma tendsto_one_add_pow_of_tendsto_nat_mul {N : ℕ → ℕ} {g : ℕ → ℂ} {z : ℂ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop)
    (hg : Tendsto (fun k => (N k : ℂ) * g k) atTop (𝓝 z)) :
    Tendsto (fun k => (1 + g k) ^ (N k)) atTop (𝓝 (Complex.exp z)) := by
  have hNne : ∀ᶠ k in atTop, (N k : ℂ) ≠ 0 := by
    filter_upwards [hN.eventually_gt_atTop 0] with k hk
    have hk0 : N k ≠ 0 := by
      intro h
      rw [h] at hk
      simp at hk
    exact_mod_cast Nat.cast_ne_zero.2 hk0
  have hinv : Tendsto (fun k => ((N k : ℂ))⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ((N k : ℝ))⁻¹) atTop (𝓝 0) := hN.inv_tendsto_atTop
    have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h1
    simp only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zero] at h2
    exact h2
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have h := hinv.mul hg
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [hNne] with k hk
    exact inv_mul_cancel_left₀ hk (g k)
  have hgn : Tendsto (fun k => ‖g k‖) atTop (𝓝 0) := by simpa using hg0.norm
  have hsmall : ∀ᶠ k in atTop, ‖g k‖ < 1 / 2 :=
    hgn.eventually (eventually_lt_nhds (by norm_num))
  have hdiff : Tendsto (fun k => (N k : ℂ) * (Complex.log (1 + g k) - g k)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun k => ‖(N k : ℂ) * g k‖ * ‖g k‖) ?_ ?_
    · filter_upwards [hsmall] with k hk
      have hk1 : ‖g k‖ < 1 := hk.trans (by norm_num)
      have hbd := Complex.norm_log_one_add_sub_self_le hk1
      have hinv2 : (1 - ‖g k‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      have hstep : ‖Complex.log (1 + g k) - g k‖ ≤ ‖g k‖ ^ 2 := by
        refine hbd.trans ?_
        nlinarith [sq_nonneg ‖g k‖, norm_nonneg (g k)]
      calc ‖(N k : ℂ) * (Complex.log (1 + g k) - g k)‖
          = (N k : ℝ) * ‖Complex.log (1 + g k) - g k‖ := by
            rw [norm_mul]; simp
        _ ≤ (N k : ℝ) * ‖g k‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)
        _ = ‖(N k : ℂ) * g k‖ * ‖g k‖ := by rw [norm_mul]; simp; ring
    · have h := hg.norm.mul hgn
      simpa using h
  have hlog : Tendsto (fun k => (N k : ℂ) * Complex.log (1 + g k)) atTop (𝓝 z) := by
    have h := hg.add hdiff
    rw [add_zero] at h
    exact h.congr fun k => by ring
  have hexp := (Complex.continuous_exp.tendsto z).comp hlog
  refine hexp.congr' ?_
  filter_upwards [hsmall] with k hk
  have h1 : (1 : ℂ) + g k ≠ 0 := by
    intro h
    have hgk : g k = -1 := by linear_combination h
    rw [hgk] at hk
    norm_num at hk
  simp only [Function.comp_apply]
  rw [Complex.exp_nat_mul, Complex.exp_log h1]

/-- **Characteristic-function powers with varying exponent and varying argument.** For a
centred law `Q` with second moment `v > 0`, exponents `N k → ∞` and arguments with
`N k · (s k)² → c`, one has `(charFun Q (s k)) ^ (N k) → exp(−v c / 2)`. Both the exponent
and the argument move with `k`, which is what the two-sample statistic requires. -/
private lemma tendsto_charFun_pow {Q : Measure ℝ} [IsProbabilityMeasure Q] {v c : ℝ}
    (hQ0 : ∫ y, y ∂Q = 0) (hQ2 : ∫ y, y ^ 2 ∂Q = v) (hv : 0 < v)
    {N : ℕ → ℕ} (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop)
    {s : ℕ → ℝ} (hs : Tendsto (fun k => (N k : ℝ) * s k ^ 2) atTop (𝓝 c)) :
    Tendsto (fun k => charFun Q (s k) ^ (N k)) atTop
      (𝓝 (Complex.exp (-((v * c : ℝ) : ℂ) / 2))) := by
  obtain ⟨σ, hσpos, hσsq⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ^ 2 = v :=
    ⟨Real.sqrt v, Real.sqrt_pos.2 hv, Real.sq_sqrt hv.le⟩
  -- Standardise: `X y = y / σ` has mean `0` and variance `1` under `Q`.
  have hXm : Measurable (fun y : ℝ => y / σ) := by fun_prop
  have h0 : ∫ y, (fun y : ℝ => y / σ) y ∂Q = 0 := by
    simp only [integral_div, hQ0, zero_div]
  have h1 : ∫ y, ((fun y : ℝ => y / σ) ^ 2) y ∂Q = 1 := by
    simp only [Pi.pow_apply, div_pow, integral_div, hQ2, hσsq]
    exact div_self hv.ne'
  have hR : ∀ w : ℝ, charFun Q w = charFun (Q.map (fun y : ℝ => y / σ)) (σ * w) := by
    intro w
    have h := charFun_map_mul_comp (μ := Q) (f := fun y : ℝ => y / σ) hXm.aemeasurable σ w
    have hid : (fun y : ℝ => σ * (y / σ)) = id := by
      funext y
      change σ * (y / σ) = y
      field_simp
    rw [hid, Measure.map_id] at h
    exact h
  -- The arguments tend to `0`.
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have hsq : Tendsto (fun k => s k ^ 2) atTop (𝓝 0) := by
      have h := hs.mul hN.inv_tendsto_atTop
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [hN.eventually_gt_atTop 0] with k hk
      simp only [Pi.inv_apply]
      field_simp
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq
    simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using h
  have hw0 : Tendsto (fun k => σ * s k) atTop (𝓝 0) := by
    simpa using hs0.const_mul σ
  have hNw : Tendsto (fun k => (N k : ℝ) * (σ * s k) ^ 2) atTop (𝓝 (v * c)) := by
    have h : Tendsto (fun k => σ ^ 2 * ((N k : ℝ) * s k ^ 2)) atTop (𝓝 (σ ^ 2 * c)) :=
      hs.const_mul _
    rw [hσsq] at h
    refine h.congr fun k => ?_
    rw [← hσsq]
    ring
  -- Second-order Taylor expansion of the characteristic function at the moving argument.
  have hlittle := (taylor_charFun_two (P := Q) (X := fun y : ℝ => y / σ)
    hXm.aemeasurable h0 h1).comp_tendsto hw0
  -- The rescaled remainder is negligible against the exponent.
  have hB : Tendsto (fun k => (N k : ℂ) * (charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) -
      (1 - ((σ * s k : ℝ) : ℂ) ^ 2 / 2))) atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hMpos : (0 : ℝ) < |v * c| + 1 := by positivity
    have hbound := hlittle.def (show (0 : ℝ) < ε / (2 * (|v * c| + 1)) by positivity)
    have hAle : ∀ᶠ k in atTop, (N k : ℝ) * (σ * s k) ^ 2 ≤ |v * c| + 1 := by
      have hlt : v * c < |v * c| + 1 := lt_of_le_of_lt (le_abs_self _) (by linarith)
      filter_upwards [hNw.eventually (eventually_lt_nhds hlt)] with k hk using hk.le
    filter_upwards [hbound, hAle] with k hk hkA
    have hnn : (0 : ℝ) ≤ (N k : ℝ) := Nat.cast_nonneg _
    have hkey : (N k : ℝ) * ‖charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) -
        (1 - ((σ * s k : ℝ) : ℂ) ^ 2 / 2)‖
        ≤ ε / (2 * (|v * c| + 1)) * ((N k : ℝ) * (σ * s k) ^ 2) := by
      have := mul_le_mul_of_nonneg_left hk hnn
      calc (N k : ℝ) * ‖charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) -
              (1 - ((σ * s k : ℝ) : ℂ) ^ 2 / 2)‖
          ≤ (N k : ℝ) * (ε / (2 * (|v * c| + 1)) * ‖(σ * s k) ^ 2‖) := this
        _ = ε / (2 * (|v * c| + 1)) * ((N k : ℝ) * (σ * s k) ^ 2) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (σ * s k))]; ring
    have hfin : ε / (2 * (|v * c| + 1)) * ((N k : ℝ) * (σ * s k) ^ 2) < ε := by
      have hcpos : (0 : ℝ) < ε / (2 * (|v * c| + 1)) := by positivity
      have := mul_le_mul_of_nonneg_left hkA hcpos.le
      have hhalf : ε / (2 * (|v * c| + 1)) * (|v * c| + 1) = ε / 2 := by
        field_simp
      rw [hhalf] at this
      linarith
    calc ‖(N k : ℂ) * (charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) -
            (1 - ((σ * s k : ℝ) : ℂ) ^ 2 / 2))‖
        = (N k : ℝ) * ‖charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) -
            (1 - ((σ * s k : ℝ) : ℂ) ^ 2 / 2)‖ := by rw [norm_mul]; simp
      _ ≤ _ := hkey
      _ < ε := hfin
  -- The quadratic term supplies the exponent.
  have hA : Tendsto (fun k => (N k : ℂ) * (-(((σ * s k : ℝ) : ℂ) ^ 2) / 2)) atTop
      (𝓝 (-((v * c : ℝ) : ℂ) / 2)) := by
    have hreal : Tendsto (fun k => -((N k : ℝ) * (σ * s k) ^ 2) / 2) atTop (𝓝 (-(v * c) / 2)) :=
      hNw.neg.div_const 2
    have h := (Complex.continuous_ofReal.tendsto (-(v * c) / 2)).comp hreal
    simp only [Function.comp_def] at h
    push_cast at h ⊢
    exact h.congr fun k => by ring
  have hgz : Tendsto (fun k => (N k : ℂ) *
      (charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) - 1)) atTop
      (𝓝 (-((v * c : ℝ) : ℂ) / 2)) := by
    have h := hA.add hB
    rw [add_zero] at h
    exact h.congr fun k => by ring
  have hbrick := tendsto_one_add_pow_of_tendsto_nat_mul (N := N)
    (g := fun k => charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) - 1) hN hgz
  refine hbrick.congr fun k => ?_
  rw [hR (s k)]
  congr 1
  ring

/-! ### Linear form of the statistic and the product characteristic function -/

/-- The linear coefficients of the difference-of-means statistic on the pooled data:
`√m/m` on the first block and `−√m/n` on the second. -/
private noncomputable def twoSampleCoef (m n : ℕ) : Fin (m + n) → ℝ :=
  Fin.addCases (motive := fun _ => ℝ) (fun _ => Real.sqrt m * (m : ℝ)⁻¹)
    (fun _ => -(Real.sqrt m * (n : ℝ)⁻¹))

/-- The statistic is the linear form with those coefficients. -/
private lemma twoSampleMeanDiff_eq_sum (m n : ℕ) (x : Fin (m + n) → ℝ) :
    twoSampleMeanDiff m n x = ∑ l, twoSampleCoef m n l * x l := by
  rw [Fin.sum_univ_add]
  simp only [twoSampleCoef, Fin.addCases_left, Fin.addCases_right, twoSampleMeanDiff]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The characteristic function of a linear form of independent coordinates factorizes. -/
private lemma charFun_map_sum_pi {N : ℕ} (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (c : Fin N → ℝ) (t : ℝ) :
    charFun ((Measure.pi ν).map (fun x => ∑ i, c i * x i)) t = ∏ i, charFun (ν i) (c i * t) := by
  have hmeas : ∀ i : Fin N, AEMeasurable (fun x : Fin N → ℝ => c i * x i) (Measure.pi ν) :=
    fun i => Measurable.aemeasurable (by fun_prop)
  have hindep : iIndepFun (fun (i : Fin N) (x : Fin N → ℝ) => c i * x i) (Measure.pi ν) :=
    iIndepFun_pi (X := fun (i : Fin N) (y : ℝ) => c i * y) (fun i => by fun_prop)
  rw [hindep.charFun_map_fun_sum_eq_prod hmeas, Finset.prod_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [charFun_map_mul_comp (measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval ν i).map_eq]

/-- Each coordinate of the pooled family is a probability measure. -/
private lemma isProbabilityMeasure_addCases (m n : ℕ) (PY PZ : Measure ℝ)
    [IsProbabilityMeasure PY] [IsProbabilityMeasure PZ] (i : Fin (m + n)) :
    IsProbabilityMeasure
      (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i) := by
  refine Fin.addCases (m := m) (n := n)
    (motive := fun i => IsProbabilityMeasure
      (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i))
    (fun j => ?_) (fun j => ?_) i
  · first
      | infer_instance
      | · simp only [Fin.addCases_left]; infer_instance
  · first
      | infer_instance
      | · simp only [Fin.addCases_right]; infer_instance

/-- **The exact finite-sample characteristic function of the two-sample statistic.** -/
private lemma charFun_map_twoSampleMeanDiff (m n : ℕ) (PY PZ : Measure ℝ)
    [IsProbabilityMeasure PY] [IsProbabilityMeasure PZ] (t : ℝ) :
    charFun ((twoSampleLaw m n PY PZ).map (twoSampleMeanDiff m n)) t
      = charFun PY (Real.sqrt m * (m : ℝ)⁻¹ * t) ^ m
        * charFun PZ (-(Real.sqrt m * (n : ℝ)⁻¹) * t) ^ n := by
  haveI hfam := isProbabilityMeasure_addCases m n PY PZ
  have hsum : twoSampleMeanDiff m n = fun x => ∑ l, twoSampleCoef m n l * x l :=
    funext fun x => twoSampleMeanDiff_eq_sum m n x
  rw [twoSampleLaw, hsum, charFun_map_sum_pi, Fin.prod_univ_add]
  simp only [twoSampleCoef, Fin.addCases_left, Fin.addCases_right, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-! ### The unconditional limit, for contrast -/

/-- **Unconditional two-sample central limit theorem.** Under the same assumptions the
*true* sampling distribution of the statistic is asymptotically `N(0, s²)` with
$$ s^2 = \sigma^2(P_Y) + \lambda\,\sigma^2(P_Z) , $$
the mirror image of the permutation variance `τ² = λσ²(P_Y) + σ²(P_Z)`. The two agree if
and only if `λ = 1` or `σ²(P_Y) = σ²(P_Z)`; otherwise the permutation test calibrated on
this unstudentized statistic does not have asymptotic level `α` for testing equality of
means. -/
theorem weakConverges_twoSampleMeanDiff (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ s μ : ℝ}
    -- USER-INPUT: both sample sizes grow
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: `m/n → λ`, with a nondegenerate limit
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: equal means; the null hypothesis under test
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances, both nonzero
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ)
    -- LEAN-ONLY: positive square root of the unconditional variance
    (hspos : 0 < s) (hs : s ^ 2 = varY + lam * varZ) :
    WeakConverges
      (fun k => (twoSampleLaw (m k) (n k) PY PZ).map (twoSampleMeanDiff (m k) (n k)))
      (gaussianReal 0 (NNReal.mk (s ^ 2) (sq_nonneg s))) := by
  -- Reduce to characteristic functions, factorize exactly at each finite `k` into the two
  -- per-block powers, recentre both populations at the common mean `μ` (the phase factors
  -- cancel because `mα + nβ = 0`), and apply the varying-exponent power limit to each block.
  classical
  set QY := PY.map (fun y : ℝ => y + (-μ)) with hQYdef
  set QZ := PZ.map (fun y : ℝ => y + (-μ)) with hQZdef
  haveI : IsProbabilityMeasure QY := by
    rw [hQYdef]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure QZ := by
    rw [hQZdef]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hIY : Integrable (fun y : ℝ => y) PY := by simpa using! hYL2.integrable (by norm_num)
  have hIZ : Integrable (fun y : ℝ => y) PZ := by simpa using! hZL2.integrable (by norm_num)
  -- The centred laws have mean `0` and the two population variances.
  have hQY0 : ∫ y, y ∂QY = 0 := by
    rw [hQYdef, integral_map (by fun_prop) (by fun_prop),
      integral_add hIY (integrable_const _), hmeanY]
    simp
  have hQZ0 : ∫ y, y ∂QZ = 0 := by
    rw [hQZdef, integral_map (by fun_prop) (by fun_prop),
      integral_add hIZ (integrable_const _), hmeanZ]
    simp
  have hQY2 : ∫ y, y ^ 2 ∂QY = varY := by
    rw [hQYdef, integral_map (by fun_prop) (by fun_prop)]
    simp only [← sub_eq_add_neg]
    exact hvarY
  have hQZ2 : ∫ y, y ^ 2 ∂QZ = varZ := by
    rw [hQZdef, integral_map (by fun_prop) (by fun_prop)]
    simp only [← sub_eq_add_neg]
    exact hvarZ
  -- Recentring only multiplies the characteristic function by a phase.
  have hPYchar : ∀ w : ℝ,
      charFun PY w = charFun QY w * Complex.exp ((μ : ℂ) * (w : ℂ) * Complex.I) := by
    intro w
    have hinner : (inner ℝ (-μ) w : ℝ) = -(μ * w) := by
      have h0 : (inner ℝ (-μ) w : ℝ) = w * (-μ) := rfl
      rw [h0]; ring
    have h := charFun_map_add_const (μ := PY) (-μ) w
    rw [hinner, ← hQYdef] at h
    rw [h, mul_assoc, ← Complex.exp_add]
    have hz : ((-(μ * w) : ℝ) : ℂ) * Complex.I + (μ : ℂ) * (w : ℂ) * Complex.I = 0 := by
      push_cast; ring
    rw [hz, Complex.exp_zero, mul_one]
  have hPZchar : ∀ w : ℝ,
      charFun PZ w = charFun QZ w * Complex.exp ((μ : ℂ) * (w : ℂ) * Complex.I) := by
    intro w
    have hinner : (inner ℝ (-μ) w : ℝ) = -(μ * w) := by
      have h0 : (inner ℝ (-μ) w : ℝ) = w * (-μ) := rfl
      rw [h0]; ring
    have h := charFun_map_add_const (μ := PZ) (-μ) w
    rw [hinner, ← hQZdef] at h
    rw [h, mul_assoc, ← Complex.exp_add]
    have hz : ((-(μ * w) : ℝ) : ℂ) * Complex.I + (μ : ℂ) * (w : ℂ) * Complex.I = 0 := by
      push_cast; ring
    rw [hz, Complex.exp_zero, mul_one]
  have hmR : Tendsto (fun k => (m k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hnR : Tendsto (fun k => (n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  haveI hprob : ∀ k, IsProbabilityMeasure
      ((twoSampleLaw (m k) (n k) PY PZ).map (twoSampleMeanDiff (m k) (n k))) := fun k =>
    Measure.isProbabilityMeasure_map (measurable_twoSampleMeanDiff _ _).aemeasurable
  refine weakConverges_of_tendsto_charFun (fun t => ?_)
  -- The two exponent-times-argument-squared limits: `m α² t² → t²` and `n β² t² → λ t²`.
  have hsY : Tendsto (fun k => (m k : ℝ) * (Real.sqrt (m k) * (m k : ℝ)⁻¹ * t) ^ 2) atTop
      (𝓝 (t ^ 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hm.eventually_gt_atTop 0] with k hk
    have hmk : (0 : ℝ) < (m k : ℝ) := by exact_mod_cast hk
    have hne : (m k : ℝ) ≠ 0 := hmk.ne'
    have hsq : Real.sqrt (m k) ^ 2 = (m k : ℝ) := Real.sq_sqrt hmk.le
    have hexp : (Real.sqrt (m k) * (m k : ℝ)⁻¹ * t) ^ 2
        = Real.sqrt (m k) ^ 2 * ((m k : ℝ)⁻¹) ^ 2 * t ^ 2 := by ring
    rw [hexp, hsq]
    field_simp
  have hsZ : Tendsto (fun k => (n k : ℝ) * (-(Real.sqrt (m k) * (n k : ℝ)⁻¹) * t) ^ 2) atTop
      (𝓝 (lam * t ^ 2)) := by
    refine (hratio.mul_const (t ^ 2)).congr' ?_
    filter_upwards [hm.eventually_gt_atTop 0, hn.eventually_gt_atTop 0] with k hmk hnk
    have hmk' : (0 : ℝ) < (m k : ℝ) := by exact_mod_cast hmk
    have hnk' : (0 : ℝ) < (n k : ℝ) := by exact_mod_cast hnk
    have hne : (n k : ℝ) ≠ 0 := hnk'.ne'
    have hsq : Real.sqrt (m k) ^ 2 = (m k : ℝ) := Real.sq_sqrt hmk'.le
    have hexp : (-(Real.sqrt (m k) * (n k : ℝ)⁻¹) * t) ^ 2
        = Real.sqrt (m k) ^ 2 * ((n k : ℝ)⁻¹) ^ 2 * t ^ 2 := by ring
    rw [hexp, hsq]
    field_simp
  have hY := tendsto_charFun_pow hQY0 hQY2 hvarYpos hmR hsY
  have hZ := tendsto_charFun_pow hQZ0 hQZ2 hvarZpos hnR hsZ
  have hprod := hY.mul hZ
  -- The limit is the characteristic function of `N(0, s²)`.
  have htarget : charFun (gaussianReal 0 (NNReal.mk (s ^ 2) (sq_nonneg s))) t
      = Complex.exp (-((varY * t ^ 2 : ℝ) : ℂ) / 2) *
        Complex.exp (-((varZ * (lam * t ^ 2) : ℝ) : ℂ) / 2) := by
    have hsC : ((s : ℂ)) ^ 2 = (varY : ℂ) + (lam : ℂ) * (varZ : ℂ) := by
      exact_mod_cast congrArg (Complex.ofReal) hs
    rw [charFun_gaussianReal, ← Complex.exp_add]
    congr 1
    push_cast
    rw [hsC]
    ring
  rw [htarget]
  refine hprod.congr' ?_
  filter_upwards [hm.eventually_gt_atTop 0, hn.eventually_gt_atTop 0] with k hmk hnk
  have hmC : ((m k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hmk.ne'
  have hnC : ((n k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hnk.ne'
  -- The two phase factors cancel: `m α + n β = 0`.
  have hcancel :
      Complex.exp ((μ : ℂ) * ((Real.sqrt (m k) * (m k : ℝ)⁻¹ * t : ℝ) : ℂ) * Complex.I) ^ (m k)
        * Complex.exp ((μ : ℂ) *
            ((-(Real.sqrt (m k) * (n k : ℝ)⁻¹) * t : ℝ) : ℂ) * Complex.I) ^ (n k) = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have hz : ((m k : ℕ) : ℂ) *
          ((μ : ℂ) * ((Real.sqrt (m k) * (m k : ℝ)⁻¹ * t : ℝ) : ℂ) * Complex.I)
        + ((n k : ℕ) : ℂ) *
          ((μ : ℂ) * ((-(Real.sqrt (m k) * (n k : ℝ)⁻¹) * t : ℝ) : ℂ) * Complex.I) = 0 := by
      push_cast
      field_simp
      ring
    rw [hz, Complex.exp_zero]
  rw [charFun_map_twoSampleMeanDiff, hPYchar, hPZchar, mul_pow, mul_pow, mul_mul_mul_comm,
    hcancel, mul_one]


end StatLean.HypothesisTesting
