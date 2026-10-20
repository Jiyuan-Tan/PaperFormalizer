module
public import StatLean.HypothesisTesting.Bootstrap.Consistency
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.CDF
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import StatLean.HypothesisTesting.ForMathlib.LindebergCLT
public import Mathlib.Probability.HasLawExists
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

/-!
# The nonparametric bootstrap for a mean

The archetypal application of the sequence-class criterion: the parameter is the mean of a law
on the line, the root is the centred and scaled sample mean, and the estimated law is the
empirical measure of the sample. The class of sequences that makes the criterion work is
explicit here — weak convergence together with convergence of means and of variances — and the
almost sure membership of the empirical sequence is exactly the Glivenko–Cantelli theorem plus
the strong law of large numbers.

This file contains:

* `meanSeqClass` — the sequence class `C_F` for the mean problem;
* `meanRootCDF`, `sampleVariance`, `studentizedRootCDF` — the sampling distribution functions
  of the centred and of the studentized sample mean;
* `mean_root_cdf_tendsto` — convergence of the sampling distribution along the class;
* `empirical_mem_meanSeqClass` — almost sure membership of the empirical sequence in the class;
* `bootstrap_mean_consistent`, `bootstrap_mean_coverage` — the headline consistency and
  coverage statements for the mean;
* `studentized_root_cdf_tendsto`, `bootstrap_t_consistent` — the studentized versions.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 18 (Bootstrap and
Subsampling Methods), §18.3 (Bootstrap Sampling Distributions), Theorem 18.3.3 (§18.3.2, The
Nonparametric Mean), Theorem 18.3.4 (the studentized bootstrap-`t`) and Lemma 18.3.1 (the
first-absolute-moment convergence tool). (`TSH4 §18.3 Thm 18.3.3, Thm 18.3.4, Lem 18.3.1`.)

**Proof formalization notes.**
* Convergence of the sampling distribution along the class is a Lindeberg central limit theorem
  for a triangular array whose `n`-th row is drawn from the `n`-th law of the sequence
  (`tendsto_meanRootLaw`). Three points make it work. The rows are realised on one probability
  space by `ProbabilityTheory.exists_hasLaw_indepFun` over the index set `ℕ × ℕ`. The
  standardisation divides by the FIXED limiting standard deviation, not by the `n`-th one, so
  the row variances tend to `1` and the residual rescaling is a fixed continuous map, disposed
  of by `TendstoInDistribution.continuous_comp`. The Lindeberg condition is the uniform
  square-integrability of the rows, `tendsto_setIntegral_sq_tail`, which is Lehmann–Romano's
  Lemma 18.3.1 and needs only the truncated squares `min ((t − b)², M²)` as test functions.
  A vanishing limiting variance is allowed: there the root converges to `0` in probability by
  Chebyshev. The array central limit theorem itself is the sibling `ForMathlib/LindebergCLT`
  brick of this area.
* The class states weak convergence through distribution functions;
  `tendsto_integral_of_tendsto_cdf` upgrades that to convergence of integrals of bounded
  continuous functions, using that the
  continuity points of a monotone function are co-countable, hence dense, and that the
  half-open intervals with endpoints there form a π-system of arbitrarily small neighbourhoods.
* Almost sure membership of the empirical sequence uses the Glivenko–Cantelli theorem for the
  weak-convergence clause and `ProbabilityTheory.strong_law_ae` for the convergence of the
  empirical means and of the empirical second moments (hence of the empirical variances).
* The studentized statement adds one step: the sample variance converges in probability to the
  limiting variance along the class. It is obtained on the same single carrier as the root, so
  that Mathlib's Slutsky lemmas (which are stated for one fixed measure, not for the varying
  carriers `Fin n → ℝ`) apply: the sample second moment is handled by the self-contained
  triangular weak law `tendstoInMeasure_rowMean_of_uniform`, whose uniform-integrability input
  is `exists_uniform_sq_trunc`, and the sample mean by plain Chebyshev on the centred row
  average. Neither routes through `Bootstrap/Consistency`'s
  `tendstoInMeasure_rowMean_triangular`, which depends on the open Feller weak law of
  `ForMathlib/LindebergCLT` and would taint the result. The denominator is kept away from zero
  by the fixed truncation `v ↦ max v (σ²/2)`, removed afterwards by
  `tendstoInDistribution_of_tendstoInMeasure_sub`, which also absorbs the junk convention
  `σ̂ₙ = 0 ↦ 0`.
* The class is stated with the `n = 0` entry unconstrained (`0 < n` guard on the
  probability-measure clause): the empirical measure of an empty sample is the zero measure,
  and every convergence in the class is a statement along `atTop`, so the degenerate entry is
  never seen.
* Division by a vanishing sample standard deviation returns `0` by the junk convention; this is
  reached only on the null event where the sample is constant, which the nondegeneracy
  hypothesis on the limiting variance makes asymptotically negligible.

**Bibliographic comments.** The bootstrap is due to B. Efron ("Bootstrap methods: another look
at the jackknife," *Ann. Statist.* **7** (1979), 1–26). Consistency of the bootstrap for a mean
under a finite nonzero variance, and its failure without one, is due to P. J. Bickel and
D. A. Freedman ("Some asymptotic theory for the bootstrap," *Ann. Statist.* **9** (1981),
1196–1217) and K. Singh ("On the asymptotic accuracy of Efron's bootstrap," *Ann. Statist.* **9**
(1981), 1187–1195); the class-of-sequences packaging follows R. Beran ("Bootstrap methods in
statistics," *Jahresber. Deutsch. Math.-Verein.* **86** (1984), 14–30) and D. N. Politis,
J. P. Romano and M. Wolf, *Subsampling*, Springer, 1999. The superiority of the studentized
(bootstrap-t) root is analysed in P. Hall, *The Bootstrap and Edgeworth Expansion*, Springer,
1992.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StatLean.HypothesisTesting

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The mean-bootstrap sequence class and the roots -/

/-- The **sequence class for the mean problem**, `C_F`: sequences of laws on the line that are
square-integrable, converge weakly to `Q` (their distribution functions converge at every
continuity point of the limit distribution function), and whose means and variances converge to
the mean and variance of `Q`. The `n = 0` entry is left unconstrained; see the file's proof
formalization notes. -/
def meanSeqClass (Q : Measure ℝ) : Set (ℕ → Measure ℝ) :=
  {F | (∀ n : ℕ, 0 < n → IsProbabilityMeasure (F n)) ∧
    (∀ n : ℕ, MemLp (fun t : ℝ => t) 2 (F n)) ∧
    (∀ x : ℝ, ContinuousAt (fun t => (Q (Set.Iic t)).toReal) x →
      Tendsto (fun n => ((F n) (Set.Iic x)).toReal) atTop (𝓝 ((Q (Set.Iic x)).toReal))) ∧
    Tendsto (fun n => ∫ t, t ∂(F n)) atTop (𝓝 (∫ t, t ∂Q)) ∧
    Tendsto (fun n => Var[fun t : ℝ => t; F n]) atTop (𝓝 Var[fun t : ℝ => t; Q])}

/-- The **sampling distribution function of the centred and scaled sample mean** under `n`
independent draws from `F`: `x ↦ F^n{ n^{1/2}(X̄ₙ − E_F X) ≤ x }`. -/
noncomputable def meanRootCDF (F : Measure ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((Measure.pi fun _ : Fin n => F)
    {y : Fin n → ℝ | Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F) ≤ x}).toReal

/-- The **sample variance** in the plug-in (divide-by-`n`) form: the variance of the empirical
measure of the sample. Returns `0` for an empty sample. -/
noncomputable def sampleVariance {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (y i - (n : ℝ)⁻¹ * (∑ j, y j)) ^ 2

/-- The **sampling distribution function of the studentized sample mean** under `n` independent
draws from `F`: `x ↦ F^n{ n^{1/2}(X̄ₙ − E_F X)/σ̂ₙ ≤ x }`, with `σ̂ₙ` the plug-in sample standard
deviation. A vanishing `σ̂ₙ` makes the quotient `0` by the junk convention. -/
noncomputable def studentizedRootCDF (F : Measure ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((Measure.pi fun _ : Fin n => F)
    {y : Fin n → ℝ |
      Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F) /
        Real.sqrt (sampleVariance y) ≤ x}).toReal


/-- The empirical measure of a nonempty sample is a probability measure. -/
private lemma isProbabilityMeasure_empiricalMeasure {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    IsProbabilityMeasure (empiricalMeasure x) := by
  refine ⟨?_⟩
  unfold empiricalMeasure
  simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)]

/-- The sampling distribution function of the centred sample mean is a distribution function
(whenever the underlying `n`-fold product is a probability measure). -/
private lemma isCDF_meanRootCDF (F : Measure ℝ) (n : ℕ)
    [IsProbabilityMeasure (Measure.pi fun _ : Fin n => F)] :
    IsCDF (meanRootCDF F n) := by
  have hSmeas : Measurable (fun y : Fin n → ℝ =>
      Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F)) := by fun_prop
  haveI : IsProbabilityMeasure
      ((Measure.pi fun _ : Fin n => F).map
        (fun y : Fin n → ℝ => Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F))) :=
    Measure.isProbabilityMeasure_map hSmeas.aemeasurable
  have heq : meanRootCDF F n = fun x =>
      (((Measure.pi fun _ : Fin n => F).map
        (fun y : Fin n → ℝ => Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F)))
        (Set.Iic x)).toReal := by
    funext x
    rw [Measure.map_apply hSmeas measurableSet_Iic]
    rfl
  rw [heq]
  exact isCDF_toReal_measure_Iic _

/-- The sampling distribution function of the studentized sample mean is a distribution function
(whenever the underlying `n`-fold product is a probability measure). -/
private lemma isCDF_studentizedRootCDF (F : Measure ℝ) (n : ℕ)
    [IsProbabilityMeasure (Measure.pi fun _ : Fin n => F)] :
    IsCDF (studentizedRootCDF F n) := by
  have hSmeas : Measurable (fun y : Fin n → ℝ =>
      Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F) / Real.sqrt (sampleVariance y)) := by
    unfold sampleVariance; fun_prop
  haveI : IsProbabilityMeasure
      ((Measure.pi fun _ : Fin n => F).map
        (fun y : Fin n → ℝ =>
          Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F) / Real.sqrt (sampleVariance y))) :=
    Measure.isProbabilityMeasure_map hSmeas.aemeasurable
  have heq : studentizedRootCDF F n = fun x =>
      (((Measure.pi fun _ : Fin n => F).map
        (fun y : Fin n → ℝ =>
          Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F) / Real.sqrt (sampleVariance y)))
        (Set.Iic x)).toReal := by
    funext x
    rw [Measure.map_apply hSmeas measurableSet_Iic]
    rfl
  rw [heq]
  exact isCDF_toReal_measure_Iic _

/-- Every real function is integrable against an empirical (finite-support) measure. -/
private lemma integrable_empiricalMeasure {n : ℕ} (x : Fin n → ℝ) (f : ℝ → ℝ) :
    Integrable f (empiricalMeasure x) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [empiricalMeasure]
  · unfold empiricalMeasure
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (by exact_mod_cast hn.ne'))
    exact integrable_finset_sum_measure.2 (fun i _ => integrable_dirac (by simp))

/-- The integral of a function against an empirical measure is the sample average of its values. -/
private lemma integral_empiricalMeasure {n : ℕ} (x : Fin n → ℝ) (f : ℝ → ℝ) :
    ∫ t, f t ∂(empiricalMeasure x) = (n : ℝ)⁻¹ * ∑ i, f (x i) := by
  unfold empiricalMeasure
  rw [integral_smul_measure, integral_finset_sum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

/-- The identity is square-integrable against an empirical measure. -/
private lemma memLp_id_empiricalMeasure {n : ℕ} (x : Fin n → ℝ) :
    MemLp (fun t : ℝ => t) 2 (empiricalMeasure x) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  exact integrable_empiricalMeasure x (fun t => t ^ 2)

/-- An empirical measure is finite. -/
private lemma isFiniteMeasure_empiricalMeasure {n : ℕ} (x : Fin n → ℝ) :
    IsFiniteMeasure (empiricalMeasure x) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [empiricalMeasure, Finset.univ_eq_empty, Finset.sum_empty, smul_zero]
    infer_instance
  · haveI := isProbabilityMeasure_empiricalMeasure hn x; infer_instance

/-- The empirical distribution function is the sample average of the half-line indicators. -/
private lemma empiricalMeasure_Iic_toReal {n : ℕ} (x : Fin n → ℝ) (y : ℝ) :
    ((empiricalMeasure x) (Set.Iic y)).toReal
      = (n : ℝ)⁻¹ * ∑ i, Set.indicator (Set.Iic y) (1 : ℝ → ℝ) (x i) := by
  haveI := isFiniteMeasure_empiricalMeasure x
  rw [← measureReal_def, ← integral_indicator_one (μ := empiricalMeasure x) measurableSet_Iic,
    integral_empiricalMeasure x (Set.indicator (Set.Iic y) (1 : ℝ → ℝ))]

/-- The `n`-fold product of a probability law is a probability measure. -/
private lemma isProbabilityMeasure_pi_const (n : ℕ) (F : Measure ℝ) [IsProbabilityMeasure F] :
    IsProbabilityMeasure (Measure.pi fun _ : Fin n => F) := by
  haveI : ∀ _ : Fin n, IsProbabilityMeasure F := fun _ => ‹_›
  infer_instance

/-- The `n`-fold product of the empirical measure of a sample is a probability measure (for the
empty sample it is the point mass on the empty tuple). -/
private lemma isProbabilityMeasure_pi_empirical (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    IsProbabilityMeasure
      (Measure.pi fun _ : Fin n => empiricalMeasure fun i : Fin n => X i ω) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Measure.pi_of_empty]
    infer_instance
  · haveI := isProbabilityMeasure_empiricalMeasure hn (fun i : Fin n => X i ω)
    exact isProbabilityMeasure_pi_const n _

/-- The constant sequence at a square-integrable probability law belongs to its own mean class. -/
private lemma const_mem_meanSeqClass (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q) : (fun _ => Q) ∈ meanSeqClass Q :=
  ⟨fun _ _ => inferInstance, fun _ => hQ2, fun _ _ => tendsto_const_nhds,
    tendsto_const_nhds, tendsto_const_nhds⟩

open Classical in
/-- A distribution-function-valued wrapper of `meanRootCDF`: it is `meanRootCDF F n` whenever
the `n`-fold product of `F` is a probability measure, and the standard normal otherwise. This
makes `IsCDF (Jmean n F)` hold for **every** measure `F`, so the general bootstrap criterion of
`Bootstrap/Consistency` applies with `J := Jmean`. -/
private noncomputable def Jmean (n : ℕ) (F : Measure ℝ) : ℝ → ℝ :=
  if IsProbabilityMeasure (Measure.pi fun _ : Fin n => F) then meanRootCDF F n else stdNormalCDF

private lemma isCDF_Jmean (n : ℕ) (F : Measure ℝ) : IsCDF (Jmean n F) := by
  unfold Jmean
  split_ifs with h
  · haveI := h; exact isCDF_meanRootCDF F n
  · exact isCDF_stdNormalCDF

private lemma Jmean_eq_meanRootCDF (n : ℕ) (F : Measure ℝ)
    [h : IsProbabilityMeasure (Measure.pi fun _ : Fin n => F)] :
    Jmean n F = meanRootCDF F n := by
  unfold Jmean; rw [if_pos h]

/-! ## Uniform square-integrability along a weakly convergent sequence -/

section Vitali

/-- The shifted truncated square `t ↦ min ((t - b)²) (M²)`, as a bounded continuous function. -/
private noncomputable def truncSq (M b : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => min ((t - b) ^ 2) (M ^ 2))
    (by fun_prop) (M ^ 2)
    (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) (sq_nonneg M))]
      exact min_le_right _ _)

private lemma truncSq_apply (M b t : ℝ) : truncSq M b t = min ((t - b) ^ 2) (M ^ 2) := rfl

/-- The truncated square is `2M`-Lipschitz. -/
private lemma abs_truncSq_sub_le {M : ℝ} (hM : 0 ≤ M) (u w : ℝ) :
    |min (u ^ 2) (M ^ 2) - min (w ^ 2) (M ^ 2)| ≤ 2 * M * |u - w| := by
  have hmin_le : ∀ x y : ℝ, min x M - min y M ≤ |x - y| := by
    intro x y
    rcases le_total y M with h | h
    · rw [min_eq_left h]
      calc min x M - y ≤ x - y := by linarith [min_le_left x M]
        _ ≤ |x - y| := le_abs_self _
    · rw [min_eq_right h]
      calc min x M - M ≤ 0 := by linarith [min_le_right x M]
        _ ≤ |x - y| := abs_nonneg _
  have hminabs : |min |u| M - min |w| M| ≤ |u - w| := by
    refine abs_sub_le_iff.2 ⟨(hmin_le |u| |w|).trans (abs_abs_sub_abs_le_abs_sub u w), ?_⟩
    refine (hmin_le |w| |u|).trans ((abs_abs_sub_abs_le_abs_sub w u).trans ?_)
    exact le_of_eq (abs_sub_comm w u)
  have hsq : ∀ x : ℝ, min (x ^ 2) (M ^ 2) = (min |x| M) ^ 2 := by
    intro x
    rcases le_total |x| M with h | h
    · rw [min_eq_left h, sq_abs, min_eq_left (by nlinarith [abs_nonneg x, sq_abs x])]
    · rw [min_eq_right h, min_eq_right (by nlinarith [abs_nonneg x, sq_abs x])]
  rw [hsq, hsq]
  have hx : 0 ≤ min |u| M := le_min (abs_nonneg u) hM
  have hy : 0 ≤ min |w| M := le_min (abs_nonneg w) hM
  have hxM : min |u| M ≤ M := min_le_right _ _
  have hyM : min |w| M ≤ M := min_le_right _ _
  have hfac : (min |u| M) ^ 2 - (min |w| M) ^ 2
      = (min |u| M - min |w| M) * (min |u| M + min |w| M) := by ring
  rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ min |u| M + min |w| M)]
  calc |min |u| M - min |w| M| * (min |u| M + min |w| M)
      ≤ |u - w| * (2 * M) := by
        refine mul_le_mul hminabs (by linarith) (by linarith) (abs_nonneg _)
    _ = 2 * M * |u - w| := by ring

/-- **Vitali's uniform square-integrability upgrade (with a drifting centre).**

If the laws `F n` converge weakly to `Q` and the second moments about the drifting centres
`a n → b` converge to the second moment of `Q` about `b`, then the squares are uniformly
integrable: the tail integrals over `{|t - a n| > c n}` vanish for every threshold sequence
`c n → ∞`.

This is Lehmann–Romano Lemma 18.3.1 in the exact form the Lindeberg condition needs. The proof
uses only the truncated squares `min ((t - b)²) (M²)` as bounded continuous test functions,
together with their `2M`-Lipschitz dependence on the centre. -/
private lemma tendsto_setIntegral_sq_tail
    {F : ℕ → Measure ℝ} {Q : Measure ℝ} [∀ n, IsProbabilityMeasure (F n)] [IsProbabilityMeasure Q]
    {a : ℕ → ℝ} {b : ℝ}
    (hF2 : ∀ n, MemLp (fun t : ℝ => t) 2 (F n)) (hQ2 : MemLp (fun t : ℝ => t) 2 Q)
    (hweak : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n => ∫ t, f t ∂(F n)) atTop (𝓝 (∫ t, f t ∂Q)))
    (ha : Tendsto a atTop (𝓝 b))
    (hsq : Tendsto (fun n => ∫ t, (t - a n) ^ 2 ∂(F n)) atTop (𝓝 (∫ t, (t - b) ^ 2 ∂Q)))
    {c : ℕ → ℝ} (hc : Tendsto c atTop atTop) :
    Tendsto (fun n => ∫ t in {t : ℝ | c n < |t - a n|}, (t - a n) ^ 2 ∂(F n)) atTop (𝓝 0) := by
  classical
  have hshiftLp : ∀ (n : ℕ) (r : ℝ), MemLp (fun t : ℝ => t - r) 2 (F n) := fun n r =>
    (hF2 n).sub (memLp_const r)
  have hint : ∀ (n : ℕ) (r : ℝ), Integrable (fun t : ℝ => (t - r) ^ 2) (F n) := fun n r =>
    (hshiftLp n r).integrable_sq
  have hintQ : Integrable (fun t : ℝ => (t - b) ^ 2) Q := (hQ2.sub (memLp_const b)).integrable_sq
  -- the defect of the truncation at level `m` vanishes as `m → ∞`
  have hδ : Tendsto (fun m : ℕ => ∫ t, ((t - b) ^ 2 - min ((t - b) ^ 2) ((m : ℝ) ^ 2)) ∂Q)
      atTop (𝓝 0) := by
    have hlim : ∀ t : ℝ,
        Tendsto (fun m : ℕ => (t - b) ^ 2 - min ((t - b) ^ 2) ((m : ℝ) ^ 2)) atTop (𝓝 0) := by
      intro t
      have hev : ∀ᶠ m : ℕ in atTop, (t - b) ^ 2 - min ((t - b) ^ 2) ((m : ℝ) ^ 2) = 0 := by
        filter_upwards [eventually_ge_atTop (Nat.ceil |t - b|)] with m hm
        have h1 : |t - b| ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
        have h2 : (t - b) ^ 2 ≤ (m : ℝ) ^ 2 := by nlinarith [sq_abs (t - b), abs_nonneg (t - b)]
        rw [min_eq_left h2, sub_self]
      exact tendsto_const_nhds.congr' (hev.mono fun m hm => hm.symm)
    have hdom : Tendsto (fun m : ℕ => ∫ t, ((t - b) ^ 2 - min ((t - b) ^ 2) ((m : ℝ) ^ 2)) ∂Q)
        atTop (𝓝 (∫ _t : ℝ, (0 : ℝ) ∂Q)) := by
      refine tendsto_integral_of_dominated_convergence (fun t => (t - b) ^ 2) ?_ hintQ ?_ ?_
      · exact fun m => (by fun_prop : Measurable fun t : ℝ =>
          (t - b) ^ 2 - min ((t - b) ^ 2) ((m : ℝ) ^ 2)).aestronglyMeasurable
      · intro m
        filter_upwards with t
        rw [Real.norm_eq_abs, abs_of_nonneg (by simp [sub_nonneg])]
        simp [sq_nonneg]
      · filter_upwards with t using hlim t
    simpa using hdom
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro η hη
  -- choose the truncation level
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∫ t, ((t - b) ^ 2 - min ((t - b) ^ 2) ((m : ℝ) ^ 2)) ∂Q < 3 * η / 8 :=
    (hδ.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 3 * η / 8))).exists
  set M : ℝ := (m : ℝ) with hM
  have hMnn : 0 ≤ M := Nat.cast_nonneg m
  -- the truncated integrals with drifting centre converge
  have hI : ∀ (r : ℝ) (n : ℕ), Integrable (fun t : ℝ => min ((t - r) ^ 2) (M ^ 2)) (F n) :=
    fun r n => (truncSq M r).integrable (F n)
  have hIQ : Integrable (fun t : ℝ => min ((t - b) ^ 2) (M ^ 2)) Q := (truncSq M b).integrable Q
  have htruncconv : Tendsto (fun n => ∫ t, min ((t - a n) ^ 2) (M ^ 2) ∂(F n)) atTop
      (𝓝 (∫ t, min ((t - b) ^ 2) (M ^ 2) ∂Q)) := by
    have hbase := hweak (truncSq M b)
    simp only [truncSq_apply] at hbase
    have hdiff : Tendsto (fun n => (∫ t, min ((t - a n) ^ 2) (M ^ 2) ∂(F n))
        - ∫ t, min ((t - b) ^ 2) (M ^ 2) ∂(F n)) atTop (𝓝 0) := by
      have hbd : ∀ n, |(∫ t, min ((t - a n) ^ 2) (M ^ 2) ∂(F n))
          - ∫ t, min ((t - b) ^ 2) (M ^ 2) ∂(F n)| ≤ 2 * M * |a n - b| := by
        intro n
        rw [← integral_sub (hI (a n) n) (hI b n)]
        refine (abs_integral_le_integral_abs).trans ?_
        have hmono : ∫ t, |min ((t - a n) ^ 2) (M ^ 2) - min ((t - b) ^ 2) (M ^ 2)| ∂(F n)
            ≤ ∫ _t : ℝ, 2 * M * |a n - b| ∂(F n) := by
          refine integral_mono ((hI (a n) n).sub (hI b n)).abs (integrable_const _) (fun t => ?_)
          have h := abs_truncSq_sub_le hMnn (t - a n) (t - b)
          have heq : (t - a n) - (t - b) = b - a n := by ring
          rw [heq] at h
          rwa [abs_sub_comm b (a n)] at h
        refine hmono.trans ?_
        simp
      have hto : Tendsto (fun n => 2 * M * |a n - b|) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n => |a n - b|) atTop (𝓝 0) := by
          simpa using (ha.sub_const b).abs
        simpa using h1.const_mul (2 * M)
      refine squeeze_zero_norm (fun n => ?_) hto
      simpa using hbd n
    have := hdiff.add hbase
    simpa using this
  -- the defect for `F n` converges to the defect for `Q`
  have hgm : Tendsto (fun n => ∫ t, ((t - a n) ^ 2 - min ((t - a n) ^ 2) (M ^ 2)) ∂(F n)) atTop
      (𝓝 (∫ t, ((t - b) ^ 2 - min ((t - b) ^ 2) (M ^ 2)) ∂Q)) := by
    have hrw : ∀ n, ∫ t, ((t - a n) ^ 2 - min ((t - a n) ^ 2) (M ^ 2)) ∂(F n)
        = (∫ t, (t - a n) ^ 2 ∂(F n)) - ∫ t, min ((t - a n) ^ 2) (M ^ 2) ∂(F n) :=
      fun n => integral_sub (hint n (a n)) (hI (a n) n)
    have hrwQ : ∫ t, ((t - b) ^ 2 - min ((t - b) ^ 2) (M ^ 2)) ∂Q
        = (∫ t, (t - b) ^ 2 ∂Q) - ∫ t, min ((t - b) ^ 2) (M ^ 2) ∂Q :=
      integral_sub hintQ hIQ
    simp only [hrw, hrwQ]
    exact hsq.sub htruncconv
  have hdefect : ∀ᶠ n in atTop,
      ∫ t, ((t - a n) ^ 2 - min ((t - a n) ^ 2) (M ^ 2)) ∂(F n) < η / 2 := by
    refine hgm.eventually (eventually_lt_nhds ?_)
    have h : ∫ t, ((t - b) ^ 2 - min ((t - b) ^ 2) (M ^ 2)) ∂Q < 3 * η / 8 := hm
    linarith
  filter_upwards [hdefect, hc.eventually_ge_atTop (2 * M)] with n hn1 hn2
  have hmeasS : MeasurableSet {t : ℝ | c n < |t - a n|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hmeasT : MeasurableSet {t : ℝ | 2 * M < |t - a n|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hnn : 0 ≤ ∫ t in {t : ℝ | c n < |t - a n|}, (t - a n) ^ 2 ∂(F n) :=
    setIntegral_nonneg hmeasS (fun t _ => sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hdnn : (0 : ℝ → ℝ) ≤ᵐ[F n] fun t => (t - a n) ^ 2 - min ((t - a n) ^ 2) (M ^ 2) := by
    filter_upwards with t
    simp [sub_nonneg]
  have hdint : Integrable (fun t : ℝ => (t - a n) ^ 2 - min ((t - a n) ^ 2) (M ^ 2)) (F n) :=
    (hint n (a n)).sub (hI (a n) n)
  calc ∫ t in {t : ℝ | c n < |t - a n|}, (t - a n) ^ 2 ∂(F n)
      ≤ ∫ t in {t : ℝ | 2 * M < |t - a n|}, (t - a n) ^ 2 ∂(F n) := by
        refine setIntegral_mono_set ((hint n (a n)).integrableOn) ?_ ?_
        · filter_upwards with t using sq_nonneg _
        · filter_upwards with t ht using lt_of_le_of_lt hn2 ht
    _ ≤ ∫ t in {t : ℝ | 2 * M < |t - a n|},
          (4 / 3) * ((t - a n) ^ 2 - min ((t - a n) ^ 2) (M ^ 2)) ∂(F n) := by
        refine setIntegral_mono_on ((hint n (a n)).integrableOn)
          ((hdint.const_mul (4 / 3)).integrableOn) hmeasT ?_
        intro t ht
        simp only [Set.mem_setOf_eq] at ht
        have hsq4 : 4 * M ^ 2 ≤ (t - a n) ^ 2 := by
          nlinarith [sq_abs (t - a n), abs_nonneg (t - a n)]
        have hmin : min ((t - a n) ^ 2) (M ^ 2) = M ^ 2 := by
          refine min_eq_right ?_
          nlinarith [sq_nonneg M]
        rw [hmin]
        nlinarith
    _ ≤ ∫ t, (4 / 3) * ((t - a n) ^ 2 - min ((t - a n) ^ 2) (M ^ 2)) ∂(F n) := by
        refine setIntegral_le_integral (hdint.const_mul (4 / 3)) ?_
        filter_upwards [hdnn] with t ht
        have h : (0 : ℝ) ≤ (t - a n) ^ 2 - min ((t - a n) ^ 2) (M ^ 2) := ht
        positivity
    _ = (4 / 3) * ∫ t, ((t - a n) ^ 2 - min ((t - a n) ^ 2) (M ^ 2)) ∂(F n) :=
        integral_const_mul _ _
    _ < η := by nlinarith [hn1]

/-- The truncated square `t ↦ min (t², M)`, as a bounded continuous function. -/
private lemma truncSq_zero_apply {M : ℝ} (hM : 0 ≤ M) (t : ℝ) :
    truncSq (Real.sqrt M) 0 t = min (t ^ 2) M := by
  rw [truncSq_apply, sub_zero, Real.sq_sqrt hM]

/-- The excess `(t² − M)⁺` is integrable against a square-integrable law, and its integral is the
second moment minus the truncated second moment. -/
private lemma integral_sq_excess {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ2 : MemLp (fun t : ℝ => t) 2 μ) {M : ℝ} (hM : 0 ≤ M) :
    ∫ t, max (t ^ 2 - M) 0 ∂μ = ∫ t, t ^ 2 ∂μ - ∫ t, truncSq (Real.sqrt M) 0 t ∂μ := by
  have hsq : Integrable (fun t : ℝ => t ^ 2) μ := hμ2.integrable_sq
  have hbdd : Integrable (fun t : ℝ => truncSq (Real.sqrt M) 0 t) μ :=
    BoundedContinuousFunction.integrable _ (truncSq (Real.sqrt M) 0)
  rw [← integral_sub hsq hbdd]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [truncSq_zero_apply hM]
  rcases le_total (t ^ 2) M with hle | hle
  · rw [min_eq_left hle, max_eq_right (by linarith)]; ring
  · rw [min_eq_right hle, max_eq_left (by linarith)]

/-- The excess integral is antitone in the truncation level. -/
private lemma integral_sq_excess_antitone {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ2 : MemLp (fun t : ℝ => t) 2 μ) {M M' : ℝ} (hMM : M ≤ M') :
    ∫ t, max (t ^ 2 - M') 0 ∂μ ≤ ∫ t, max (t ^ 2 - M) 0 ∂μ := by
  have hsq : Integrable (fun t : ℝ => t ^ 2) μ := hμ2.integrable_sq
  have hint : ∀ r : ℝ, Integrable (fun t : ℝ => max (t ^ 2 - r) 0) μ := by
    intro r
    have hg : Integrable (fun t : ℝ => t ^ 2 + |r|) μ := hsq.add (integrable_const |r|)
    refine Integrable.mono' hg (by fun_prop) (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right (t ^ 2 - r) 0)]
    exact max_le (by linarith [neg_le_abs r]) (by positivity)
  refine integral_mono (hint M') (hint M) fun t => ?_
  exact max_le_max (by linarith) le_rfl

/-- **Uniform square-integrability along a weakly convergent sequence with converging second
moments.**

For every `ε > 0` there is one truncation level `M` at which the excess `(t² − M)⁺` has integral
at most `ε` against **every** member of the sequence — not merely in the limit. This is the form
the weak law of large numbers for the *squares* of a triangular array consumes. -/
private lemma exists_uniform_sq_trunc {F : ℕ → Measure ℝ} {Q : Measure ℝ}
    [∀ n, IsProbabilityMeasure (F n)] [IsProbabilityMeasure Q]
    (hF2 : ∀ n, MemLp (fun t : ℝ => t) 2 (F n)) (hQ2 : MemLp (fun t : ℝ => t) 2 Q)
    (hweak : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n => ∫ t, f t ∂(F n)) atTop (𝓝 (∫ t, f t ∂Q)))
    (hsq : Tendsto (fun n => ∫ t, t ^ 2 ∂(F n)) atTop (𝓝 (∫ t, t ^ 2 ∂Q)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ∫ t, max (t ^ 2 - M) 0 ∂(F n) ≤ ε := by
  classical
  -- for each fixed level the excess integrals converge
  have hlevel : ∀ M : ℝ, 0 ≤ M →
      Tendsto (fun n => ∫ t, max (t ^ 2 - M) 0 ∂(F n)) atTop
        (𝓝 (∫ t, max (t ^ 2 - M) 0 ∂Q)) := by
    intro M hM
    have hconv := hsq.sub (hweak (truncSq (Real.sqrt M) 0))
    rw [← integral_sq_excess hQ2 hM] at hconv
    exact hconv.congr fun n => (integral_sq_excess (hF2 n) hM).symm
  -- the excess integral against any fixed square-integrable law vanishes as the level grows
  have hvanish : ∀ (μ : Measure ℝ), IsProbabilityMeasure μ → MemLp (fun t : ℝ => t) 2 μ →
      Tendsto (fun j : ℕ => ∫ t, max (t ^ 2 - (j : ℝ)) 0 ∂μ) atTop (𝓝 0) := by
    intro μ hμ hμ2
    haveI := hμ
    have hsqint : Integrable (fun t : ℝ => t ^ 2) μ := hμ2.integrable_sq
    have hDCT : Tendsto (fun j : ℕ => ∫ t, max (t ^ 2 - (j : ℝ)) 0 ∂μ) atTop
        (𝓝 (∫ _t : ℝ, (0 : ℝ) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun t => t ^ 2)
        (fun j => by fun_prop) hsqint (fun j => Filter.Eventually.of_forall fun t => ?_)
        (Filter.Eventually.of_forall fun t => ?_)
      · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right (t ^ 2 - (j : ℝ)) 0)]
        exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) j]) (sq_nonneg t)
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈t ^ 2⌉₊] with j hj
        have hjr : t ^ 2 ≤ (j : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.2 hj)
        exact (max_eq_right (by linarith)).symm
    simpa using hDCT
  -- a level that works for the limit, hence for all large indices
  obtain ⟨j₀, hj₀⟩ : ∃ j : ℕ, ∫ t, max (t ^ 2 - (j : ℝ)) 0 ∂Q < ε / 2 :=
    ((hvanish Q inferInstance hQ2).eventually_lt_const (by positivity)).exists
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (((hlevel (j₀ : ℝ) (Nat.cast_nonneg j₀)).eventually_lt_const
      (show ∫ t, max (t ^ 2 - (j₀ : ℝ)) 0 ∂Q < ε by linarith)))
  -- levels that work for the finitely many small indices
  have hsmall : ∀ n : ℕ, ∃ j : ℕ, ∫ t, max (t ^ 2 - (j : ℝ)) 0 ∂(F n) ≤ ε := by
    intro n
    obtain ⟨j, hj⟩ := ((hvanish (F n) inferInstance (hF2 n)).eventually_lt_const
      (show (0 : ℝ) < ε from hε)).exists
    exact ⟨j, hj.le⟩
  choose g hg using hsmall
  refine ⟨((Finset.range N).sup g ⊔ j₀ : ℕ), Nat.cast_nonneg _, fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · refine le_trans (integral_sq_excess_antitone (hF2 n) ?_) (hg n)
    exact_mod_cast le_sup_of_le_left (Finset.le_sup (Finset.mem_range.2 hn))
  · refine le_trans (integral_sq_excess_antitone (hF2 n) ?_) (hN n hn).le
    exact_mod_cast le_sup_right

/-- **Weak law of large numbers for a triangular array with uniformly integrable nonnegative
rows.**

The entries of row `n` are independent and nonnegative with a common mean `s n → c`, and the
excess above a common truncation level has arbitrarily small integral **uniformly in the row**.
Then the row averages converge to `c` in probability.

This is the self-contained replacement for `Bootstrap/Consistency`'s
`tendstoInMeasure_rowMean_triangular`, which derives uniform integrability from a Feller-type
weak law and therefore carries that file's `sorryAx`. Here uniform integrability is supplied
directly — by `exists_uniform_sq_trunc` at the application site — and the proof is the classical
truncation argument: split each entry as `min (Z, M) + (Z − M)⁺`, control the bounded part by
Chebyshev (its variance is at most `M²/n`) and the excess by Markov. -/
private lemma tendstoInMeasure_rowMean_of_uniform {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {Z : ℕ → ℕ → Ω → ℝ} {s : ℕ → ℝ} {c : ℝ}
    (hmeas : ∀ n i, Measurable (Z n i))
    (hindep : ∀ n : ℕ, iIndepFun (fun i : Fin n => Z n (i : ℕ)) Pr)
    (hnn : ∀ n i ω, 0 ≤ Z n i ω)
    (hint : ∀ n i, Integrable (Z n i) Pr)
    (hmean : ∀ n i : ℕ, i < n → ∫ ω, Z n i ω ∂Pr = s n)
    (hs : Tendsto s atTop (𝓝 c))
    (hUI : ∀ ρ : ℝ, 0 < ρ → ∃ M : ℝ, 0 ≤ M ∧
      ∀ n i : ℕ, i < n → ∫ ω, max (Z n i ω - M) 0 ∂Pr ≤ ρ) :
    TendstoInMeasure Pr (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z n i ω) atTop
      (fun _ => c) := by
  classical
  refine tendstoInMeasure_iff_measureReal_norm.2 fun ε hε => ?_
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro η hη
  -- the common truncation level
  set ρ : ℝ := min (ε / 4) (η * ε / 8) with hρdef
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  obtain ⟨M, hM0, hMbound⟩ := hUI ρ hρ
  -- the truncated entries and the excess
  set A : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i : Fin n, min (Z n (i : ℕ) ω) M with hAdef
  set B : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i : Fin n, max (Z n (i : ℕ) ω - M) 0 with hBdef
  have hsplit : ∀ (n : ℕ) (ω : Ω),
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z n i ω = A n ω + B n ω := by
    intro n ω
    rw [hAdef, hBdef, ← Fin.sum_univ_eq_sum_range (fun i => Z n i ω) n, ← mul_add,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases le_total (Z n (i : ℕ) ω) M with hle | hle
    · rw [min_eq_left hle, max_eq_right (by linarith)]; ring
    · rw [min_eq_right hle, max_eq_left (by linarith)]; ring
  have hAmeas : ∀ n, Measurable (A n) := by
    intro n; rw [hAdef]; fun_prop
  have hBmeas : ∀ n, Measurable (B n) := by
    intro n; rw [hBdef]; fun_prop
  have hBnn : ∀ n ω, 0 ≤ B n ω := by
    intro n ω
    rw [hBdef]
    have : (0 : ℝ) ≤ ∑ i : Fin n, max (Z n (i : ℕ) ω - M) 0 :=
      Finset.sum_nonneg fun i _ => le_max_right _ _
    positivity
  have hAbdd : ∀ n ω, |A n ω| ≤ M := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hAdef, hM0]
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hlow : (0 : ℝ) ≤ ∑ i : Fin n, min (Z n (i : ℕ) ω) M :=
        Finset.sum_nonneg fun i _ => le_min (hnn _ _ _) hM0
      have hhigh : ∑ i : Fin n, min (Z n (i : ℕ) ω) M ≤ (n : ℝ) * M := by
        calc ∑ i : Fin n, min (Z n (i : ℕ) ω) M ≤ ∑ _i : Fin n, M :=
              Finset.sum_le_sum fun i _ => min_le_right _ _
          _ = (n : ℝ) * M := by simp [mul_comm]
      rw [hAdef, abs_le]
      constructor
      · have : (0 : ℝ) ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, min (Z n (i : ℕ) ω) M := by positivity
        linarith
      · calc (n : ℝ)⁻¹ * ∑ i : Fin n, min (Z n (i : ℕ) ω) M ≤ (n : ℝ)⁻¹ * ((n : ℝ) * M) := by
              exact mul_le_mul_of_nonneg_left hhigh (by positivity)
          _ = M := by field_simp
  have hAL2 : ∀ n, MemLp (A n) 2 Pr := fun n =>
    MemLp.of_bound (hAmeas n).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hAbdd n ω)
  have hminiG : ∀ n i : ℕ, Integrable (fun ω => min (Z n i ω) M) Pr := by
    intro n i
    refine Integrable.mono' (integrable_const (|M| + 1)) (by fun_prop)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, ?_⟩
    · have h1 : (0 : ℝ) ≤ min (Z n i ω) M := le_min (hnn _ _ _) hM0
      have := abs_nonneg M; linarith
    · have := min_le_right (Z n i ω) M
      have := le_abs_self M; linarith
  have hexiG : ∀ n i : ℕ, Integrable (fun ω => max (Z n i ω - M) 0) Pr := by
    intro n i
    have hbound : Integrable (fun ω => Z n i ω + |M|) Pr :=
      (hint n i).add (integrable_const |M|)
    refine Integrable.mono' hbound (by fun_prop) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ ?_
    · have h1 := le_abs_self M
      have h2 := hnn n i ω
      have h3 := neg_abs_le M
      linarith
    · have h2 := hnn n i ω
      have h3 := abs_nonneg M
      linarith
  -- the mean of the truncated average is within `ρ` of the row mean
  have hAmean : ∀ n : ℕ, 0 < n → |(∫ ω, A n ω ∂Pr) - s n| ≤ ρ := by
    intro n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmini : ∀ i : Fin n, Integrable (fun ω => min (Z n (i : ℕ) ω) M) Pr :=
      fun i => hminiG n (i : ℕ)
    have hexi : ∀ i : Fin n, Integrable (fun ω => max (Z n (i : ℕ) ω - M) 0) Pr :=
      fun i => hexiG n (i : ℕ)
    have hAint : ∫ ω, A n ω ∂Pr
        = (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, min (Z n (i : ℕ) ω) M ∂Pr := by
      rw [hAdef]
      simp only []
      rw [integral_const_mul, integral_finset_sum _ fun i _ => hmini i]
    have hper : ∀ i : Fin n, ∫ ω, min (Z n (i : ℕ) ω) M ∂Pr
        = s n - ∫ ω, max (Z n (i : ℕ) ω - M) 0 ∂Pr := by
      intro i
      have hid : ∫ ω, Z n (i : ℕ) ω ∂Pr
          = ∫ ω, min (Z n (i : ℕ) ω) M ∂Pr + ∫ ω, max (Z n (i : ℕ) ω - M) 0 ∂Pr := by
        rw [← integral_add (hmini i) (hexi i)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        simp only []
        rcases le_total (Z n (i : ℕ) ω) M with hle | hle
        · rw [min_eq_left hle, max_eq_right (by linarith)]; ring
        · rw [min_eq_right hle, max_eq_left (by linarith)]; ring
      rw [hmean n (i : ℕ) i.isLt] at hid
      linarith
    have hnn' : ∀ i : Fin n, 0 ≤ ∫ ω, max (Z n (i : ℕ) ω - M) 0 ∂Pr := fun i =>
      integral_nonneg fun ω => le_max_right _ _
    rw [hAint]
    simp only [hper, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hsum_le : ∑ i : Fin n, ∫ ω, max (Z n (i : ℕ) ω - M) 0 ∂Pr ≤ (n : ℝ) * ρ := by
      calc ∑ i : Fin n, ∫ ω, max (Z n (i : ℕ) ω - M) 0 ∂Pr ≤ ∑ _i : Fin n, ρ :=
            Finset.sum_le_sum fun i _ => hMbound n (i : ℕ) i.isLt
        _ = (n : ℝ) * ρ := by simp
    have hsum_nn : (0 : ℝ) ≤ ∑ i : Fin n, ∫ ω, max (Z n (i : ℕ) ω - M) 0 ∂Pr :=
      Finset.sum_nonneg fun i _ => hnn' i
    rw [mul_sub, abs_le]
    constructor
    · have h1 : (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, max (Z n (i : ℕ) ω - M) 0 ∂Pr ≤ ρ := by
        calc (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, max (Z n (i : ℕ) ω - M) 0 ∂Pr
            ≤ (n : ℝ)⁻¹ * ((n : ℝ) * ρ) := by
              exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = ρ := by field_simp
      have h2 : (n : ℝ)⁻¹ * ((n : ℝ) * s n) = s n := by field_simp
      rw [h2]; linarith
    · have h1 : (0 : ℝ) ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, max (Z n (i : ℕ) ω - M) 0 ∂Pr := by
        positivity
      have h2 : (n : ℝ)⁻¹ * ((n : ℝ) * s n) = s n := by field_simp
      rw [h2]; linarith
  -- Chebyshev for the truncated average
  have hAvar : ∀ n : ℕ, 0 < n → Var[A n; Pr] ≤ M ^ 2 / n := by
    intro n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    set W : Fin n → Ω → ℝ := fun i ω => min (Z n (i : ℕ) ω) M with hWdef
    have hWmeas : ∀ i, Measurable (W i) := by intro i; rw [hWdef]; fun_prop
    have hWbdd : ∀ i ω, |W i ω| ≤ M := by
      intro i ω
      rw [hWdef, abs_le]
      exact ⟨by have := le_min (hnn n (i : ℕ) ω) hM0; linarith,
        min_le_right _ _⟩
    have hWL2 : ∀ i, MemLp (W i) 2 Pr := fun i =>
      MemLp.of_bound (hWmeas i).aestronglyMeasurable M
        (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hWbdd i ω)
    have hWindep : iIndepFun W Pr := by
      have := (hindep n).comp (fun _ : Fin n => fun z : ℝ => min z M) (fun _ => by fun_prop)
      simpa [Function.comp_def, hWdef] using this
    have hvarsum : Var[∑ i : Fin n, W i; Pr] = ∑ i : Fin n, Var[W i; Pr] :=
      IndepFun.variance_sum (fun i _ => hWL2 i)
        (fun i _ j _ hij => hWindep.indepFun hij)
    have hWvar : ∀ i, Var[W i; Pr] ≤ M ^ 2 := by
      intro i
      refine (variance_le_expectation_sq (hWmeas i).aestronglyMeasurable).trans ?_
      have hb : ∫ ω, (W i ω) ^ 2 ∂Pr ≤ ∫ _ω : Ω, M ^ 2 ∂Pr := by
        refine integral_mono ((hWL2 i).integrable_sq) (integrable_const _) fun ω => ?_
        have := hWbdd i ω
        nlinarith [abs_nonneg (W i ω), sq_abs (W i ω)]
      simpa using hb
    have hAeq : A n = fun ω => (n : ℝ)⁻¹ * (∑ i : Fin n, W i) ω := by
      funext ω
      rw [hAdef, hWdef]
      simp [Finset.sum_apply]
    rw [hAeq, variance_const_mul, hvarsum]
    have hsumle : ∑ i : Fin n, Var[W i; Pr] ≤ (n : ℝ) * M ^ 2 := by
      calc ∑ i : Fin n, Var[W i; Pr] ≤ ∑ _i : Fin n, M ^ 2 :=
            Finset.sum_le_sum fun i _ => hWvar i
        _ = (n : ℝ) * M ^ 2 := by simp
    calc ((n : ℝ)⁻¹) ^ 2 * ∑ i : Fin n, Var[W i; Pr]
        ≤ ((n : ℝ)⁻¹) ^ 2 * ((n : ℝ) * M ^ 2) := by
          exact mul_le_mul_of_nonneg_left hsumle (by positivity)
      _ = M ^ 2 / n := by field_simp
  -- Markov for the excess average
  have hMarkov : ∀ n : ℕ, 0 < n → Pr.real {ω | ε / 4 ≤ B n ω} ≤ η / 2 := by
    intro n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hexi : ∀ i : Fin n, Integrable (fun ω => max (Z n (i : ℕ) ω - M) 0) Pr :=
      fun i => hexiG n (i : ℕ)
    have hBint : Integrable (B n) Pr := by
      have hb : Integrable (fun ω => (n : ℝ)⁻¹ * ∑ i : Fin n, max (Z n (i : ℕ) ω - M) 0) Pr :=
        (integrable_finset_sum _ fun i _ => hexi i).const_mul _
      exact hb
    have hBle : ∫ ω, B n ω ∂Pr ≤ ρ := by
      have hBeq : ∫ ω, B n ω ∂Pr
          = (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, max (Z n (i : ℕ) ω - M) 0 ∂Pr := by
        rw [hBdef]
        simp only []
        rw [integral_const_mul, integral_finset_sum _ fun i _ => hexi i]
      have hsum_le : ∑ i : Fin n, ∫ ω, max (Z n (i : ℕ) ω - M) 0 ∂Pr ≤ (n : ℝ) * ρ := by
        calc ∑ i : Fin n, ∫ ω, max (Z n (i : ℕ) ω - M) 0 ∂Pr ≤ ∑ _i : Fin n, ρ :=
              Finset.sum_le_sum fun i _ => hMbound n (i : ℕ) i.isLt
          _ = (n : ℝ) * ρ := by simp
      rw [hBeq]
      calc (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, max (Z n (i : ℕ) ω - M) 0 ∂Pr
          ≤ (n : ℝ)⁻¹ * ((n : ℝ) * ρ) := mul_le_mul_of_nonneg_left hsum_le (by positivity)
        _ = ρ := by field_simp
    have hmk := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun ω => hBnn n ω) hBint (ε / 4)
    have hρη : ρ ≤ η * ε / 8 := min_le_right _ _
    have h4 : (ε / 4) * Pr.real {ω | ε / 4 ≤ B n ω} ≤ ρ := hmk.trans hBle
    nlinarith [measureReal_nonneg (μ := Pr) (s := {ω | ε / 4 ≤ B n ω})]
  -- Chebyshev for the truncated average
  have hcheb : ∀ n : ℕ, 0 < n →
      Pr.real {ω | ε / 4 ≤ |A n ω - (∫ ω, A n ω ∂Pr)|} ≤ M ^ 2 / n / (ε / 4) ^ 2 := by
    intro n hn
    have h := meas_ge_le_variance_div_sq (hAL2 n) (show (0 : ℝ) < ε / 4 by positivity)
    have h2 : Pr.real {ω | ε / 4 ≤ |A n ω - (∫ ω, A n ω ∂Pr)|}
        ≤ (ENNReal.ofReal (Var[A n; Pr] / (ε / 4) ^ 2)).toReal := by
      rw [measureReal_def]
      exact ENNReal.toReal_mono (by finiteness) h
    refine h2.trans ?_
    rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (by positivity))]
    have := hAvar n hn
    gcongr
  -- the Chebyshev bound and the row means settle down
  have hchebzero : Tendsto (fun n : ℕ => M ^ 2 / n / (ε / 4) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => (M ^ 2 / (ε / 4) ^ 2) * (n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using h1.const_mul (M ^ 2 / (ε / 4) ^ 2)
    exact h2.congr fun n => by ring
  have hsev : ∀ᶠ n : ℕ in atTop, |s n - c| ≤ ε / 4 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hs (ε / 4) (by positivity)
    filter_upwards [eventually_ge_atTop N] with n hn
    have h := hN n hn
    rw [Real.dist_eq] at h
    exact h.le
  filter_upwards [eventually_gt_atTop 0, hsev,
    hchebzero.eventually_lt_const (show (0 : ℝ) < η / 2 by positivity)] with n hn hsn hchn
  -- the deviation event is covered by the two small events
  have hsub : {x | ε ≤ ‖(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z n i x - c‖}
      ⊆ {ω | ε / 4 ≤ |A n ω - (∫ ω, A n ω ∂Pr)|} ∪ {ω | ε / 4 ≤ B n ω} := by
    intro x hx
    by_contra hcon
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hxx : ε ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z n i x - c| := by
      simpa [Real.norm_eq_abs] using hx
    rw [hsplit n x] at hxx
    have hEA := hAmean n hn
    have hρle : ρ ≤ ε / 4 := min_le_left _ _
    have hBx : |B n x| = B n x := abs_of_nonneg (hBnn n x)
    have he : A n x + B n x - c
        = ((A n x - (∫ ω, A n ω ∂Pr)) + ((∫ ω, A n ω ∂Pr) - s n) + (s n - c)) + B n x := by
      ring
    rw [he] at hxx
    have ht1 := abs_add_le ((A n x - (∫ ω, A n ω ∂Pr)) + ((∫ ω, A n ω ∂Pr) - s n) + (s n - c))
      (B n x)
    have ht2 := abs_add_le ((A n x - (∫ ω, A n ω ∂Pr)) + ((∫ ω, A n ω ∂Pr) - s n)) (s n - c)
    have ht3 := abs_add_le (A n x - (∫ ω, A n ω ∂Pr)) ((∫ ω, A n ω ∂Pr) - s n)
    linarith
  have hunion : Pr.real ({ω | ε / 4 ≤ |A n ω - (∫ ω, A n ω ∂Pr)|} ∪ {ω | ε / 4 ≤ B n ω})
      ≤ Pr.real {ω | ε / 4 ≤ |A n ω - (∫ ω, A n ω ∂Pr)|} + Pr.real {ω | ε / 4 ≤ B n ω} :=
    measureReal_union_le _ _
  have hmono : Pr.real {x | ε ≤ ‖(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z n i x - c‖}
      ≤ Pr.real ({ω | ε / 4 ≤ |A n ω - (∫ ω, A n ω ∂Pr)|} ∪ {ω | ε / 4 ≤ B n ω}) :=
    measureReal_mono hsub (by finiteness)
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  have hc1 := hcheb n hn
  have hc2 := hMarkov n hn
  linarith

end Vitali


/-! ## The triangular-array central limit theorem with a drifting row law -/

section TriangularCLT

/-- The law of the centred and scaled sample mean under `n` independent draws from `G`. -/
noncomputable def meanRootLaw (G : Measure ℝ) (n : ℕ) : Measure ℝ :=
  (Measure.pi fun _ : Fin n => G).map
    fun y => Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂G)

lemma meanRootCDF_eq (G : Measure ℝ) (n : ℕ) (x : ℝ)
    [IsProbabilityMeasure (Measure.pi fun _ : Fin n => G)] :
    meanRootCDF G n x = (meanRootLaw G n (Set.Iic x)).toReal := by
  rw [meanRootLaw, Measure.map_apply (by fun_prop) measurableSet_Iic]
  rfl

variable {G : ℕ → Measure ℝ} {Q₁ : Measure ℝ}

/-- **Triangular-array central limit theorem with a drifting row law.**

If the row laws `G n` converge weakly to `Q₁`, with converging means and variances, then the
law of the centred and scaled sample mean of `n` independent draws from `G n` converges weakly
to the centred normal law with the limiting variance. Degenerate limits (`Var = 0`) are
allowed. -/
theorem tendsto_meanRootLaw
    [∀ n, IsProbabilityMeasure (G n)] [IsProbabilityMeasure Q₁]
    (hG2 : ∀ n, MemLp (fun t : ℝ => t) 2 (G n)) (hQ2 : MemLp (fun t : ℝ => t) 2 Q₁)
    (hweak : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n => ∫ t, f t ∂(G n)) atTop (𝓝 (∫ t, f t ∂Q₁)))
    (hmean : Tendsto (fun n => ∫ t, t ∂(G n)) atTop (𝓝 (∫ t, t ∂Q₁)))
    (hvar : Tendsto (fun n => Var[fun t : ℝ => t; G n]) atTop (𝓝 Var[fun t : ℝ => t; Q₁]))
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ z, f z ∂(meanRootLaw (G n) n)) atTop
      (𝓝 (∫ z, f z ∂(gaussianReal 0 (Real.toNNReal Var[fun t : ℝ => t; Q₁])))) := by
  classical
  set m : ℕ → ℝ := fun n => ∫ t, t ∂(G n) with hm
  set v : ℕ → ℝ := fun n => Var[fun t : ℝ => t; G n] with hv
  set σ2 : ℝ := Var[fun t : ℝ => t; Q₁] with hσ2
  have hvnn : ∀ n, 0 ≤ v n := fun n => variance_nonneg _ _
  have hσ2nn : 0 ≤ σ2 := variance_nonneg _ _
  -- the canonical independent model with the prescribed row laws
  obtain ⟨Ω, mΩ, P, Y, hYmeas, hYlaw, hYindep, hPprob⟩ :=
    ProbabilityTheory.exists_hasLaw_indepFun (ι := ℕ × ℕ) (fun _ : ℕ × ℕ => ℝ)
      (fun p : ℕ × ℕ => G p.1)
  letI : MeasurableSpace Ω := mΩ
  haveI : IsProbabilityMeasure P := hPprob
  -- moments of the coordinates
  have hYint : ∀ p : ℕ × ℕ, ∫ ω, Y p ω ∂P = m p.1 := fun p =>
    (hYlaw p).integral_comp (f := fun t : ℝ => t) (by fun_prop)
  have hYL2 : ∀ p : ℕ × ℕ, MemLp (Y p) 2 P := by
    intro p
    have h : MemLp (fun t : ℝ => t) 2 (P.map (Y p)) := by rw [(hYlaw p).map_eq]; exact hG2 p.1
    have h2 := (memLp_map_measure_iff (by fun_prop) (hYmeas p).aemeasurable).1 h
    simpa [Function.comp_def] using h2
  have hYvar : ∀ p : ℕ × ℕ, Var[Y p; P] = v p.1 := by
    intro p
    have h : Var[fun t : ℝ => t; P.map (Y p)] = Var[Y p; P] := by
      rw [variance_map (by fun_prop) (hYmeas p).aemeasurable]
      rfl
    rw [← h, (hYlaw p).map_eq]
  -- the row law is the `n`-fold product
  have hinj : ∀ n : ℕ, Function.Injective (fun i : Fin n => ((n, (i : ℕ)) : ℕ × ℕ)) := by
    intro n a b hab
    exact Fin.val_injective (congrArg Prod.snd hab)
  have hpimap : ∀ n : ℕ, P.map (fun ω (i : Fin n) => Y (n, (i : ℕ)) ω)
      = Measure.pi (fun _ : Fin n => G n) := by
    intro n
    have hsub : iIndepFun (fun i : Fin n => Y (n, (i : ℕ))) P := hYindep.precomp (hinj n)
    rw [(iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => (hYmeas (n, (i : ℕ))).aemeasurable)).1 hsub]
    congr 1
    funext i
    exact (hYlaw (n, (i : ℕ))).map_eq
  -- the root law, realised on the common space
  have hroot : ∀ n : ℕ, meanRootLaw (G n) n
      = P.map (fun ω => (Real.sqrt n)⁻¹ * ∑ i : Fin n, (Y (n, (i : ℕ)) ω - m n)) := by
    intro n
    have hψmeas : Measurable (fun y : Fin n → ℝ => (Real.sqrt n)⁻¹ * ∑ i, (y i - m n)) := by
      fun_prop
    have h1 : meanRootLaw (G n) n
        = (Measure.pi fun _ : Fin n => G n).map
            (fun y : Fin n → ℝ => (Real.sqrt n)⁻¹ * ∑ i, (y i - m n)) := by
      rw [meanRootLaw]
      congr 1
      funext y
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hgoal : ∀ r S : ℝ, r ≠ 0 → r * r = (n : ℝ) →
            r * ((n : ℝ)⁻¹ * S - m n) = r⁻¹ * (S - (n : ℝ) * m n) := by
          intro r S hr0 hrsq
          rw [← hrsq]
          field_simp
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact hgoal (Real.sqrt n) _ (Real.sqrt_pos.2 hnR).ne'
          (Real.mul_self_sqrt hnR.le)
    rw [h1, ← hpimap n, Measure.map_map hψmeas (by fun_prop)]
    rfl
  -- second moments about the drifting centres
  have hsqmom : ∀ n : ℕ, ∫ t, (t - m n) ^ 2 ∂(G n) = v n := fun n =>
    (variance_eq_integral (by fun_prop)).symm
  have hsqmomQ : ∫ t, (t - ∫ u, u ∂Q₁) ^ 2 ∂Q₁ = σ2 := (variance_eq_integral (by fun_prop)).symm
  rcases hσ2nn.lt_or_eq with hσpos | hσzero
  case inr =>
    -- degenerate limit: the root converges to `0` in probability
    have hσ0 : σ2 = 0 := hσzero.symm
    set R : ℕ → Ω → ℝ :=
      fun n ω => (Real.sqrt n)⁻¹ * ∑ i : Fin n, (Y (n, (i : ℕ)) ω - m n) with hRdef
    have hZL2 : ∀ (n : ℕ) (i : Fin n),
        MemLp (fun ω => Y (n, (i : ℕ)) ω - m n) 2 P := fun n i =>
      (hYL2 (n, (i : ℕ))).sub (memLp_const _)
    have hZint : ∀ (n : ℕ) (i : Fin n), ∫ ω, (Y (n, (i : ℕ)) ω - m n) ∂P = 0 := by
      intro n i
      rw [integral_sub ((hYL2 _).integrable one_le_two) (integrable_const _)]
      simp [hYint (n, (i : ℕ))]
    have hfun : ∀ n : ℕ, (fun ω => ∑ i : Fin n, (Y (n, (i : ℕ)) ω - m n))
        = ∑ i : Fin n, fun ω => Y (n, (i : ℕ)) ω - m n := by
      intro n; funext ω; simp
    have hRmeas : ∀ n, Measurable (R n) := by intro n; simp only [hRdef]; fun_prop
    have hsumL2 : ∀ n : ℕ, MemLp (fun ω => ∑ i : Fin n, (Y (n, (i : ℕ)) ω - m n)) 2 P := by
      intro n
      have h := memLp_finset_sum' (Finset.univ : Finset (Fin n)) (fun i _ => hZL2 n i)
      rw [← hfun n] at h
      exact h
    have hRL2 : ∀ n, MemLp (R n) 2 P := by
      intro n
      simp only [hRdef]
      exact (hsumL2 n).const_mul _
    have hRmean : ∀ n, ∫ ω, R n ω ∂P = 0 := by
      intro n
      simp only [hRdef]
      rw [integral_const_mul,
        integral_finset_sum _ (fun i _ => (hZL2 n i).integrable one_le_two)]
      simp [hZint n]
    have hRvar : ∀ n : ℕ, 0 < n → Var[R n; P] = v n := by
      intro n hn
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin n)) : Set (Fin n))
          fun i j => IndepFun (fun ω => Y (n, (i : ℕ)) ω - m n)
            (fun ω => Y (n, (j : ℕ)) ω - m n) P := by
        intro i _ j _ hij
        exact ((hYindep.precomp (hinj n)).comp (fun _ => fun t : ℝ => t - m n)
          (fun _ => by fun_prop)).indepFun hij
      have hsum : Var[fun ω => ∑ i : Fin n, (Y (n, (i : ℕ)) ω - m n); P] = (n : ℝ) * v n := by
        rw [hfun n, IndepFun.variance_sum (fun i _ => hZL2 n i) hpair]
        simp only [variance_sub_const (hYmeas _).aestronglyMeasurable, hYvar]
        simp
      simp only [hRdef]
      rw [variance_const_mul, hsum, inv_pow, Real.sq_sqrt hnR.le]
      field_simp
    -- convergence in probability to zero, by Chebyshev
    have hRmeasure : TendstoInMeasure P R atTop 0 := by
      rw [tendstoInMeasure_iff_norm]
      intro r hr
      have hcheb : ∀ n : ℕ, P {ω | r ≤ ‖R n ω - (0 : Ω → ℝ) ω‖}
          ≤ ENNReal.ofReal (Var[R n; P] / r ^ 2) := by
        intro n
        have h := meas_ge_le_variance_div_sq (μ := P) (hRL2 n) hr
        rw [hRmean n] at h
        simpa using h
      have hto : Tendsto (fun n : ℕ => ENNReal.ofReal (Var[R n; P] / r ^ 2)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => Var[R n; P] / r ^ 2) atTop (𝓝 0) := by
          have heq : ∀ᶠ n : ℕ in atTop, Var[R n; P] / r ^ 2 = v n / r ^ 2 := by
            filter_upwards [eventually_gt_atTop 0] with n hn
            rw [hRvar n hn]
          refine Tendsto.congr' (heq.mono fun n h => h.symm) ?_
          have h2 := hvar.div_const (r ^ 2)
          rw [← hσzero] at h2
          simpa using h2
        have := (ENNReal.continuous_ofReal.tendsto 0).comp h1
        simpa using! this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto
        (fun n => zero_le) hcheb
    -- convergence in probability implies convergence in distribution
    have hdist := hRmeasure.tendstoInDistribution (fun n => (hRmeas n).aemeasurable)
    have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hdist.tendsto f
    have hlhs : ∀ n : ℕ, P.map (R n) = meanRootLaw (G n) n := fun n => (hroot n).symm
    have hrhs : P.map (0 : Ω → ℝ) = Measure.dirac (0 : ℝ) := by
      rw [show (0 : Ω → ℝ) = fun _ : Ω => (0 : ℝ) from rfl, Measure.map_const]
      simp
    have hgauss : gaussianReal 0 (Real.toNNReal σ2) = Measure.dirac (0 : ℝ) := by
      rw [hσ0]
      simp [gaussianReal_zero_var]
    simp only [hlhs, hrhs] at hint
    rw [hgauss]
    exact hint
  -- the standardisation constants
  set σ : ℝ := Real.sqrt σ2 with hσdef
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hσpos
  have hσsq : σ ^ 2 = σ2 := Real.sq_sqrt hσ2nn
  set c : ℕ → ℝ := fun n => (Real.sqrt n * σ)⁻¹ with hcdef
  set X : (n : ℕ) → Fin n → Ω → ℝ := fun n i ω => c n * (Y (n, (i : ℕ)) ω - m n) with hXdef
  have hXmeas : ∀ (n : ℕ) (i : Fin n), Measurable (X n i) := by
    intro n i; simp only [hXdef]; fun_prop
  have hXindep : ∀ n : ℕ, iIndepFun (X n) P := by
    intro n
    have hsub : iIndepFun (fun i : Fin n => Y (n, (i : ℕ))) P := hYindep.precomp (hinj n)
    exact hsub.comp (fun _ => fun t : ℝ => c n * (t - m n)) (fun _ => by fun_prop)
  have hXL2 : ∀ (n : ℕ) (i : Fin n), MemLp (X n i) 2 P := fun n i =>
    ((hYL2 (n, (i : ℕ))).sub (memLp_const _)).const_mul _
  have hXmean : ∀ (n : ℕ) (i : Fin n), ∫ ω, X n i ω ∂P = 0 := by
    intro n i
    have hint : Integrable (Y (n, (i : ℕ))) P := (hYL2 _).integrable one_le_two
    simp only [hXdef]
    rw [integral_const_mul, integral_sub hint (integrable_const _)]
    simp [hYint (n, (i : ℕ))]
  have hXvarterm : ∀ (n : ℕ) (i : Fin n), Var[X n i; P] = c n ^ 2 * v n := by
    intro n i
    simp only [hXdef]
    rw [variance_const_mul, variance_sub_const (hYmeas _).aestronglyMeasurable,
      hYvar (n, (i : ℕ))]
  have hcsq : ∀ n : ℕ, 0 < n → c n ^ 2 = ((n : ℝ) * σ2)⁻¹ := by
    intro n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    simp only [hcdef, inv_pow, mul_pow, Real.sq_sqrt hnR.le, hσsq]
  have hXvar : Tendsto (fun n => ∑ i, Var[X n i; P]) atTop (𝓝 1) := by
    have heq : ∀ᶠ n : ℕ in atTop, (∑ i, Var[X n i; P]) = v n / σ2 := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      simp only [hXvarterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        hcsq n hn]
      field_simp
    refine Tendsto.congr' (heq.mono fun n h => h.symm) ?_
    have h := hvar.div_const σ2
    rwa [div_self hσpos.ne'] at h
  -- the Lindeberg condition, from the Vitali uniform-integrability brick
  have hXlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P) atTop (𝓝 0) := by
    intro ε hε
    have hterm : ∀ n : ℕ, 0 < n → ∀ i : Fin n,
        (∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P)
          = c n ^ 2 *
              ∫ t in {t : ℝ | ε * σ * Real.sqrt n < |t - m n|}, (t - m n) ^ 2 ∂(G n) := by
      intro n hn i
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hrpos : (0 : ℝ) < Real.sqrt n * σ := mul_pos (Real.sqrt_pos.2 hnR) hσ0
      have hcpos : 0 < c n := by simp only [hcdef]; exact inv_pos.2 hrpos
      have hSmeas : MeasurableSet {t : ℝ | ε * σ * Real.sqrt n < |t - m n|} :=
        measurableSet_lt measurable_const (by fun_prop)
      have hiff : ∀ z : ℝ, ε < |c n * z| ↔ ε * σ * Real.sqrt n < |z| := by
        intro z
        rw [abs_mul, abs_of_pos hcpos]
        simp only [hcdef]
        rw [inv_mul_eq_div, lt_div_iff₀ hrpos,
          show ε * (Real.sqrt n * σ) = ε * σ * Real.sqrt n by ring]
      have hpre : {ω | ε < |X n i ω|}
          = (Y (n, (i : ℕ))) ⁻¹' {t : ℝ | ε * σ * Real.sqrt n < |t - m n|} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_preimage, hXdef]
        exact hiff _
      rw [hpre, ← setIntegral_map hSmeas
        (f := fun t : ℝ => (c n * (t - m n)) ^ 2) (by fun_prop) (hYmeas _).aemeasurable,
        (hYlaw (n, (i : ℕ))).map_eq]
      simp only [mul_pow]
      exact integral_const_mul _ _
    have hsum : ∀ᶠ n : ℕ in atTop,
        (∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P)
          = σ2⁻¹ * ∫ t in {t : ℝ | ε * σ * Real.sqrt n < |t - m n|}, (t - m n) ^ 2 ∂(G n) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [Finset.sum_congr rfl (fun i _ => hterm n hn i)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcsq n hn]
      rw [← mul_assoc]
      congr 1
      field_simp
    have hthr : Tendsto (fun n : ℕ => ε * σ * Real.sqrt n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity)
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hV := tendsto_setIntegral_sq_tail (F := G) (Q := Q₁) (a := m) (b := ∫ u, u ∂Q₁)
      hG2 hQ2 hweak hmean (by simpa only [hsqmom, hsqmomQ] using hvar) hthr
    refine Tendsto.congr' (hsum.mono fun n h => h.symm) ?_
    simpa using hV.const_mul σ2⁻¹
  -- the Lindeberg central limit theorem, then a fixed rescaling by `σ`
  have hclt := lindeberg_clt (P := P) (P' := gaussianReal 0 1) hXmeas hXindep hXL2 hXmean hXvar
    hXlin (Z := (id : ℝ → ℝ)) HasLaw.id
  have hcomp := TendstoInDistribution.continuous_comp
    (g := fun z : ℝ => σ * z) (by fun_prop) hclt
  have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hcomp.tendsto f
  have hlhs : ∀ n : ℕ, P.map ((fun z : ℝ => σ * z) ∘ (fun ω => ∑ i, X n i ω))
      = meanRootLaw (G n) n := by
    intro n
    rw [hroot n]
    congr 1
    funext ω
    simp only [Function.comp_def, hXdef, hcdef, ← Finset.mul_sum, ← mul_assoc]
    congr 1
    field_simp
  have hrhs : (gaussianReal 0 1).map ((fun z : ℝ => σ * z) ∘ (id : ℝ → ℝ))
      = gaussianReal 0 (Real.toNNReal σ2) := by
    have h1 : ((fun z : ℝ => σ * z) ∘ (id : ℝ → ℝ)) = fun z : ℝ => σ * z := rfl
    rw [h1, gaussianReal_map_const_mul σ]
    congr 1
    · simp
    · refine NNReal.eq ?_
      simp [Real.coe_toNNReal σ2 hσ2nn, hσsq]
  simp only [hlhs, hrhs] at hint
  exact hint

end TriangularCLT

/-! ## Convergence along the class, and membership of the empirical sequence -/

section MeanBootstrap

variable {Q : Measure ℝ} {F : ℕ → Measure ℝ} {Pr : Measure Ω} {X : ℕ → Ω → ℝ} {α : ℝ}

/-- **Convergence of the sampling distribution of the mean along the class.**

Along every sequence of the mean class, the sampling distribution function of the centred and
scaled sample mean converges to the normal distribution function with mean zero and the limiting
variance. -/
theorem mean_root_cdf_tendsto [IsProbabilityMeasure Q]
    -- USER-INPUT: the limit law is square-integrable, so its mean and variance exist
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q)
    -- USER-INPUT: the limiting variance is nonzero; the bootstrap for a mean is inconsistent
    -- without a finite nonzero variance
    (hQvar : 0 < Var[fun t : ℝ => t; Q])
    -- USER-INPUT: the sequence of laws belongs to the mean class
    (hF : F ∈ meanSeqClass Q) (x : ℝ) :
    Tendsto (fun n => meanRootCDF (F n) n x) atTop
      (𝓝 (normalCDF 0 (Real.toNNReal Var[fun t : ℝ => t; Q]) x)) := by
  classical
  -- Replace the unconstrained `n = 0` entry of the sequence by `Q`.
  set F' : ℕ → Measure ℝ := fun n => if n = 0 then Q else F n with hF'def
  have hF'eq : ∀ n : ℕ, 0 < n → F' n = F n := by
    intro n hn; simp only [hF'def, if_neg hn.ne']
  haveI hF'prob : ∀ n, IsProbabilityMeasure (F' n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa only [hF'def, if_pos rfl] using ‹IsProbabilityMeasure Q›
    · rw [hF'eq n hn]; exact hF.1 n hn
  obtain ⟨-, hF2, hFcdf, hFmean, hFvar⟩ := hF
  have hF'2 : ∀ n, MemLp (fun t : ℝ => t) 2 (F' n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa only [hF'def, if_pos rfl] using hQ2
    · rw [hF'eq n hn]; exact hF2 n
  have hF'cdf : ∀ y : ℝ, ContinuousAt (fun t => (Q (Set.Iic t)).toReal) y →
      Tendsto (fun n => ((F' n) (Set.Iic y)).toReal) atTop (𝓝 ((Q (Set.Iic y)).toReal)) := by
    intro y hy
    refine (hFcdf y hy).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hF'eq n hn]
  have hF'mean : Tendsto (fun n => ∫ t, t ∂(F' n)) atTop (𝓝 (∫ t, t ∂Q)) := by
    refine hFmean.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hF'eq n hn]
  have hF'var : Tendsto (fun n => Var[fun t : ℝ => t; F' n]) atTop
      (𝓝 Var[fun t : ℝ => t; Q]) := by
    refine hFvar.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hF'eq n hn]
  -- distribution-function convergence upgrades to weak convergence, then the array CLT applies
  have hF'weak := tendsto_integral_of_tendsto_cdf hF'prob hF'cdf
  have huni := tendsto_meanRootLaw hF'2 hQ2 hF'weak hF'mean hF'var
  haveI hpi : ∀ n : ℕ, IsProbabilityMeasure (Measure.pi fun _ : Fin n => F' n) := fun n =>
    isProbabilityMeasure_pi_const n (F' n)
  haveI hroot : ∀ n : ℕ, IsProbabilityMeasure (meanRootLaw (F' n) n) := by
    intro n
    haveI := hpi n
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  set ρs : ℕ → ProbabilityMeasure ℝ := fun n => ⟨meanRootLaw (F' n) n, hroot n⟩ with hρs
  set ρ : ProbabilityMeasure ℝ :=
    ⟨gaussianReal 0 (Real.toNNReal Var[fun t : ℝ => t; Q]), inferInstance⟩ with hρ
  have hconv : Tendsto ρs atTop (𝓝 ρ) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 huni
  -- the nondegenerate normal limit has no atoms, so the portmanteau theorem applies at `Iic x`
  have hvne : Real.toNNReal Var[fun t : ℝ => t; Q] ≠ 0 := (Real.toNNReal_pos.mpr hQvar).ne'
  haveI : NullSingletonClass (gaussianReal 0 (Real.toNNReal Var[fun t : ℝ => t; Q])) :=
    nullSingletonClass_gaussianReal hvne
  have hfront : (ρ : Measure ℝ) (frontier (Set.Iic x)) = 0 := by
    rw [hρ]; simp [frontier_Iic]
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv hfront
  have htoreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport
  have hL : ∀ n : ℕ, ((ρs n : Measure ℝ) (Set.Iic x)).toReal = meanRootCDF (F' n) n x := by
    intro n
    haveI := hpi n
    exact (meanRootCDF_eq (F' n) n x).symm
  have hR : ((ρ : Measure ℝ) (Set.Iic x)).toReal
      = normalCDF 0 (Real.toNNReal Var[fun t : ℝ => t; Q]) x := rfl
  simp only [Function.comp_def, hL, hR] at htoreal
  refine htoreal.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hF'eq n hn]

/-- **The empirical sequence belongs to the mean class, almost surely.**

For an independent identically distributed sample from a square-integrable law, the sequence of
empirical measures satisfies the three defining convergences of the mean class with probability
one. -/
theorem empirical_mem_meanSeqClass [IsProbabilityMeasure Pr] [IsProbabilityMeasure Q]
    -- LEAN-ONLY: the observations are measurable
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the observations are independent
    (hindep : iIndepFun X Pr)
    -- USER-INPUT: the observations are identically distributed with law `Q`
    (hlaw : HasLaw (X 0) Q Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: the sampling law is square-integrable, so means and variances converge
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q) :
    ∀ᵐ ω ∂Pr, (fun n => empiricalMeasure fun i : Fin n => X i ω) ∈ meanSeqClass Q := by
  classical
  -- Transfer the first two moments of `X 0` from the limit law `Q`.
  have hidQ : IdentDistrib (X 0) (fun t : ℝ => t) Pr Q :=
    ⟨(hmeas 0).aemeasurable, measurable_id.aemeasurable, by rw [hlaw.map_eq, Measure.map_id']⟩
  have hXmem : MemLp (X 0) 2 Pr := hidQ.memLp_iff.mpr hQ2
  have hXint : Integrable (X 0) Pr := hXmem.integrable one_le_two
  have hXsqint : Integrable (fun ω => X 0 ω ^ 2) Pr := hXmem.integrable_sq
  have hmeanQ : Pr[X 0] = ∫ t, t ∂Q := hlaw.integral_comp (f := fun t : ℝ => t) (by fun_prop)
  have hsqQ : Pr[fun ω => X 0 ω ^ 2] = ∫ t, t ^ 2 ∂Q :=
    hlaw.integral_comp (f := fun t : ℝ => t ^ 2) (by fun_prop)
  -- Three strong laws: of `X`, of `X²`, and of the indicator of a half-line at each point.
  have hSLLN_mean : ∀ᵐ ω ∂Pr, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) atTop (𝓝 (∫ t, t ∂Q)) := by
    rw [← hmeanQ]; exact strong_law_ae X hXint (fun i j hij => hindep.indepFun hij) hident
  have hSLLN_sq : ∀ᵐ ω ∂Pr, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω ^ 2) atTop (𝓝 (∫ t, t ^ 2 ∂Q)) := by
    rw [← hsqQ]
    exact strong_law_ae (fun i ω => X i ω ^ 2) hXsqint
      (fun i j hij =>
        (hindep.comp (fun _ => fun t : ℝ => t ^ 2) (fun _ => by fun_prop)).indepFun hij)
      (fun i => (hident i).comp (by fun_prop : Measurable fun t : ℝ => t ^ 2))
  have hCDF : ∀ y : ℝ, ∀ᵐ ω ∂Pr, Tendsto
      (fun n : ℕ => ((empiricalMeasure fun i : Fin n => X i ω) (Set.Iic y)).toReal)
      atTop (𝓝 ((Q (Set.Iic y)).toReal)) := by
    intro y
    have hind_meas : Measurable (Set.indicator (Set.Iic y) (1 : ℝ → ℝ)) :=
      measurable_one.indicator measurableSet_Iic
    have hb : Integrable (fun ω => Set.indicator (Set.Iic y) (1 : ℝ → ℝ) (X 0 ω)) Pr := by
      refine (memLp_top_of_bound ((hind_meas.comp (hmeas 0)).aestronglyMeasurable) 1 ?_).integrable
        le_top
      filter_upwards with ω
      calc ‖Set.indicator (Set.Iic y) (1 : ℝ → ℝ) (X 0 ω)‖
          ≤ ‖(1 : ℝ → ℝ) (X 0 ω)‖ := norm_indicator_le_norm_self _ _
        _ = 1 := by simp
    have hPrind : Pr[fun ω => Set.indicator (Set.Iic y) (1 : ℝ → ℝ) (X 0 ω)]
        = (Q (Set.Iic y)).toReal := by
      have h := hlaw.integral_comp (f := Set.indicator (Set.Iic y) (1 : ℝ → ℝ))
        hind_meas.aestronglyMeasurable
      rw [Function.comp_def] at h
      rw [h]; exact integral_indicator_one measurableSet_Iic
    have hsl := strong_law_ae (fun i ω => Set.indicator (Set.Iic y) (1 : ℝ → ℝ) (X i ω)) hb
      (fun i j hij =>
        (hindep.comp (fun _ => Set.indicator (Set.Iic y) (1 : ℝ → ℝ))
          (fun _ => hind_meas)).indepFun hij)
      (fun i => (hident i).comp hind_meas)
    filter_upwards [hsl] with ω hω
    rw [← hPrind]
    refine hω.congr' (Filter.Eventually.of_forall fun n => ?_)
    simp only [empiricalMeasure_Iic_toReal, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun k => Set.indicator (Set.Iic y) (1 : ℝ → ℝ) (X k ω)) n]
  have hCDFrat : ∀ᵐ ω ∂Pr, ∀ q : ℚ, Tendsto
      (fun n : ℕ => ((empiricalMeasure fun i : Fin n => X i ω) (Set.Iic (q : ℝ))).toReal)
      atTop (𝓝 ((Q (Set.Iic (q : ℝ))).toReal)) := ae_all_iff.mpr (fun q => hCDF (q : ℝ))
  -- Assemble the five clauses on the intersection of the almost sure events.
  filter_upwards [hSLLN_mean, hSLLN_sq, hCDFrat] with ω hmean hsq hcdf
  -- The mean and second-moment integrals against the empirical measure, as sample averages.
  have hEmean : (fun n => ∫ t, t ∂(empiricalMeasure fun i : Fin n => X i ω))
      = fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω := by
    funext n
    rw [← Fin.sum_univ_eq_sum_range (fun i => X i ω) n]
    exact integral_empiricalMeasure (fun i : Fin n => X i ω) (fun t : ℝ => t)
  have hEsq : (fun n => ∫ t, t ^ 2 ∂(empiricalMeasure fun i : Fin n => X i ω))
      = fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω ^ 2 := by
    funext n
    rw [← Fin.sum_univ_eq_sum_range (fun i => X i ω ^ 2) n]
    exact integral_empiricalMeasure (fun i : Fin n => X i ω) (fun t : ℝ => t ^ 2)
  refine ⟨fun n hn => isProbabilityMeasure_empiricalMeasure hn _,
    fun n => memLp_id_empiricalMeasure _, ?_, ?_, ?_⟩
  · -- Weak convergence: rational sandwich at each continuity point.
    intro x hx
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.continuousAt_iff] at hx
    obtain ⟨δ, hδpos, hδ⟩ := hx (ε / 3) (by positivity)
    obtain ⟨q1, hq1l, hq1r⟩ := exists_rat_btwn (show x - δ < x by linarith)
    obtain ⟨q2, hq2l, hq2r⟩ := exists_rat_btwn (show x < x + δ by linarith)
    have hc1 := hcdf q1
    have hc2 := hcdf q2
    rw [Metric.tendsto_atTop] at hc1 hc2
    obtain ⟨N1, hN1⟩ := hc1 (ε / 3) (by positivity)
    obtain ⟨N2, hN2⟩ := hc2 (ε / 3) (by positivity)
    refine ⟨max N1 N2, fun n hn => ?_⟩
    haveI := isFiniteMeasure_empiricalMeasure (fun i : Fin n => X i ω)
    have hmono : ∀ a b : ℝ, a ≤ b →
        ((empiricalMeasure fun i : Fin n => X i ω) (Set.Iic a)).toReal
          ≤ ((empiricalMeasure fun i : Fin n => X i ω) (Set.Iic b)).toReal := fun a b hab =>
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr hab))
    have hQ1 : |(Q (Set.Iic (q1 : ℝ))).toReal - (Q (Set.Iic x)).toReal| < ε / 3 := by
      have hd : dist (q1 : ℝ) x < δ := by
        rw [Real.dist_eq, abs_of_neg (by linarith : (q1 : ℝ) - x < 0)]; linarith
      have := hδ hd; rwa [Real.dist_eq] at this
    have hQ2' : |(Q (Set.Iic (q2 : ℝ))).toReal - (Q (Set.Iic x)).toReal| < ε / 3 := by
      have hd : dist (q2 : ℝ) x < δ := by
        rw [Real.dist_eq, abs_of_pos (by linarith : (0 : ℝ) < (q2 : ℝ) - x)]; linarith
      have := hδ hd; rwa [Real.dist_eq] at this
    have hb1 := hN1 n (le_of_max_le_left hn)
    have hb2 := hN2 n (le_of_max_le_right hn)
    have hle1 := hmono (q1 : ℝ) x hq1r.le
    have hle2 := hmono x (q2 : ℝ) hq2l.le
    rw [Real.dist_eq] at hb1 hb2 ⊢
    rw [abs_lt] at hQ1 hQ2' hb1 hb2 ⊢
    constructor <;> linarith [hQ1.1, hQ1.2, hQ2'.1, hQ2'.2, hb1.1, hb1.2, hb2.1, hb2.2, hle1, hle2]
  · -- Convergence of the mean.
    rw [hEmean]; exact hmean
  · -- Convergence of the variance.
    have hVarQ : Var[fun t : ℝ => t; Q] = (∫ t, t ^ 2 ∂Q) - (∫ t, t ∂Q) ^ 2 :=
      variance_eq_sub hQ2
    rw [hVarQ]
    have hcongr : ∀ᶠ n in atTop,
        (∫ t, t ^ 2 ∂(empiricalMeasure fun i : Fin n => X i ω))
            - (∫ t, t ∂(empiricalMeasure fun i : Fin n => X i ω)) ^ 2
          = Var[fun t : ℝ => t; empiricalMeasure fun i : Fin n => X i ω] := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      haveI := isProbabilityMeasure_empiricalMeasure hn (fun i : Fin n => X i ω)
      exact (variance_eq_sub (memLp_id_empiricalMeasure _)).symm
    refine Tendsto.congr' hcongr ?_
    have h1 : Tendsto (fun n => ∫ t, t ^ 2 ∂(empiricalMeasure fun i : Fin n => X i ω)) atTop
        (𝓝 (∫ t, t ^ 2 ∂Q)) := by rw [hEsq]; exact hsq
    have h2 : Tendsto (fun n => ∫ t, t ∂(empiricalMeasure fun i : Fin n => X i ω)) atTop
        (𝓝 (∫ t, t ∂Q)) := by rw [hEmean]; exact hmean
    exact h1.sub (h2.pow 2)

/-- **Consistency of the nonparametric bootstrap for a mean.**

The bootstrap sampling distribution — the sampling distribution of the root computed at the
empirical measure — is uniformly close to the true sampling distribution, almost surely. -/
theorem bootstrap_mean_consistent [IsProbabilityMeasure Pr] [IsProbabilityMeasure Q]
    -- LEAN-ONLY: the observations are measurable
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent identically distributed observations with law `Q`
    (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) Q Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: square-integrable sampling law with nonzero variance
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q) (hQvar : 0 < Var[fun t : ℝ => t; Q]) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n => supCDFDist (meanRootCDF Q n)
      (meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n)) atTop (𝓝 0) := by
  set Jlim := normalCDF 0 (Real.toNNReal Var[fun t : ℝ => t; Q]) with hJlim
  have hvne : Real.toNNReal Var[fun t : ℝ => t; Q] ≠ 0 := (Real.toNNReal_pos.mpr hQvar).ne'
  have hcont : Continuous Jlim := continuous_normalCDF 0 hvne
  have hcdflim : IsCDF Jlim := isCDF_normalCDF 0 _
  have hQcdf : ∀ n, IsCDF (meanRootCDF Q n) := fun n => by
    haveI := isProbabilityMeasure_pi_const n Q; exact isCDF_meanRootCDF Q n
  have hQconv : ∀ x, Tendsto (fun n => meanRootCDF Q n x) atTop (𝓝 (Jlim x)) := fun x =>
    mean_root_cdf_tendsto hQ2 hQvar (const_mem_meanSeqClass Q hQ2) x
  filter_upwards [empirical_mem_meanSeqClass hmeas hindep hlaw hident hQ2] with ω hω
  have hEcdf : ∀ n, IsCDF (meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n) := fun n => by
    haveI := isProbabilityMeasure_pi_empirical n X ω; exact isCDF_meanRootCDF _ n
  have hEconv : ∀ x, Tendsto
      (fun n => meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n x) atTop (𝓝 (Jlim x)) :=
    fun x => mean_root_cdf_tendsto hQ2 hQvar hω x
  have hA : Tendsto (fun n => supCDFDist (meanRootCDF Q n) Jlim) atTop (𝓝 0) :=
    tendsto_supCDFDist_zero hQcdf hcont hcdflim hQconv
  have hB : Tendsto (fun n =>
      supCDFDist Jlim (meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n)) atTop (𝓝 0) := by
    have h := tendsto_supCDFDist_zero hEcdf hcont hcdflim hEconv
    simpa only [supCDFDist_comm] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
    (h := fun n => supCDFDist (meanRootCDF Q n) Jlim
      + supCDFDist Jlim (meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n))
    tendsto_const_nhds (by simpa using hA.add hB) (fun n => ?_) (fun n => ?_)
  · exact supCDFDist_nonneg (hQcdf n) (hEcdf n)
  · exact supCDFDist_triangle_of_isCDF (hQcdf n) hcdflim (hEcdf n)

/-- **The sampling distribution at `Q` is the law of the root.** At the data-generating law the
value of `meanRootCDF Q n` is the true distribution function of the centred-and-scaled sample
mean of the i.i.d. sample, so `meanRootCDF` is genuinely the object being bootstrapped. -/
private lemma meanRootCDF_eq_law_of_root [IsProbabilityMeasure Pr] [IsProbabilityMeasure Q]
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) Q Pr)
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr) (n : ℕ) (x : ℝ) :
    meanRootCDF Q n x
      = (Pr {ω | Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i : Fin n, X i ω) - ∫ t, t ∂Q) ≤ x}).toReal := by
  have hφmeas : Measurable (fun ω (i : Fin n) => X i ω) :=
    measurable_pi_lambda _ (fun i => hmeas i)
  have hmap : Pr.map (fun ω (i : Fin n) => X i ω) = Measure.pi (fun _ : Fin n => Q) := by
    have h := (iIndepFun_iff_map_fun_eq_pi_map (μ := Pr) (f := fun i : Fin n => X (i : ℕ))
      (fun i => (hmeas (i : ℕ)).aemeasurable)).1 (hindep.precomp Fin.val_injective)
    rw [h]
    congr 1; funext i
    exact ((hident (i : ℕ)).map_eq).trans hlaw.map_eq
  have hSmeas : Measurable fun y : Fin n → ℝ =>
      Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂Q) := by fun_prop
  unfold meanRootCDF
  rw [← hmap, Measure.map_apply hφmeas (measurableSet_le hSmeas measurable_const)]
  rfl

/-- The `n`-fold product of an empirical measure is the uniform law on resamples. -/
private lemma pi_empiricalMeasure {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    (Measure.pi fun _ : Fin n => empiricalMeasure x)
      = ((n : ℝ≥0∞) ^ n)⁻¹ • ∑ j : Fin n → Fin n, Measure.dirac (fun i => x (j i)) := by
  classical
  haveI := isProbabilityMeasure_empiricalMeasure hn x
  refine Measure.pi_eq (fun s hs => ?_)
  have hbox : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  set T : Fin n → Finset (Fin n) := fun i => Finset.univ.filter (fun a => x a ∈ s i) with hT
  -- the candidate on a box
  have hL : (((n : ℝ≥0∞) ^ n)⁻¹ • ∑ j : Fin n → Fin n,
        Measure.dirac (fun i => x (j i))) (Set.pi Set.univ s)
      = ((n : ℝ≥0∞) ^ n)⁻¹ * ((Fintype.piFinset T).card : ℝ≥0∞) := by
    simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
    congr 1
    have hstep : ∀ j : Fin n → Fin n,
        (Measure.dirac (fun i => x (j i))) (Set.pi Set.univ s)
          = if (∀ i, x (j i) ∈ s i) then (1 : ℝ≥0∞) else 0 := by
      intro j
      rw [Measure.dirac_apply' _ hbox, Set.indicator_apply]
      simp only [Set.mem_univ_pi, Pi.one_apply]
    simp only [hstep, Finset.sum_boole]
    congr 2
    ext j
    simp [hT, Fintype.mem_piFinset]
  -- the product of the marginals
  have hR : ∀ i : Fin n, (empiricalMeasure x) (s i)
      = (n : ℝ≥0∞)⁻¹ * (((T i).card : ℕ) : ℝ≥0∞) := by
    intro i
    unfold empiricalMeasure
    simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
    congr 1
    have hstep : ∀ a : Fin n, (Measure.dirac (x a)) (s i)
        = if x a ∈ s i then (1 : ℝ≥0∞) else 0 := by
      intro a
      rw [Measure.dirac_apply' _ (hs i), Set.indicator_apply]
      simp only [Pi.one_apply]
    simp only [hstep, Finset.sum_boole]
    rfl
  rw [hL]
  simp only [hR, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_piFinset, Nat.cast_prod, ← ENNReal.inv_pow]

/-- The bootstrap sampling distribution function of the mean as a resampling average. -/
private lemma meanRootCDF_empiricalMeasure_eq {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (t : ℝ) :
    meanRootCDF (empiricalMeasure x) n t
      = (((n : ℝ≥0∞) ^ n)⁻¹ * ∑ j : Fin n → Fin n,
          (if Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, x (j i)) - (n : ℝ)⁻¹ * (∑ i, x i)) ≤ t
            then (1 : ℝ≥0∞) else 0)).toReal := by
  classical
  have hmean : ∫ u, u ∂(empiricalMeasure x) = (n : ℝ)⁻¹ * ∑ i, x i :=
    integral_empiricalMeasure x (fun u => u)
  have hA : MeasurableSet {y : Fin n → ℝ |
      Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ u, u ∂(empiricalMeasure x)) ≤ t} := by
    refine measurableSet_le ?_ measurable_const
    fun_prop
  unfold meanRootCDF
  rw [pi_empiricalMeasure hn x]
  simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  congr 2
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Measure.dirac_apply' _ hA, Set.indicator_apply]
  simp only [Set.mem_setOf_eq, hmean, Pi.one_apply]

/-- Measurability of the bootstrap sampling distribution function in the sample. -/
private lemma measurable_meanRootCDF_empirical (hmeas : ∀ i, Measurable (X i))
    (n : ℕ) (t : ℝ) :
    Measurable fun ω => meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n t := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hemp : ∀ ω : Ω, (fun i : Fin 0 => X i ω) = fun i : Fin 0 => (0 : ℝ) :=
      fun ω => funext (fun i => i.elim0)
    simp only [hemp]
    exact measurable_const
  · have hfun : (fun ω => meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n t)
        = fun ω => (((n : ℝ≥0∞) ^ n)⁻¹ * ∑ j : Fin n → Fin n,
            (if Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i : Fin n, X (j i) ω)
                - (n : ℝ)⁻¹ * (∑ i : Fin n, X (i : ℕ) ω)) ≤ t
              then (1 : ℝ≥0∞) else 0)).toReal :=
      funext fun ω => meanRootCDF_empiricalMeasure_eq hn (fun i => X i ω) t
    rw [hfun]
    refine ENNReal.measurable_toReal.comp (Measurable.const_mul (Finset.measurable_sum _ ?_) _)
    intro j _
    refine Measurable.ite (measurableSet_le ?_ measurable_const) measurable_const measurable_const
    have h1 : Measurable fun ω : Ω => ∑ i : Fin n, X (j i) ω :=
      Finset.measurable_sum (Finset.univ : Finset (Fin n)) (fun i _ => hmeas (j i))
    have h2 : Measurable fun ω : Ω => ∑ i : Fin n, X (i : ℕ) ω :=
      Finset.measurable_sum (Finset.univ : Finset (Fin n)) (fun i _ => hmeas (i : ℕ))
    exact ((h1.const_mul _).sub (h2.const_mul _)).const_mul _

/-- **Measurability of the bootstrap critical value.**

The estimated `1 − α` quantile is measurable in the sample. Two steps: the bootstrap sampling
distribution function is, level by level, an explicit average over the `nⁿ` resampling maps
(`measurable_meanRootCDF_empirical`), and the generalized inverse of a measurably parametrised
family of distribution functions is measurable (`measurable_cdfPseudoInverse`).

**Private-lemma amendment (level range).** `hα` is added: for `p ∉ (0,1)` the sublevel set
`{t | p ≤ F t}` is empty or all of `ℝ` and the `sInf` returns its junk value, so the
sublevel-set-is-a-ray identity behind the quantile's measurability fails. The only call site
(`bootstrap_mean_coverage`) carries it. -/
private lemma measurable_bootstrapCriticalValue (hmeas : ∀ i, Measurable (X i))
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    Measurable fun ω => cdfPseudoInverse
      (Jmean n (empiricalMeasure fun i : Fin n => X i ω)) (1 - α) := by
  refine measurable_cdfPseudoInverse (fun ω => isCDF_Jmean n _) (by linarith [hα.2])
    (by linarith [hα.1]) (fun t => ?_)
  have hJ : ∀ ω : Ω, Jmean n (empiricalMeasure fun i : Fin n => X i ω) t
      = meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n t := by
    intro ω
    haveI := isProbabilityMeasure_pi_empirical n X ω
    rw [Jmean_eq_meanRootCDF]
  simp only [hJ]
  exact measurable_meanRootCDF_empirical hmeas n t

/-- **Asymptotic coverage of the bootstrap confidence bound for a mean.**

The one-sided bootstrap confidence set for the mean, obtained by comparing the root to the
`1 − α` quantile of the bootstrap sampling distribution, has asymptotic coverage `1 − α`. -/
theorem bootstrap_mean_coverage [IsProbabilityMeasure Pr] [IsProbabilityMeasure Q]
    -- LEAN-ONLY: the observations are measurable
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent identically distributed observations with law `Q`
    (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) Q Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: square-integrable sampling law with nonzero variance
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q) (hQvar : 0 < Var[fun t : ℝ => t; Q])
    -- USER-INPUT: nominal level strictly between `0` and `1`
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => (Pr {ω |
        Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * (∑ i : Fin n, X i ω) - ∫ t, t ∂Q)
          ≤ cdfPseudoInverse (meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n)
              (1 - α)}).toReal)
      atTop (𝓝 (1 - α)) := by
  have hvne : Real.toNNReal Var[fun t : ℝ => t; Q] ≠ 0 := (Real.toNNReal_pos.mpr hQvar).ne'
  -- Convergence of the sampling distribution functions along the class, packaged for `Jmean`.
  have hJconv : ∀ G ∈ meanSeqClass Q, ∀ x, Tendsto (fun n => Jmean n (G n) x) atTop
      (𝓝 (normalCDF 0 (Real.toNNReal Var[fun t : ℝ => t; Q]) x)) := by
    intro G hG x
    have hagree : ∀ n, Jmean n (G n) x = meanRootCDF (G n) n x := by
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin 0 => G 0) := by
          rw [Measure.pi_of_empty]; infer_instance
        rw [Jmean_eq_meanRootCDF]
      · haveI := hG.1 n hn
        haveI := isProbabilityMeasure_pi_const n (G n)
        rw [Jmean_eq_meanRootCDF]
    simp_rw [hagree]
    exact mean_root_cdf_tendsto hQ2 hQvar hG x
  -- The field `J := Jmean` is the sampling distribution of the root at the true law.
  have hJP : ∀ (n : ℕ) (x : ℝ), Jmean n Q x
      = (Pr {ω | Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i : Fin n, X i ω) - ∫ t, t ∂Q) ≤ x}).toReal := by
    intro n x
    haveI := isProbabilityMeasure_pi_const n Q
    rw [Jmean_eq_meanRootCDF, meanRootCDF_eq_law_of_root hmeas hindep hlaw hident]
  have hRmeas : ∀ n : ℕ, Measurable fun ω : Ω =>
      Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i : Fin n, X i ω) - ∫ t, t ∂Q) := by
    intro n
    have hsum : Measurable fun ω : Ω => ∑ i : Fin n, X i ω :=
      Finset.measurable_sum _ (fun i _ => hmeas i)
    fun_prop
  have hconv := tendsto_bootstrapCoverage (P := Q) (J := Jmean)
    (Jlim := normalCDF 0 (Real.toNNReal Var[fun t : ℝ => t; Q])) (C_P := meanSeqClass Q)
    (Phat := fun n ω => empiricalMeasure fun i : Fin n => X i ω)
    (R := fun n ω => Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i : Fin n, X i ω) - ∫ t, t ∂Q)) (α := α)
    (const_mem_meanSeqClass Q hQ2) hJconv (continuous_normalCDF 0 hvne) (isCDF_normalCDF 0 _)
    isCDF_Jmean (empirical_mem_meanSeqClass hmeas hindep hlaw hident hQ2) hα
    (strictIncAt_normalCDF 0 hvne _) hJP hRmeas
    (fun n => measurable_bootstrapCriticalValue hmeas hα n)
  refine hconv.congr fun n => ?_
  have hset : {ω | Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i : Fin n, X i ω) - ∫ t, t ∂Q)
        ≤ cdfPseudoInverse (Jmean n (empiricalMeasure fun i : Fin n => X i ω)) (1 - α)}
      = {ω | Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i : Fin n, X i ω) - ∫ t, t ∂Q)
        ≤ cdfPseudoInverse (meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n) (1 - α)} := by
    ext ω
    haveI := isProbabilityMeasure_pi_empirical n X ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, Jmean_eq_meanRootCDF]
  rw [hset]

/-! ## The studentized root and the bootstrap-t -/

/-- The **plug-in sample variance in mean-square form**: the average of the squares minus the
square of the average. Both sides vanish for an empty sample. -/
private lemma sampleVariance_eq {n : ℕ} (y : Fin n → ℝ) :
    sampleVariance y = (n : ℝ)⁻¹ * ∑ i, (y i) ^ 2 - ((n : ℝ)⁻¹ * ∑ j, y j) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [sampleVariance]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set b : ℝ := (n : ℝ)⁻¹ * ∑ j, y j with hb
  have hexp : ∀ i : Fin n, (y i - b) ^ 2 = (y i) ^ 2 - 2 * b * y i + b ^ 2 := fun i => by ring
  have hsum : ∑ i, (y i - b) ^ 2
      = (∑ i, (y i) ^ 2) - 2 * b * (∑ i, y i) + (n : ℝ) * b ^ 2 := by
    rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    simp [Finset.card_univ, mul_comm]
  have hsy : (∑ j, y j) = (n : ℝ) * b := by rw [hb]; field_simp
  rw [sampleVariance, ← hb, hsum, hsy]
  field_simp
  ring

/-- **Two-variable continuous mapping to a constant, in probability.** If `A n → a` and
`B n → b` in probability and `g` is continuous at `(a, b)`, then `g (A n, B n) → g (a, b)` in
probability. Mathlib has the continuous-mapping theorem for convergence in distribution but
not this elementary two-variable version for convergence in probability to a constant. -/
private lemma tendstoInMeasure_comp₂_of_continuousAt {μ : Measure Ω}
    {A B : ℕ → Ω → ℝ} {a b : ℝ} {g : ℝ × ℝ → ℝ}
    (hA : TendstoInMeasure μ A atTop fun _ => a)
    (hB : TendstoInMeasure μ B atTop fun _ => b)
    (hg : ContinuousAt g (a, b)) :
    TendstoInMeasure μ (fun n ω => g (A n ω, B n ω)) atTop fun _ => g (a, b) := by
  rw [tendstoInMeasure_iff_norm] at hA hB ⊢
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hg ε hε
  have hsub : ∀ n : ℕ, {ω | ε ≤ ‖g (A n ω, B n ω) - g (a, b)‖}
      ⊆ {ω | δ ≤ ‖A n ω - a‖} ∪ {ω | δ ≤ ‖B n ω - b‖} := by
    intro n ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    have hd : dist ((A n ω, B n ω) : ℝ × ℝ) (a, b) < δ := by
      rw [Prod.dist_eq]
      exact max_lt (by rw [dist_eq_norm]; exact hcon.1) (by rw [dist_eq_norm]; exact hcon.2)
    have hgd := hball hd
    rw [dist_eq_norm] at hgd
    exact absurd hω (not_le.2 hgd)
  have hlim : Tendsto (fun n : ℕ => μ {ω | δ ≤ ‖A n ω - a‖} + μ {ω | δ ≤ ‖B n ω - b‖})
      atTop (𝓝 0) := by
    have := (hA δ hδ).add (hB δ hδ)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => zero_le) fun n => ?_
  exact (measure_mono (hsub n)).trans (measure_union_le _ _)

/-- **Shifting a null sequence by a converging sequence of constants.** -/
private lemma tendstoInMeasure_add_tendsto {μ : Measure Ω} {A : ℕ → Ω → ℝ} {c : ℕ → ℝ} {a : ℝ}
    (hA : TendstoInMeasure μ A atTop fun _ => (0 : ℝ)) (hc : Tendsto c atTop (𝓝 a)) :
    TendstoInMeasure μ (fun n ω => A n ω + c n) atTop fun _ => a := by
  rw [tendstoInMeasure_iff_norm] at hA ⊢
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop,
      {ω | ε ≤ ‖A n ω + c n - a‖} ⊆ {ω | ε / 2 ≤ ‖A n ω - 0‖} := by
    filter_upwards [hc.eventually (Metric.ball_mem_nhds a (show (0 : ℝ) < ε / 2 by positivity))]
      with n hn ω hω
    simp only [Set.mem_setOf_eq, sub_zero] at hω ⊢
    have hcn : ‖c n - a‖ < ε / 2 := by
      rw [← dist_eq_norm]; exact hn
    have htri : ‖A n ω + c n - a‖ ≤ ‖A n ω‖ + ‖c n - a‖ := by
      have : A n ω + c n - a = A n ω + (c n - a) := by ring
      rw [this]; exact norm_add_le _ _
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hA (ε / 2) (by positivity)) (Eventually.of_forall fun n => zero_le) ?_
  exact hev.mono fun n hn => measure_mono hn

/-- **Convergence of the studentized sampling distribution along the class.**

Along every sequence of the mean class the sampling distribution function of the studentized
sample mean converges to the standard normal distribution function — the studentized root is an
asymptotic pivot. -/
theorem studentized_root_cdf_tendsto [IsProbabilityMeasure Q]
    -- USER-INPUT: the limit law is square-integrable
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q)
    -- USER-INPUT: the limiting variance is nonzero
    (hQvar : 0 < Var[fun t : ℝ => t; Q])
    -- USER-INPUT: the sequence of laws belongs to the mean class
    (hF : F ∈ meanSeqClass Q) (x : ℝ) :
    Tendsto (fun n => studentizedRootCDF (F n) n x) atTop (𝓝 (stdNormalCDF x)) := by
  classical
  -- Replace the unconstrained `n = 0` entry of the sequence by `Q`.
  set G : ℕ → Measure ℝ := fun n => if n = 0 then Q else F n with hGdef
  have hGeq : ∀ n : ℕ, 0 < n → G n = F n := by
    intro n hn; simp only [hGdef, if_neg hn.ne']
  haveI hGprob : ∀ n, IsProbabilityMeasure (G n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa only [hGdef, if_pos rfl] using ‹IsProbabilityMeasure Q›
    · rw [hGeq n hn]; exact hF.1 n hn
  obtain ⟨-, hF2, hFcdf, hFmean, hFvar⟩ := hF
  have hG2 : ∀ n, MemLp (fun t : ℝ => t) 2 (G n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa only [hGdef, if_pos rfl] using hQ2
    · rw [hGeq n hn]; exact hF2 n
  have hGcdf : ∀ y : ℝ, ContinuousAt (fun t => (Q (Set.Iic t)).toReal) y →
      Tendsto (fun n => ((G n) (Set.Iic y)).toReal) atTop (𝓝 ((Q (Set.Iic y)).toReal)) := by
    intro y hy
    refine (hFcdf y hy).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hGeq n hn]
  have hGmean : Tendsto (fun n => ∫ t, t ∂(G n)) atTop (𝓝 (∫ t, t ∂Q)) := by
    refine hFmean.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hGeq n hn]
  have hGvar : Tendsto (fun n => Var[fun t : ℝ => t; G n]) atTop
      (𝓝 Var[fun t : ℝ => t; Q]) := by
    refine hFvar.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hGeq n hn]
  have hGweak := tendsto_integral_of_tendsto_cdf hGprob hGcdf
  -- the limiting variance and standard deviation
  set σ2 : ℝ := Var[fun t : ℝ => t; Q] with hσ2def
  set σ : ℝ := Real.sqrt σ2 with hσdef
  have hσpos : 0 < σ := Real.sqrt_pos.2 hQvar
  have hσsq : σ ^ 2 = σ2 := Real.sq_sqrt hQvar.le
  have hvne : Real.toNNReal σ2 ≠ 0 := (Real.toNNReal_pos.mpr hQvar).ne'
  -- the second moments of the sequence converge, by the variance identity
  have hsqQ : ∫ t, t ^ 2 ∂Q = σ2 + (∫ t, t ∂Q) ^ 2 := by
    have h := variance_eq_sub (μ := Q) (X := fun t : ℝ => t) hQ2
    have h2 : Q[(fun t : ℝ => t) ^ 2] = ∫ t, t ^ 2 ∂Q := by norm_num
    rw [h2] at h
    have h3 : Q[fun t : ℝ => t] = ∫ t, t ∂Q := rfl
    rw [h3] at h
    rw [← hσ2def] at h
    linarith
  have hsqG : ∀ n : ℕ, ∫ t, t ^ 2 ∂(G n)
      = Var[fun t : ℝ => t; G n] + (∫ t, t ∂(G n)) ^ 2 := by
    intro n
    have h := variance_eq_sub (μ := G n) (X := fun t : ℝ => t) (hG2 n)
    have h2 : (G n)[(fun t : ℝ => t) ^ 2] = ∫ t, t ^ 2 ∂(G n) := by norm_num
    rw [h2] at h
    have h3 : (G n)[fun t : ℝ => t] = ∫ t, t ∂(G n) := rfl
    rw [h3] at h
    linarith
  have hGsq : Tendsto (fun n => ∫ t, t ^ 2 ∂(G n)) atTop (𝓝 (∫ t, t ^ 2 ∂Q)) := by
    rw [hsqQ]
    exact (hGvar.add (hGmean.pow 2)).congr fun n => (hsqG n).symm
  -- the canonical independent model with the prescribed row laws
  obtain ⟨Ω₀, mΩ₀, P, Y, hYmeas, hYlaw, hYindep, hPprob⟩ :=
    ProbabilityTheory.exists_hasLaw_indepFun (ι := ℕ × ℕ) (fun _ : ℕ × ℕ => ℝ)
      (fun p : ℕ × ℕ => G p.1)
  letI : MeasurableSpace Ω₀ := mΩ₀
  haveI : IsProbabilityMeasure P := hPprob
  have hinj : ∀ n : ℕ, Function.Injective (fun i : Fin n => ((n, (i : ℕ)) : ℕ × ℕ)) := by
    intro n a b hab
    exact Fin.val_injective (congrArg Prod.snd hab)
  have hpimap : ∀ n : ℕ, P.map (fun ω (i : Fin n) => Y (n, (i : ℕ)) ω)
      = Measure.pi (fun _ : Fin n => G n) := by
    intro n
    have hsub : iIndepFun (fun i : Fin n => Y (n, (i : ℕ))) P := hYindep.precomp (hinj n)
    rw [(iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => (hYmeas (n, (i : ℕ))).aemeasurable)).1 hsub]
    congr 1
    funext i
    exact (hYlaw (n, (i : ℕ))).map_eq
  -- moments of the coordinates
  have hYL2 : ∀ p : ℕ × ℕ, MemLp (Y p) 2 P := by
    intro p
    have h : MemLp (fun t : ℝ => t) 2 (P.map (Y p)) := by rw [(hYlaw p).map_eq]; exact hG2 p.1
    have h2 := (memLp_map_measure_iff (by fun_prop) (hYmeas p).aemeasurable).1 h
    simpa [Function.comp_def] using h2
  have hYint : ∀ p : ℕ × ℕ, ∫ ω, Y p ω ∂P = ∫ t, t ∂(G p.1) := fun p =>
    (hYlaw p).integral_comp (f := fun t : ℝ => t) (by fun_prop)
  have hYsq : ∀ p : ℕ × ℕ, ∫ ω, (Y p ω) ^ 2 ∂P = ∫ t, t ^ 2 ∂(G p.1) := fun p =>
    (hYlaw p).integral_comp (f := fun t : ℝ => t ^ 2) (by fun_prop)
  have hYvar : ∀ p : ℕ × ℕ, Var[Y p; P] = Var[fun t : ℝ => t; G p.1] := by
    intro p
    have h : Var[fun t : ℝ => t; P.map (Y p)] = Var[Y p; P] := by
      rw [variance_map (by fun_prop) (hYmeas p).aemeasurable]
      rfl
    rw [← h, (hYlaw p).map_eq]
  -- the sample mean, the sample second moment and the sample variance on the common space
  set Am : ℕ → Ω₀ → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i : Fin n, Y (n, (i : ℕ)) ω with hAmdef
  set Bm : ℕ → Ω₀ → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i : Fin n, (Y (n, (i : ℕ)) ω) ^ 2 with hBmdef
  set V : ℕ → Ω₀ → ℝ := fun n ω => Bm n ω - (Am n ω) ^ 2 with hVdef
  set R : ℕ → Ω₀ → ℝ := fun n ω => Real.sqrt n * (Am n ω - ∫ t, t ∂(G n)) with hRdef
  set W : ℕ → Ω₀ → ℝ := fun n ω => R n ω / Real.sqrt (V n ω) with hWdef
  have hAmmeas : ∀ n, Measurable (Am n) := by intro n; simp only [hAmdef]; fun_prop
  have hBmmeas : ∀ n, Measurable (Bm n) := by intro n; simp only [hBmdef]; fun_prop
  have hVmeas : ∀ n, Measurable (V n) := by
    intro n; simp only [hVdef]; exact (hBmmeas n).sub ((hAmmeas n).pow_const 2)
  have hRmeas : ∀ n, Measurable (R n) := by
    intro n; simp only [hRdef]; exact measurable_const.mul ((hAmmeas n).sub measurable_const)
  have hWmeas : ∀ n, Measurable (W n) := by
    intro n; simp only [hWdef]
    exact (hRmeas n).div (hVmeas n).sqrt
  -- the sample second moment converges in probability, by the uniformly integrable weak law
  have hBmprob : TendstoInMeasure P Bm atTop (fun _ => ∫ t, t ^ 2 ∂Q) := by
    have hZindep : ∀ n : ℕ,
        iIndepFun (fun i : Fin n => (fun ω => (Y (n, (i : ℕ)) ω) ^ 2)) P := by
      intro n
      exact (hYindep.precomp (hinj n)).comp (fun _ => fun t : ℝ => t ^ 2)
        (fun _ => by fun_prop)
    have hUI : ∀ ρ : ℝ, 0 < ρ → ∃ M : ℝ, 0 ≤ M ∧
        ∀ n i : ℕ, i < n → ∫ ω, max ((Y (n, i) ω) ^ 2 - M) 0 ∂P ≤ ρ := by
      intro ρ hρ
      obtain ⟨M, hM0, hM⟩ := exists_uniform_sq_trunc (F := G) (Q := Q) hG2 hQ2 hGweak hGsq hρ
      refine ⟨M, hM0, fun n i _ => ?_⟩
      have htr : ∫ ω, max ((Y (n, i) ω) ^ 2 - M) 0 ∂P
          = ∫ t, max (t ^ 2 - M) 0 ∂(G n) :=
        (hYlaw (n, i)).integral_comp (f := fun t : ℝ => max (t ^ 2 - M) 0) (by fun_prop)
      rw [htr]
      exact hM n
    have hraw := tendstoInMeasure_rowMean_of_uniform (Pr := P)
      (Z := fun n i ω => (Y (n, i) ω) ^ 2) (s := fun n => ∫ t, t ^ 2 ∂(G n))
      (c := ∫ t, t ^ 2 ∂Q) (fun n i => by fun_prop) hZindep (fun n i ω => sq_nonneg _)
      (fun n i => (hYL2 (n, i)).integrable_sq) (fun n i _ => hYsq (n, i)) hGsq hUI
    intro ε hε
    refine (hraw ε hε).congr fun n => ?_
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, hBmdef, Fin.sum_univ_eq_sum_range fun i => (Y (n, i) ω) ^ 2]
  -- the sample mean converges in probability, by Chebyshev on the centred row average
  have hZL2 : ∀ (n : ℕ) (i : Fin n),
      MemLp (fun ω => Y (n, (i : ℕ)) ω - ∫ t, t ∂(G n)) 2 P := fun n i =>
    (hYL2 (n, (i : ℕ))).sub (memLp_const _)
  have hZint : ∀ (n : ℕ) (i : Fin n),
      ∫ ω, (Y (n, (i : ℕ)) ω - ∫ t, t ∂(G n)) ∂P = 0 := by
    intro n i
    rw [integral_sub ((hYL2 _).integrable one_le_two) (integrable_const _)]
    simp [hYint (n, (i : ℕ))]
  have hfun : ∀ n : ℕ, (fun ω => ∑ i : Fin n, (Y (n, (i : ℕ)) ω - ∫ t, t ∂(G n)))
      = ∑ i : Fin n, fun ω => Y (n, (i : ℕ)) ω - ∫ t, t ∂(G n) := by
    intro n; funext ω; simp
  have hsumL2 : ∀ n : ℕ,
      MemLp (fun ω => ∑ i : Fin n, (Y (n, (i : ℕ)) ω - ∫ t, t ∂(G n))) 2 P := by
    intro n
    have h := memLp_finset_sum' (Finset.univ : Finset (Fin n)) (fun i _ => hZL2 n i)
    rw [← hfun n] at h
    exact h
  set D : ℕ → Ω₀ → ℝ :=
    fun n ω => (n : ℝ)⁻¹ * ∑ i : Fin n, (Y (n, (i : ℕ)) ω - ∫ t, t ∂(G n)) with hDdef
  have hDL2 : ∀ n, MemLp (D n) 2 P := by
    intro n; simp only [hDdef]; exact (hsumL2 n).const_mul _
  have hDmean : ∀ n, ∫ ω, D n ω ∂P = 0 := by
    intro n
    simp only [hDdef]
    rw [integral_const_mul,
      integral_finset_sum _ (fun i _ => (hZL2 n i).integrable one_le_two)]
    simp [hZint n]
  have hDvar : ∀ n : ℕ, 0 < n → Var[D n; P] = Var[fun t : ℝ => t; G n] / n := by
    intro n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin n)) : Set (Fin n))
        fun i j => IndepFun (fun ω => Y (n, (i : ℕ)) ω - ∫ t, t ∂(G n))
          (fun ω => Y (n, (j : ℕ)) ω - ∫ t, t ∂(G n)) P := by
      intro i _ j _ hij
      exact ((hYindep.precomp (hinj n)).comp
        (fun _ => fun t : ℝ => t - ∫ t, t ∂(G n)) (fun _ => by fun_prop)).indepFun hij
    have hsum : Var[fun ω => ∑ i : Fin n, (Y (n, (i : ℕ)) ω - ∫ t, t ∂(G n)); P]
        = (n : ℝ) * Var[fun t : ℝ => t; G n] := by
      rw [hfun n, IndepFun.variance_sum (fun i _ => hZL2 n i) hpair]
      simp only [variance_sub_const (hYmeas _).aestronglyMeasurable, hYvar]
      simp
    simp only [hDdef]
    rw [variance_const_mul, hsum]
    field_simp
  have hDprob : TendstoInMeasure P D atTop (fun _ => (0 : ℝ)) := by
    rw [tendstoInMeasure_iff_norm]
    intro r hr
    have hcheb : ∀ᶠ n : ℕ in atTop, P {ω | r ≤ ‖D n ω - (0 : ℝ)‖}
        ≤ ENNReal.ofReal (Var[fun t : ℝ => t; G n] / n / r ^ 2) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have h := meas_ge_le_variance_div_sq (μ := P) (hDL2 n) hr
      rw [hDmean n, hDvar n hn] at h
      simpa using h
    have hto : Tendsto
        (fun n : ℕ => ENNReal.ofReal (Var[fun t : ℝ => t; G n] / n / r ^ 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => Var[fun t : ℝ => t; G n] / n / r ^ 2) atTop (𝓝 0) := by
        have h0 := hGvar.mul tendsto_inv_atTop_nhds_zero_nat
        rw [mul_zero] at h0
        have h2 := h0.div_const (r ^ 2)
        simpa [div_eq_mul_inv] using h2
      have := (ENNReal.continuous_ofReal.tendsto 0).comp h1
      simpa using! this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hto
      (Eventually.of_forall fun n => zero_le) hcheb
  have hAmeq : ∀ n : ℕ, 0 < n → ∀ ω, Am n ω = D n ω + ∫ t, t ∂(G n) := by
    intro n hn ω
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hs : ∑ i : Fin n, (Y (n, (i : ℕ)) ω - ∫ t, t ∂(G n))
        = (∑ i : Fin n, Y (n, (i : ℕ)) ω) - (n : ℝ) * ∫ t, t ∂(G n) := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.card_univ, mul_comm]
    simp only [hAmdef, hDdef, hs]
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hnR, one_mul]
    ring
  have hAmprob : TendstoInMeasure P Am atTop (fun _ => ∫ t, t ∂Q) := by
    have hshift := tendstoInMeasure_add_tendsto hDprob hGmean
    intro ε hε
    refine (hshift ε hε).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, hAmeq n hn ω]
  -- the sample variance converges in probability to the limiting variance
  have hVprob : TendstoInMeasure P V atTop (fun _ => σ2) := by
    have hg : ContinuousAt (fun p : ℝ × ℝ => p.1 - p.2 ^ 2)
        ((∫ t, t ^ 2 ∂Q), (∫ t, t ∂Q)) := by fun_prop
    have h := tendstoInMeasure_comp₂_of_continuousAt hBmprob hAmprob hg
    have hval : (∫ t, t ^ 2 ∂Q) - (∫ t, t ∂Q) ^ 2 = σ2 := by rw [hsqQ]; ring
    intro ε hε
    have h2 := h ε hε
    simp only [hval] at h2
    exact h2
  -- the numerator converges in distribution to the centred normal law
  have hroot : ∀ n : ℕ, P.map (R n) = meanRootLaw (G n) n := by
    intro n
    rw [meanRootLaw, ← hpimap n, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hRdist : TendstoInDistribution R atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal σ2)) := by
    refine ⟨fun n => (hRmeas n).aemeasurable, measurable_id.aemeasurable, ?_⟩
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
    intro f
    have h := tendsto_meanRootLaw hG2 hQ2 hGweak hGmean hGvar f
    simp only [ProbabilityMeasure.coe_mk, Measure.map_id]
    exact h.congr fun n => by rw [hroot n]
  -- Slutsky, with the denominator kept away from zero by a fixed truncation
  set gtr : ℝ × ℝ → ℝ := fun p => p.1 / Real.sqrt (max p.2 (σ2 / 2)) with hgtrdef
  have hden : ∀ p : ℝ × ℝ, Real.sqrt (max p.2 (σ2 / 2)) ≠ 0 := by
    intro p
    have h1 : (0 : ℝ) < σ2 / 2 := by positivity
    exact (Real.sqrt_pos.2 (lt_of_lt_of_le h1 (le_max_right _ _))).ne'
  have hgtrcont : Continuous gtr := by
    simp only [hgtrdef]
    exact continuous_fst.div
      (Real.continuous_sqrt.comp (continuous_snd.max continuous_const)) hden
  have hXdist := hRdist.continuous_comp_prodMk_of_tendstoInMeasure_const hgtrcont hVprob
    (fun n => (hVmeas n).aemeasurable)
  have hWsub : TendstoInMeasure P (W - fun n ω => gtr (R n ω, V n ω)) atTop 0 := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have hVn := (tendstoInMeasure_iff_norm.1 hVprob) (σ2 / 2) (by positivity)
    have hsub : ∀ n : ℕ,
        {ω | ε ≤ ‖(W - fun n ω => gtr (R n ω, V n ω)) n ω - (0 : Ω₀ → ℝ) ω‖}
          ⊆ {ω | σ2 / 2 ≤ ‖V n ω - σ2‖} := by
      intro n ω hω
      simp only [Pi.sub_apply, Pi.zero_apply, sub_zero, Set.mem_setOf_eq] at hω ⊢
      by_contra hcon
      push_neg at hcon
      have hV2 : σ2 / 2 ≤ V n ω := by
        rw [Real.norm_eq_abs] at hcon
        have hab := abs_lt.1 hcon
        linarith [hab.1]
      have hEq : gtr (R n ω, V n ω) = W n ω := by
        simp only [hgtrdef, hWdef, max_eq_left hV2]
      rw [hEq] at hω
      simp only [sub_self, norm_zero] at hω
      linarith
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVn
      (fun n => zero_le) fun n => measure_mono (hsub n)
  have hWdist := tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => gtr (R n ω, V n ω)) W (fun z : ℝ => gtr (id z, σ2)) hXdist hWsub
    (fun n => (hWmeas n).aemeasurable)
  -- identify the limit law as the standard normal
  have hlimmeas : (gaussianReal 0 (Real.toNNReal σ2)).map (fun z : ℝ => gtr (id z, σ2))
      = gaussianReal 0 1 := by
    have hfun : (fun z : ℝ => gtr (id z, σ2)) = fun z : ℝ => z / σ := by
      funext z
      simp only [hgtrdef, id_eq, max_eq_left (by linarith : σ2 / 2 ≤ σ2), hσdef]
    rw [hfun, gaussianReal_map_div_const σ]
    have h1 : NNReal.mk (σ ^ 2) (sq_nonneg σ) = Real.toNNReal σ2 := by
      refine NNReal.eq ?_
      simp [Real.coe_toNNReal σ2 hQvar.le, hσsq]
    rw [h1, div_self hvne]
    congr 1
    simp
  -- portmanteau at `Iic x`
  haveI hWmap : ∀ n, IsProbabilityMeasure (P.map (W n)) := fun n =>
    Measure.isProbabilityMeasure_map (hWmeas n).aemeasurable
  set ρs : ℕ → ProbabilityMeasure ℝ := fun n => ⟨P.map (W n), hWmap n⟩ with hρs
  set ρ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩ with hρ
  have hconv : Tendsto ρs atTop (𝓝 ρ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hWdist.tendsto f
    simp only [ProbabilityMeasure.coe_mk, hlimmeas] at h
    simpa only [hρs, hρ, ProbabilityMeasure.coe_mk] using h
  haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hfront : (ρ : Measure ℝ) (frontier (Set.Iic x)) = 0 := by
    rw [hρ]; simp [frontier_Iic]
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv hfront
  have htoreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport
  have hL : ∀ n : ℕ, ((ρs n : Measure ℝ) (Set.Iic x)).toReal = studentizedRootCDF (G n) n x := by
    intro n
    have hSmeas : MeasurableSet {y : Fin n → ℝ |
        Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂(G n)) /
          Real.sqrt (sampleVariance y) ≤ x} := by
      refine measurableSet_le ?_ measurable_const
      have h1 : Measurable fun y : Fin n → ℝ => sampleVariance y := by
        simp only [sampleVariance]; fun_prop
      exact (measurable_const.mul ((by fun_prop : Measurable fun y : Fin n → ℝ =>
        (n : ℝ)⁻¹ * (∑ i, y i)).sub measurable_const)).div h1.sqrt
    have hpre : (fun (ω : Ω₀) (i : Fin n) => Y (n, (i : ℕ)) ω) ⁻¹'
        {y : Fin n → ℝ | Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂(G n)) /
          Real.sqrt (sampleVariance y) ≤ x} = W n ⁻¹' Set.Iic x := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Iic, hWdef, hRdef, hVdef, hAmdef,
        hBmdef, sampleVariance_eq]
    have h1' : ((ρs n : Measure ℝ) (Set.Iic x)) = P (W n ⁻¹' Set.Iic x) := by
      simp only [hρs, ProbabilityMeasure.coe_mk]
      exact Measure.map_apply (hWmeas n) measurableSet_Iic
    have h2' : studentizedRootCDF (G n) n x = (P (W n ⁻¹' Set.Iic x)).toReal := by
      rw [studentizedRootCDF, ← hpimap n, Measure.map_apply (by fun_prop) hSmeas, hpre]
    rw [h1', h2']
  have hR' : ((ρ : Measure ℝ) (Set.Iic x)).toReal = stdNormalCDF x := rfl
  simp only [Function.comp_def, hL, hR'] at htoreal
  refine htoreal.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hGeq n hn]

/-- **Consistency of the bootstrap-t.**

The bootstrap sampling distribution of the studentized root, computed at the empirical measure,
is uniformly close to the true one, almost surely. -/
theorem bootstrap_t_consistent [IsProbabilityMeasure Pr] [IsProbabilityMeasure Q]
    -- LEAN-ONLY: the observations are measurable
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent identically distributed observations with law `Q`
    (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) Q Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: square-integrable sampling law with nonzero variance
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q) (hQvar : 0 < Var[fun t : ℝ => t; Q]) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n => supCDFDist (studentizedRootCDF Q n)
      (studentizedRootCDF (empiricalMeasure fun i : Fin n => X i ω) n)) atTop (𝓝 0) := by
  have hcont : Continuous stdNormalCDF := continuous_stdNormalCDF
  have hcdflim : IsCDF stdNormalCDF := isCDF_stdNormalCDF
  have hQcdf : ∀ n, IsCDF (studentizedRootCDF Q n) := fun n => by
    haveI := isProbabilityMeasure_pi_const n Q; exact isCDF_studentizedRootCDF Q n
  have hQconv : ∀ x, Tendsto (fun n => studentizedRootCDF Q n x) atTop (𝓝 (stdNormalCDF x)) :=
    fun x => studentized_root_cdf_tendsto hQ2 hQvar (const_mem_meanSeqClass Q hQ2) x
  filter_upwards [empirical_mem_meanSeqClass hmeas hindep hlaw hident hQ2] with ω hω
  have hEcdf : ∀ n, IsCDF (studentizedRootCDF (empiricalMeasure fun i : Fin n => X i ω) n) :=
    fun n => by haveI := isProbabilityMeasure_pi_empirical n X ω; exact isCDF_studentizedRootCDF _ n
  have hEconv : ∀ x, Tendsto
      (fun n => studentizedRootCDF (empiricalMeasure fun i : Fin n => X i ω) n x) atTop
      (𝓝 (stdNormalCDF x)) := fun x => studentized_root_cdf_tendsto hQ2 hQvar hω x
  have hA : Tendsto (fun n => supCDFDist (studentizedRootCDF Q n) stdNormalCDF) atTop (𝓝 0) :=
    tendsto_supCDFDist_zero hQcdf hcont hcdflim hQconv
  have hB : Tendsto (fun n =>
      supCDFDist stdNormalCDF (studentizedRootCDF (empiricalMeasure fun i : Fin n => X i ω) n))
      atTop (𝓝 0) := by
    have h := tendsto_supCDFDist_zero hEcdf hcont hcdflim hEconv
    simpa only [supCDFDist_comm] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
    (h := fun n => supCDFDist (studentizedRootCDF Q n) stdNormalCDF
      + supCDFDist stdNormalCDF (studentizedRootCDF (empiricalMeasure fun i : Fin n => X i ω) n))
    tendsto_const_nhds (by simpa using hA.add hB) (fun n => ?_) (fun n => ?_)
  · exact supCDFDist_nonneg (hQcdf n) (hEcdf n)
  · exact supCDFDist_triangle_of_isCDF (hQcdf n) hcdflim (hEcdf n)

end MeanBootstrap

end StatLean.HypothesisTesting
