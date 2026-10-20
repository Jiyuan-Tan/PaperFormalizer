module
public import StatLean.HypothesisTesting.Bootstrap.Consistency

@[expose] public section

/-!
# Bootstrap hypothesis tests

To turn a test statistic into a test one needs a critical value, and the bootstrap supplies one
by resampling. The essential point is *which* law to resample from: not the empirical measure of
the data, but an estimate `Qhat n` that **satisfies the constraints of the null hypothesis**.
Resampling from the unrestricted empirical measure estimates the distribution of the statistic
under the law that actually generated the data, whether or not it satisfies the null; the
resulting test has asymptotic rejection probability `α` even against alternatives, and so has no
power. Estimating under the null constraints makes the critical value behave, under an
alternative, like the critical value at some null law, against which a divergent statistic
rejects with probability tending to one.

This file contains:

* `MemClassInProbability` — membership of a random sequence of laws in a sequence class, in
  probability;
* `tendsto_bootstrapTest_level` — the rejection probability of the bootstrap test tends to the
  nominal level under the null;
* `tendsto_bootstrapTest_power_one` — the accompanying consistency claim against fixed
  alternatives.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 18 (Bootstrap and
Subsampling Methods), §18.5 (Hypothesis Testing), Theorem 18.5.1 (a bootstrap test has
asymptotic level `α`). (`TSH4 §18.5 Thm 18.5.1`.)

**Designed deviation (metric-free formulation, and its cost here).** The reference states this
result with a metric `d` on laws: smoothness is `d(P_n, P) → 0 ⇒ G_n(·, P_n) ⇒ G(·, P)`, and the
estimator satisfies `d(Qhat n, P) → 0` in probability. We keep this area's sequence-class
formulation instead. The convergence hypothesis translates directly. The *in probability*
hypothesis does not: a sequence class ties the index `n` of the law to the sample size, so one
cannot simply pass to a subsequence of laws and keep the pairing. `MemClassInProbability`
therefore asks that along a further subsequence there exist, almost surely, a class member
**agreeing with the random sequence at those indices** — the index-preserving form of the
"fill in the missing indices with the limit law" device that the metric argument performs
implicitly. Almost sure membership implies it, with the identity subsequence.

**Deviation from the reference hypotheses (strict increase at the quantile).** The reference
assumes only that the limit law `G(·, P)` is continuous. Continuity alone does not give
convergence of the `1 − α` quantiles: a flat stretch of the limit distribution function at
height `1 − α` leaves the quantile undetermined, and the estimated quantiles may then oscillate
across it. The quantile step needs strict increase at that point, exactly as in the confidence
set theory of this area, and we state it explicitly rather than leave it implicit.

**Proof formalization notes.**
* `G` is the distribution function field of the **statistic**, not of a root: it depends on the
  law and on the sample size only, so the critical value is a function of the resampling law
  alone. As everywhere in this area, its distribution function properties are hypotheses and no
  measurability in the measure argument is assumed.
* The test rejects on `{ω | g_n(1 − α, Qhat n ω) < T n ω}` — a strict inequality, matching the
  convention that large values of the statistic are evidence against the null. The rejection
  probability appearing in the conclusions is the size of the nonrandomized critical function of
  that region, in the sense of this area's test vocabulary; the statements are phrased directly
  as measures of the rejection event, so none of that vocabulary is needed here.
* Consistency against fixed alternatives is not part of the numbered result in the reference; it
  is the claim accompanying it, under the additional assumptions that the statistic diverges in
  probability under the alternative and that the estimated critical value stays bounded in
  probability. It is stated separately here to keep that distinction visible.

**Bibliographic comments.** The bootstrap is due to B. Efron ("Bootstrap methods: another look
at the jackknife," *Ann. Statist.* **7** (1979), 1–26). Its use for constructing critical values
of tests, and the requirement that resampling respect the null constraints, are developed by
R. Beran ("Bootstrap methods in statistics," *Jahresber. Deutsch. Math.-Verein.* **86** (1984),
14–30) and J. P. Romano ("A bootstrap revival of some nonparametric distance tests," *J. Amer.
Statist. Assoc.* **83** (1988), 698–708); see also D. N. Politis, J. P. Romano and M. Wolf,
*Subsampling*, Springer, 1999, and P. Hall, *The Bootstrap and Edgeworth Expansion*, Springer,
1992, for the higher-order comparisons.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace StatLean.HypothesisTesting

variable {𝓧 Ω : Type*} [MeasurableSpace 𝓧] [MeasurableSpace Ω]

/-- **Membership of a random sequence of laws in a sequence class, in probability.**

Every subsequence admits a further subsequence along which, almost surely, some member of the
class agrees with the random sequence *at those very indices*. Index preservation is essential:
the classes of this area pair the index of a law with the sample size, so a class member cannot
be produced by reindexing. Almost sure membership is the special case obtained with the identity
subsequence. -/
def MemClassInProbability (Pr : Measure Ω) (Qhat : ℕ → Ω → Measure 𝓧)
    (C : Set (ℕ → Measure 𝓧)) : Prop :=
  ∀ ϕ : ℕ → ℕ, StrictMono ϕ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
    ∀ᵐ ω ∂Pr, ∃ Qs ∈ C, ∀ m : ℕ, Qs (ϕ (ψ m)) = Qhat (ϕ (ψ m)) ω

section BootstrapTest

variable {Pr : Measure Ω} {P : Measure 𝓧} {T : ℕ → Ω → ℝ} {G : ℕ → Measure 𝓧 → ℝ → ℝ}
  {C_Q : Set (ℕ → Measure 𝓧)} {Glim : ℝ → ℝ} {Qhat : ℕ → Ω → Measure 𝓧} {α : ℝ}

/-- **Asymptotic level of the bootstrap test.**

The data are generated by a null law `P`. Along every sequence of the null class the sampling
distribution functions of the statistic converge to a common continuous limit, and the
null-restricted estimator lies in the null class in probability. Then the test rejecting when
the statistic exceeds the estimated `1 − α` quantile has rejection probability tending to the
nominal level `α`. -/
theorem tendsto_bootstrapTest_level [IsProbabilityMeasure Pr]
    -- USER-INPUT: the data-generating law belongs to the null class, as the constant sequence
    (hP_mem : (fun _ => P) ∈ C_Q)
    -- USER-INPUT: along every sequence of the null class the distribution functions of the
    -- statistic converge pointwise to the common limit
    (hGconv : ∀ Q ∈ C_Q, ∀ x : ℝ, Tendsto (fun n => G n (Q n) x) atTop (𝓝 (Glim x)))
    -- USER-INPUT: the common limit law is continuous
    (hGlim_cont : Continuous Glim)
    -- USER-INPUT: the common limit is a distribution function
    (hGlim_cdf : IsCDF Glim)
    -- USER-INPUT: every sampling distribution of the statistic is a distribution function
    (hGcdf : ∀ (n : ℕ) (Q : Measure 𝓧), IsCDF (G n Q))
    -- USER-INPUT: the null-restricted estimator lies in the null class, in probability
    (hQhat : MemClassInProbability Pr Qhat C_Q)
    -- USER-INPUT: nominal level strictly between `0` and `1`
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    -- USER-INPUT: the limit law is strictly increasing at the critical value being estimated;
    -- see the file's note on this hypothesis
    (hstrict : StrictIncAt Glim (cdfPseudoInverse Glim (1 - α)))
    -- USER-INPUT: at the data-generating law the field `G` is the exact sampling distribution
    -- function of the statistic
    (hGP : ∀ (n : ℕ) (x : ℝ), G n P x = (Pr {ω | T n ω ≤ x}).toReal)
    -- LEAN-ONLY: the statistic is measurable
    (hTmeas : ∀ n, Measurable (T n))
    -- LEAN-ONLY: the estimated critical value is measurable in the sample; no measurability in
    -- the measure argument of `G` is assumed, so this is recorded directly
    (hqmeas : ∀ n, Measurable fun ω => cdfPseudoInverse (G n (Qhat n ω)) (1 - α)) :
    Tendsto (fun n => (Pr {ω | cdfPseudoInverse (G n (Qhat n ω)) (1 - α) < T n ω}).toReal)
      atTop (𝓝 α) := by
  set q := cdfPseudoInverse Glim (1 - α) with hqdef
  have hq : Glim q = 1 - α :=
    cdf_quantile_eq hGlim_cdf hGlim_cont (by linarith [hα.2]) (by linarith [hα.1])
  set qn : ℕ → Ω → ℝ := fun n ω => cdfPseudoInverse (G n (Qhat n ω)) (1 - α) with hqn
  -- The acceptance probability tends to `1 − α`. Convergence in probability of the estimated
  -- critical value is only available along subsequences, so the limit is identified by the
  -- subsequence criterion: every subsequence has a further subsequence along which the
  -- acceptance probabilities converge to `1 − α`.
  have haccept : Tendsto (fun n => (Pr {ω | T n ω ≤ qn n ω}).toReal) atTop (𝓝 (1 - α)) := by
    refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
    obtain ⟨φ, hφ, hnsφ⟩ := Filter.strictMono_subseq_of_tendsto_atTop hns
    obtain ⟨ψ, hψ, hae⟩ := hQhat (ns ∘ φ) hnsφ
    refine ⟨φ ∘ ψ, ?_⟩
    set k : ℕ → ℕ := fun m => ns (φ (ψ m)) with hk
    have hkmono : StrictMono k := hnsφ.comp hψ
    -- Along `k` the bootstrap critical values converge almost surely to the limit quantile.
    have hquant : ∀ᵐ ω ∂Pr, Tendsto (fun m => qn (k m) ω) atTop (𝓝 q) := by
      filter_upwards [hae] with ω hω
      obtain ⟨Qs, hQs, hagree⟩ := hω
      have hagree' : ∀ m, Qs (k m) = Qhat (k m) ω := fun m => hagree m
      have hconv : ∀ x : ℝ, Tendsto (fun m => G (k m) (Qhat (k m) ω) x) atTop (𝓝 (Glim x)) := by
        intro x
        have h : Tendsto (fun m => G (k m) (Qs (k m)) x) atTop (𝓝 (Glim x)) :=
          (hGconv Qs hQs x).comp hkmono.tendsto_atTop
        refine h.congr (fun m => ?_)
        rw [hagree' m]
      exact tendsto_cdfPseudoInverse_of_tendsto (fun m => (hGcdf (k m) (Qhat (k m) ω)).mono)
        hstrict hq hconv
    have hInMeas : TendstoInMeasure Pr (fun m => qn (k m)) atTop (fun _ => q) :=
      tendstoInMeasure_of_tendsto_ae (fun m => (hqmeas (k m)).aestronglyMeasurable) hquant
    -- Along `k` the distribution functions of the statistic converge to the limit law.
    have hcdf : ∀ x : ℝ,
        Tendsto (fun m => (Pr {ω | T (k m) ω ≤ x}).toReal) atTop (𝓝 (Glim x)) := by
      intro x
      have h : Tendsto (fun m => G (k m) P x) atTop (𝓝 (Glim x)) :=
        (hGconv (fun _ => P) hP_mem x).comp hkmono.tendsto_atTop
      simpa only [hGP] using h
    have hmain := tendsto_measure_le_of_tendsto_cdf (μ := fun _ : ℕ => Pr)
      (S := fun m => T (k m)) (c := fun m => qn (k m)) hGlim_cont.continuousAt hcdf
      (fun ε hε => tendsto_measure_abs_sub_of_tendstoInMeasure hInMeas hε)
    rwa [hq] at hmain
  -- The rejection event is the complement of the acceptance event.
  have hmeasS : ∀ n, MeasurableSet {ω | T n ω ≤ qn n ω} :=
    fun n => measurableSet_le (hTmeas n) (hqmeas n)
  have hcompl : ∀ n, (Pr {ω | qn n ω < T n ω}).toReal
      = 1 - (Pr {ω | T n ω ≤ qn n ω}).toReal := by
    intro n
    have hset : {ω | qn n ω < T n ω} = {ω | T n ω ≤ qn n ω}ᶜ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [hset, measure_compl (hmeasS n) (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top _ _),
      measure_univ, ENNReal.toReal_one]
  have hlim : Tendsto (fun n => 1 - (Pr {ω | T n ω ≤ qn n ω}).toReal) atTop
      (𝓝 (1 - (1 - α))) := Tendsto.const_sub 1 haccept
  have harith : (1 : ℝ) - (1 - α) = α := by ring
  rw [harith] at hlim
  exact Tendsto.congr (fun n => (hcompl n).symm) hlim

/-- **Consistency of the bootstrap test against a fixed alternative.**

Accompanying claim, not part of the level statement above. If under the law generating the data
the statistic diverges in probability, while the estimated critical value stays bounded in
probability — which is what resampling under the null constraints buys — then the rejection
probability tends to one. -/
theorem tendsto_bootstrapTest_power_one [IsProbabilityMeasure Pr]
    -- USER-INPUT: under the alternative the test statistic diverges in probability
    (hT : ∀ M : ℝ, Tendsto (fun n => (Pr {ω | T n ω ≤ M}).toReal) atTop (𝓝 0))
    -- USER-INPUT: the estimated critical value is bounded in probability; under an alternative
    -- the null-restricted estimator approaches a null law, whose critical value is finite
    (hcrit : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ n : ℕ,
      (Pr {ω | M < cdfPseudoInverse (G n (Qhat n ω)) (1 - α)}).toReal ≤ ε)
    -- LEAN-ONLY: the statistic is measurable
    (hTmeas : ∀ n, Measurable (T n))
    -- LEAN-ONLY: the estimated critical value is measurable in the sample
    (hqmeas : ∀ n, Measurable fun ω => cdfPseudoInverse (G n (Qhat n ω)) (1 - α)) :
    Tendsto (fun n => (Pr {ω | cdfPseudoInverse (G n (Qhat n ω)) (1 - α) < T n ω}).toReal)
      atTop (𝓝 1) := by
  set qn : ℕ → Ω → ℝ := fun n ω => cdfPseudoInverse (G n (Qhat n ω)) (1 - α) with hqn
  show Tendsto (fun n => (Pr {ω | qn n ω < T n ω}).toReal) atTop (𝓝 1)
  have hmeasS : ∀ n, MeasurableSet {ω | T n ω ≤ qn n ω} :=
    fun n => measurableSet_le (hTmeas n) (hqmeas n)
  -- The acceptance probability vanishes: a divergent statistic overtakes a tight critical value.
  have hzero : Tendsto (fun n => (Pr {ω | T n ω ≤ qn n ω}).toReal) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := hcrit (ε / 2) (by positivity)
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hT M)) (ε / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hsub : {ω | T n ω ≤ qn n ω} ⊆ {ω | T n ω ≤ M} ∪ {ω | M < qn n ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
      rcases le_or_gt (qn n ω) M with h | h
      · exact Or.inl (le_trans hω h)
      · exact Or.inr h
    have hle : Pr {ω | T n ω ≤ qn n ω} ≤ Pr {ω | T n ω ≤ M} + Pr {ω | M < qn n ω} :=
      le_trans (measure_mono hsub) (measure_union_le _ _)
    have hleR : (Pr {ω | T n ω ≤ qn n ω}).toReal ≤
        (Pr {ω | T n ω ≤ M}).toReal + (Pr {ω | M < qn n ω}).toReal := by
      have := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hle
      rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    have h1 : (Pr {ω | T n ω ≤ M}).toReal < ε / 2 := by
      have hd := hN n hn
      rw [Real.dist_eq, sub_zero] at hd
      exact lt_of_le_of_lt (le_abs_self _) hd
    have h2 : (Pr {ω | M < qn n ω}).toReal ≤ ε / 2 := hM n
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
    linarith
  -- The rejection event is the complement.
  have hcompl : ∀ n, (Pr {ω | qn n ω < T n ω}).toReal
      = 1 - (Pr {ω | T n ω ≤ qn n ω}).toReal := by
    intro n
    have hset : {ω | qn n ω < T n ω} = {ω | T n ω ≤ qn n ω}ᶜ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [hset, measure_compl (hmeasS n) (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top _ _),
      measure_univ, ENNReal.toReal_one]
  have hlim : Tendsto (fun n => 1 - (Pr {ω | T n ω ≤ qn n ω}).toReal) atTop (𝓝 (1 - 0)) :=
    Tendsto.const_sub 1 hzero
  rw [sub_zero] at hlim
  exact Tendsto.congr (fun n => (hcompl n).symm) hlim

end BootstrapTest

end StatLean.HypothesisTesting
