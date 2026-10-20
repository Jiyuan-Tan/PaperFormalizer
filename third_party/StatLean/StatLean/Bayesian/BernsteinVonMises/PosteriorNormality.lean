module
public import StatLean.Bayesian.BernsteinVonMises.ExponentialTests
public import StatLean.Bayesian.BernsteinVonMises.PosteriorConcentration
public import StatLean.Bayesian.BernsteinVonMises.LocalApproximation

@[expose] public section

/-!
# The Bernstein–von Mises theorem

Assembly of the Bernstein–von Mises theorem. Let the model be an iid sample from a dominated
parametric
family that is differentiable in quadratic mean at `θ₀` with nonsingular Fisher information
`J`, let the uniform-tests condition hold, and let the prior be a probability measure that is
absolutely continuous near `θ₀` with a density continuous and positive at `θ₀`. Then the
total-variation distance between the posterior law of `h = √n(θ − θ₀)` and the random
Gaussian `N(Δ_{n,θ₀}, J⁻¹)`, `Δ_{n,θ₀} = J⁻¹ (n^{-1/2} ∑ sc(Xᵢ))`, tends to zero in
`P^n_{θ₀}`-probability.

* `scoreSum_uniformly_tight` — uniform tightness of the score sums under `P^n_{θ₀}` (from
  the score CLT), feeding the Gaussian-tail side of the triangle inequality;
* `bernstein_von_mises` — the headline, in unrolled in-probability form;
* `bernstein_von_mises_lintegral` — the expectation form
  `∫ tvDist dP^n_{θ₀} → 0` (equivalent since `tvDist ≤ 1`), the form consumed by
  the Bayes-point-estimator theorem.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10 (Bayes
Procedures), §10.2, Theorem 10.1, p. 141 (statement); proof pp. 141–143.

**Proof formalization notes.** Triangle inequality with the conditioned measures (all in
sup-form `tvDist`, half of vdV's `L¹` norm):
`tvDist(Post, N) ≤ tvDist(Post, Post^C) + tvDist(Post^C, N^C) + tvDist(N^C, N)`,
with `C = B̄(0, M)`: the first term is controlled by Step A (`posterior_mass_compl_ball_tendsto`
via `tvDist_cond_le` and `bvmLocalPosterior_compl_ball`), the third by score-sum tightness
plus the mean-uniform Gaussian tail bound
(`multivariateGaussian_compl_closedBall_uniform_small`), the second by Step B
(`local_tv_tendsto`) at fixed `M`; conclude by a `limsup`-in-`M` argument (for every `δ`,
`limsup_n P(tvDist ≥ δ) ≤ ε(M) → 0`). The tests of the exponential-tests lemma are supplied by
`exponential_tests`.

**Bibliographic comments.** The theorem's name refers to S. Bernstein, *Theory of
Probability* (Russian), 1917, and R. von Mises, *Wahrscheinlichkeitsrechnung*, Deuticke,
1931, who proved early versions for smooth one-dimensional models; P. S. Laplace's *Mémoire
sur les probabilités des causes par les événements* (1774) contains the germ of the normal
approximation to posteriors. The modern total-variation statement under
quadratic-mean differentiability is due to L. Le Cam — *On some asymptotic properties of
maximum likelihood estimates and related Bayes' estimates*, University of California
Publications in Statistics **1** (1953), 277–330, and *Asymptotic Methods in Statistical
Decision Theory*, Springer, 1986 — with the streamlined testing-condition form in L. Le Cam
and G. L. Yang, *Asymptotics in Statistics: Some Basic Concepts*, Springer, 1990.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure scoreSum)
open StatLean.Minimaxity (tvDist)

namespace StatLean.Bayesian

/-- Three thirds, in `ℝ≥0∞` (valid also at `∞`). -/
private lemma ennreal_three_thirds (x : ℝ≥0∞) : x / 3 + x / 3 + x / 3 = x := by
  have h : (3 : ℝ≥0∞) * 3⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hx : x / 3 + x / 3 + x / 3 = x * (3 * 3⁻¹) := by
    simp only [div_eq_mul_inv]; ring
  rw [hx, h, mul_one]

/-- If a probability measure charges its conditioning event with more than half its mass,
that event is not null. -/
private lemma measure_ne_zero_of_compl_lt_half {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] {C : Set α} (hC : MeasurableSet C)
    (h : ν Cᶜ < 1 / 2) : ν C ≠ 0 := by
  intro h0
  rw [prob_compl_eq_one_sub hC, h0, tsub_zero] at h
  exact absurd h (by norm_num)

/-- **Conditioning bound in usable form**: if a probability measure puts less than
`min (1/2) (ε/2)` outside `C`, then conditioning on `C` moves it by less than `ε` in total
variation. This is the quantitative form of vdV's `‖P − P^C‖ ≤ 2 P(Cᶜ)` (p. 142). -/
private lemma tvDist_cond_lt {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {C : Set α} (hC : MeasurableSet C) {ε : ℝ≥0∞}
    (h : ν Cᶜ < min (1 / 2 : ℝ≥0∞) (ε / 2)) : tvDist ν (ν[|C]) < ε := by
  have h1 : ν Cᶜ < 1 / 2 := lt_of_lt_of_le h (min_le_left _ _)
  have h2 : ν Cᶜ < ε / 2 := lt_of_lt_of_le h (min_le_right _ _)
  have hsum : ν C + ν Cᶜ = 1 := by
    rw [measure_add_measure_compl hC, measure_univ]
  have hC2 : (1 / 2 : ℝ≥0∞) < ν C := by
    by_contra hcon
    push Not at hcon
    have hlt : (1 : ℝ≥0∞) < 1 := by
      calc (1 : ℝ≥0∞) = ν C + ν Cᶜ := hsum.symm
        _ < 1 / 2 + 1 / 2 := ENNReal.add_lt_add_of_le_of_lt (by norm_num) hcon h1
        _ = 1 := ENNReal.add_halves 1
    exact absurd hlt (lt_irrefl 1)
  have hCne : ν C ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le) hC2)
  refine lt_of_le_of_lt (tvDist_cond_le ν hC) ?_
  rw [ENNReal.div_lt_iff (Or.inl hCne) (Or.inl (measure_ne_top ν C))]
  refine lt_of_lt_of_le h2 ?_
  calc ε / 2 = ε * (1 / 2) := by rw [div_eq_mul_inv, one_div]
    _ ≤ ε * ν C := by gcongr

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- **Uniform tightness of the score sums** under `P^n_{θ₀}` (a consequence of the score
CLT `scoreSum_weakly_converges`): for every `ε > 0` there is a radius `K` such that
eventually `P^n_{θ₀}(‖scoreSum‖ > K) ≤ ε`. -/
theorem scoreSum_uniformly_tight
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    {ε : ℝ≥0∞}
    -- LEAN-ONLY: nontrivial tolerance
    (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      productMeasure M μ θ₀ n {ω | K < ‖scoreSum sc n ω‖} ≤ ε := by
  classical
  haveI hProb : ∀ (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ),
      IsProbabilityMeasure (productMeasure M μ θ n) :=
    fun θ n =>
      AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
        M μ hPDF θ n
  have hscm : ∀ n : ℕ, Measurable (scoreSum sc n) := by
    intro n
    unfold scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hsc.comp (measurable_pi_apply i))).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  set ν : ℕ → Measure (EuclideanSpace ℝ (Fin k)) :=
    fun n => (productMeasure M μ θ₀ n).map (scoreSum sc n) with hνdef
  haveI hνprob : ∀ n, IsProbabilityMeasure (ν n) := fun n => by
    rw [hνdef]; exact Measure.isProbabilityMeasure_map (hscm n).aemeasurable
  haveI : IsProbabilityMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) := inferInstance
  have hweak : AsymptoticStatistics.WeakConverges ν
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) :=
    AsymptoticStatistics.AsymptoticRepresentation.scoreSum_weakly_converges M μ θ₀ sc hsc
      (hPDF.density_integral_eq_one θ₀) (hPDF.density_integrable θ₀)
      (fun _ _ => hPDF.density_integral_eq_one _) (fun _ _ => hPDF.density_integrable _)
      hDQM J hJ_pd.posSemidef hJ
  have htight := AsymptoticStatistics.Prohorov.weakConverges_range_tight ν _ hweak
  rw [AsymptoticStatistics.Prohorov.isTightMeasureSet_range_iff_singleton_tight] at htight
  obtain ⟨C, hCcpt, hC⟩ := htight ε hε
  obtain ⟨K, hKC⟩ := hCcpt.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin k))
  refine ⟨max K 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    Filter.Eventually.of_forall fun n => ?_⟩
  have hsub : {x : EuclideanSpace ℝ (Fin k) | max K 1 < ‖x‖} ⊆ Cᶜ := by
    intro x hx hxC
    exact absurd (mem_closedBall_zero_iff.1 (hKC hxC))
      (not_le.2 (lt_of_le_of_lt (le_max_left K 1) hx))
  have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin k) | max K 1 < ‖x‖} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hpre : {ω : Fin n → 𝓧 | max K 1 < ‖scoreSum sc n ω‖}
      = (scoreSum sc n) ⁻¹' {x : EuclideanSpace ℝ (Fin k) | max K 1 < ‖x‖} := rfl
  rw [hpre, ← Measure.map_apply (hscm n) hmeas]
  exact le_trans (measure_mono hsub) (hC n)

/-- **The Bernstein–von Mises theorem.** Let the experiment be an iid sample from the
dominated family `κ θ = p_θ · μ`, differentiable in quadratic mean at `θ₀` with nonsingular
Fisher information `J`; let uniformly consistent tests exist (the uniform-tests condition); and let
the
prior `π` be absolutely continuous near `θ₀` with density continuous and positive at `θ₀`.
Then for every `δ > 0`,
`P^n_{θ₀} { tvDist( posterior law of √n(θ−θ₀), N(Δ_{n,θ₀}, J⁻¹) ) ≥ δ } → 0`. -/
theorem bernstein_von_mises
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information matrix; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the uniform-tests condition; vdV §10.2
    (hTests : UniformlyConsistentTests M μ θ₀)
    -- USER-INPUT: the prior condition; vdV §10.2
    (hπ : HasLocalDensity π θ₀ r₀ f) :
    ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun n => productMeasure M μ θ₀ n
          {ω | δ ≤ bvmTV κ π θ₀ J sc n ω}) atTop (𝓝 0) := by
  classical
  haveI hProb : ∀ (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ),
      IsProbabilityMeasure (productMeasure M μ θ n) :=
    fun θ n =>
      AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
        M μ hPDF θ n
  -- Step B at every integer radius `j + 1`, with tolerance `1/(j+1)`.
  have hBstep : ∀ j : ℕ, ∃ Nj : ℕ, ∀ n, Nj ≤ n →
      productMeasure M μ θ₀ n {ω | ENNReal.ofReal (1 / ((j : ℝ) + 1)) ≤ tvDist
          ((bvmLocalPosterior κ π θ₀ n ω)[|Metric.closedBall 0 ((j : ℝ) + 1)])
          ((bvmGaussian J sc n ω)[|Metric.closedBall 0 ((j : ℝ) + 1)])}
        ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
    intro j
    have hRpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hdpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((j : ℝ) + 1)) :=
      ENNReal.ofReal_pos.2 (by positivity)
    have h := local_tv_tendsto (κ := κ) hPDF hsc hDQM hJ_pd hJ hκ hM_joint hπ hRpos _ hdpos
    rw [ENNReal.tendsto_nhds_zero] at h
    exact eventually_atTop.1 (h _ hdpos)
  choose Nb hNb using hBstep
  -- Diagonal extraction: a single radius sequence `Mseq → ∞` along which Step B still holds.
  obtain ⟨Mseq, hMseq_tendsto, hMseqB⟩ :
      ∃ Mseq : ℕ → ℝ, Tendsto Mseq atTop atTop ∧
        ∀ᶠ n in atTop, productMeasure M μ θ₀ n
            {ω | ENNReal.ofReal (1 / Mseq n) ≤ tvDist
              ((bvmLocalPosterior κ π θ₀ n ω)[|Metric.closedBall 0 (Mseq n)])
              ((bvmGaussian J sc n ω)[|Metric.closedBall 0 (Mseq n)])}
          ≤ ENNReal.ofReal (1 / Mseq n) := by
    have hMnat : Tendsto (fun n => Nat.findGreatest (fun j => Nb j ≤ n) n) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro j
      exact ⟨max j (Nb j), fun n hn => Nat.le_findGreatest
        (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn)⟩
    refine ⟨fun n => ((Nat.findGreatest (fun j => Nb j ≤ n) n : ℕ) : ℝ) + 1, ?_, ?_⟩
    · exact Filter.tendsto_atTop_add_const_right _ 1
        (tendsto_natCast_atTop_atTop.comp hMnat)
    · filter_upwards [eventually_ge_atTop (Nb 0)] with n hn
      exact hNb _ n (Nat.findGreatest_spec (P := fun j => Nb j ≤ n) (Nat.zero_le n) hn)
  -- the exponential-tests lemma supplies the exponentially powerful tests along this `Mseq`.
  obtain ⟨φ, c, hc, hφ⟩ := exponential_tests hPDF hsc hDQM hJ_pd hJ hTests hMseq_tendsto
  have hStepA := posterior_mass_compl_ball_tendsto (κ := κ) hPDF hsc hDQM hJ_pd hJ hκ hM_joint
    hπ hMseq_tendsto hc hφ
  have hzero : Tendsto (fun n => ENNReal.ofReal (1 / Mseq n)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => 1 / Mseq n) atTop (𝓝 (0 : ℝ)) := by
      simpa [one_div] using! tendsto_inv_atTop_zero.comp hMseq_tendsto
    simpa using ENNReal.tendsto_ofReal h0
  intro δ hδ
  set δ₁ : ℝ≥0∞ := min δ 1 with hδ₁def
  have hδ₁pos : 0 < δ₁ := lt_min hδ zero_lt_one
  set ε : ℝ≥0∞ := δ₁ / 3 with hεdef
  have hεpos : 0 < ε := ENNReal.div_pos hδ₁pos.ne' (by norm_num)
  set a : ℝ≥0∞ := min (1 / 2 : ℝ≥0∞) (ε / 2) with hadef
  have hapos : 0 < a := lt_min (by norm_num) (ENNReal.half_pos hεpos.ne')
  have hatop : a ≠ ∞ := ne_top_of_le_ne_top (by norm_num) (min_le_left _ _)
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη3 : (0 : ℝ≥0∞) < η / 3 := ENNReal.div_pos hη.ne' (by norm_num)
  -- The tightness radius for the score sums, and the resulting Gaussian-tail radius.
  obtain ⟨K, hKpos, hKtight⟩ := scoreSum_uniformly_tight (M := M) (μ := μ) (θ₀ := θ₀)
    (sc := sc) (J := J) hPDF hsc hDQM hJ_pd hJ hη3
  obtain ⟨M₀, hM₀⟩ := AsymptoticStatistics.multivariateGaussian_compl_closedBall_uniform_small
    (ι := Fin k) J⁻¹ (‖Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹‖ * K)
    (ε := a / 2) (ENNReal.half_pos hapos.ne')
  have hev1 : ∀ᶠ n : ℕ in atTop, productMeasure M μ θ₀ n
      {ω | a ≤ ((iidKernel κ n)†π) ω {θ | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖}} ≤ η / 3 := by
    have h := hStepA a hapos
    rw [ENNReal.tendsto_nhds_zero] at h
    exact h _ hη3
  have hev3 : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (1 / Mseq n) ≤ min ε (η / 3) :=
    ENNReal.tendsto_nhds_zero.1 hzero _ (lt_min hεpos hη3)
  filter_upwards [hev1, hev3, hMseq_tendsto.eventually_ge_atTop M₀, hMseqB, hKtight,
    eventually_ge_atTop 1] with n h1 h3 h4 hB5 h6 h5
  -- The three bad events at sample size `n`, at radius `Mseq n`.
  set C : Set (EuclideanSpace ℝ (Fin k)) := Metric.closedBall 0 (Mseq n) with hCdef
  have hCm : MeasurableSet C := Metric.isClosed_closedBall.measurableSet
  set SA : Set (Fin n → 𝓧) := {ω | a ≤ bvmLocalPosterior κ π θ₀ n ω Cᶜ} with hSAdef
  set SB : Set (Fin n → 𝓧) := {ω | ENNReal.ofReal (1 / Mseq n) ≤ tvDist
    ((bvmLocalPosterior κ π θ₀ n ω)[|C]) ((bvmGaussian J sc n ω)[|C])} with hSBdef
  set SD : Set (Fin n → 𝓧) := {ω | a ≤ bvmGaussian J sc n ω Cᶜ} with hSDdef
  have hGprob : ∀ ω : Fin n → 𝓧, IsProbabilityMeasure (bvmGaussian J sc n ω) := by
    intro ω; unfold bvmGaussian; infer_instance
  -- The triangle inequality confines the deviation event to the union of the three.
  have hincl : {ω : Fin n → 𝓧 | δ ≤ bvmTV κ π θ₀ J sc n ω} ⊆ SA ∪ SB ∪ SD := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or, hSAdef, hSBdef, hSDdef, Set.mem_setOf_eq,
      not_le] at hcon
    obtain ⟨⟨hA, hB⟩, hD⟩ := hcon
    haveI := hGprob ω
    haveI := ProbabilityTheory.cond_isProbabilityMeasure
      (measure_ne_zero_of_compl_lt_half _ hCm (lt_of_lt_of_le hA (min_le_left _ _)))
    haveI := ProbabilityTheory.cond_isProbabilityMeasure
      (measure_ne_zero_of_compl_lt_half _ hCm (lt_of_lt_of_le hD (min_le_left _ _)))
    have hT1 : tvDist (bvmLocalPosterior κ π θ₀ n ω)
        ((bvmLocalPosterior κ π θ₀ n ω)[|C]) < ε := tvDist_cond_lt _ hCm hA
    have hT3 : tvDist ((bvmGaussian J sc n ω)[|C]) (bvmGaussian J sc n ω) < ε := by
      rw [Minimaxity.tvDist_comm]
      exact tvDist_cond_lt _ hCm hD
    have hT2 : tvDist ((bvmLocalPosterior κ π θ₀ n ω)[|C]) ((bvmGaussian J sc n ω)[|C]) < ε :=
      lt_of_lt_of_le hB (le_trans h3 (min_le_left _ _))
    have htri : bvmTV κ π θ₀ J sc n ω ≤
        tvDist (bvmLocalPosterior κ π θ₀ n ω) ((bvmLocalPosterior κ π θ₀ n ω)[|C]) +
          tvDist ((bvmLocalPosterior κ π θ₀ n ω)[|C]) ((bvmGaussian J sc n ω)[|C]) +
          tvDist ((bvmGaussian J sc n ω)[|C]) (bvmGaussian J sc n ω) := by
      unfold bvmTV
      calc tvDist (bvmLocalPosterior κ π θ₀ n ω) (bvmGaussian J sc n ω)
          ≤ tvDist (bvmLocalPosterior κ π θ₀ n ω) ((bvmLocalPosterior κ π θ₀ n ω)[|C]) +
            tvDist ((bvmLocalPosterior κ π θ₀ n ω)[|C]) (bvmGaussian J sc n ω) :=
            tvDist_triangle _ _ _
        _ ≤ tvDist (bvmLocalPosterior κ π θ₀ n ω) ((bvmLocalPosterior κ π θ₀ n ω)[|C]) +
              (tvDist ((bvmLocalPosterior κ π θ₀ n ω)[|C]) ((bvmGaussian J sc n ω)[|C]) +
                tvDist ((bvmGaussian J sc n ω)[|C]) (bvmGaussian J sc n ω)) := by
            gcongr
            exact tvDist_triangle _ _ _
        _ = _ := (add_assoc _ _ _).symm
    have hlt : bvmTV κ π θ₀ J sc n ω < δ₁ := by
      refine lt_of_le_of_lt htri ?_
      calc _ < ε + ε + ε := ENNReal.add_lt_add (ENNReal.add_lt_add hT1 hT2) hT3
        _ = δ₁ := by rw [hεdef]; exact ennreal_three_thirds δ₁
    exact absurd hω (not_le.2 (lt_of_lt_of_le hlt (min_le_left _ _)))
  -- The three bad events each have probability at most `η/3`.
  have hSA : productMeasure M μ θ₀ n SA ≤ η / 3 := by
    refine le_trans (measure_mono ?_) h1
    intro ω hω
    rw [hSAdef, Set.mem_setOf_eq] at hω
    simp only [Set.mem_setOf_eq]
    refine le_trans hω ?_
    rw [← bvmLocalPosterior_compl_ball h5 ω (Mseq n)]
    exact measure_mono (Set.compl_subset_compl.2 Metric.ball_subset_closedBall)
  have hSB : productMeasure M μ θ₀ n SB ≤ η / 3 :=
    le_trans hB5 (le_trans h3 (min_le_right _ _))
  have hSD : productMeasure M μ θ₀ n SD ≤ η / 3 := by
    refine le_trans (measure_mono ?_) h6
    intro ω hω
    rw [hSDdef, Set.mem_setOf_eq] at hω
    simp only [Set.mem_setOf_eq]
    by_contra hcon
    push Not at hcon
    have hnorm : ‖bvmEffScore J sc n ω‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹‖ * K := by
      refine le_trans ((Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹).le_opNorm _) ?_
      exact mul_le_mul_of_nonneg_left hcon (norm_nonneg _)
    have hg := hM₀ (Mseq n) h4 (bvmEffScore J sc n ω) hnorm
    exact absurd hω (not_le.2 (lt_of_le_of_lt hg (ENNReal.half_lt_self hapos.ne' hatop)))
  calc productMeasure M μ θ₀ n {ω | δ ≤ bvmTV κ π θ₀ J sc n ω}
      ≤ productMeasure M μ θ₀ n (SA ∪ SB ∪ SD) := measure_mono hincl
    _ ≤ productMeasure M μ θ₀ n (SA ∪ SB) + productMeasure M μ θ₀ n SD :=
        measure_union_le _ _
    _ ≤ productMeasure M μ θ₀ n SA + productMeasure M μ θ₀ n SB
          + productMeasure M μ θ₀ n SD := by
        gcongr
        exact measure_union_le _ _
    _ ≤ η / 3 + η / 3 + η / 3 := by gcongr
    _ = η := ennreal_three_thirds η

/-- The random Gaussian approximation `N(Δ_{n,θ₀}, J⁻¹)` packaged as a Markov kernel: the
deterministic centering paired with a fixed `N(0, J⁻¹)`, pushed forward by addition. This
is the form consumed by `measurable_tvDist_kernel`. -/
private noncomputable def bvmGaussianKernel (J : Matrix (Fin k) (Fin k) ℝ)
    {sc : 𝓧 → EuclideanSpace ℝ (Fin k)} (hsc : Measurable sc) (n : ℕ) :
    Kernel (Fin n → 𝓧) (EuclideanSpace ℝ (Fin k)) :=
  Kernel.map
    (Kernel.deterministic (bvmEffScore J sc n) (measurable_bvmEffScore J hsc n) ×ₖ
      Kernel.const _ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹))
    (fun p => p.1 + p.2)

private instance (J : Matrix (Fin k) (Fin k) ℝ) {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
    (hsc : Measurable sc) (n : ℕ) : IsMarkovKernel (bvmGaussianKernel J hsc n) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

private lemma bvmGaussianKernel_apply (J : Matrix (Fin k) (Fin k) ℝ)
    {sc : 𝓧 → EuclideanSpace ℝ (Fin k)} (hsc : Measurable sc) (n : ℕ) (ω : Fin n → 𝓧) :
    bvmGaussianKernel J hsc n ω = bvmGaussian J sc n ω := by
  rw [bvmGaussianKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop), bvmGaussian,
    ← AsymptoticStatistics.multivariateGaussian_map_const_add J⁻¹ (bvmEffScore J sc n ω)]
  rfl

/-- Measurability of the Bernstein–von Mises deviation as a function of the sample. -/
private lemma measurable_bvmTV (κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧) [IsMarkovKernel κ]
    (π : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure π]
    (θ₀ : EuclideanSpace ℝ (Fin k)) (J : Matrix (Fin k) (Fin k) ℝ)
    {sc : 𝓧 → EuclideanSpace ℝ (Fin k)} (hsc : Measurable sc) (n : ℕ) :
    Measurable fun ω => bvmTV κ π θ₀ J sc n ω := by
  have h := measurable_tvDist_kernel (bvmLocalPosterior κ π θ₀ n) (bvmGaussianKernel J hsc n)
  simpa only [bvmTV, bvmGaussianKernel_apply] using h

/-- **Bernstein–von Mises, expectation form**: the mean total-variation deviation vanishes,
`∫ tvDist(posterior, Gaussian) dP^n_{θ₀} → 0`. Equivalent to `bernstein_von_mises` since
`tvDist ≤ 1`; this is the form consumed by the Bayes-point-estimator theorem. -/
theorem bernstein_von_mises_lintegral
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information matrix; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the uniform-tests condition; vdV §10.2
    (hTests : UniformlyConsistentTests M μ θ₀)
    -- USER-INPUT: the prior condition; vdV §10.2
    (hπ : HasLocalDensity π θ₀ r₀ f) :
    Tendsto (fun n => ∫⁻ ω, bvmTV κ π θ₀ J sc n ω ∂(productMeasure M μ θ₀ n))
      atTop (𝓝 0) := by
  classical
  haveI hProb : ∀ (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ),
      IsProbabilityMeasure (productMeasure M μ θ n) :=
    fun θ n =>
      AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
        M μ hPDF θ n
  have hBvM := bernstein_von_mises hPDF hsc hDQM hJ_pd hJ hκ hM_joint hTests hπ
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : (0 : ℝ≥0∞) < η / 2 := ENNReal.half_pos hη.ne'
  have h := hBvM (η / 2) hη2
  rw [ENNReal.tendsto_nhds_zero] at h
  filter_upwards [h _ hη2] with n hn
  set S : Set (Fin n → 𝓧) := {ω | η / 2 ≤ bvmTV κ π θ₀ J sc n ω} with hSdef
  have hSm : MeasurableSet S :=
    measurableSet_le measurable_const (measurable_bvmTV κ π θ₀ J hsc n)
  have hpt : ∀ ω, bvmTV κ π θ₀ J sc n ω
      ≤ η / 2 + S.indicator (1 : (Fin n → 𝓧) → ℝ≥0∞) ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      haveI : IsProbabilityMeasure (bvmGaussian J sc n ω) := by
        unfold bvmGaussian; infer_instance
      exact le_trans (Minimaxity.tvDist_le_one _ _) le_add_self
    · rw [Set.indicator_of_notMem hω, add_zero]
      rw [hSdef, Set.mem_setOf_eq, not_le] at hω
      exact hω.le
  calc ∫⁻ ω, bvmTV κ π θ₀ J sc n ω ∂(productMeasure M μ θ₀ n)
      ≤ ∫⁻ ω, (η / 2 + S.indicator (1 : (Fin n → 𝓧) → ℝ≥0∞) ω)
          ∂(productMeasure M μ θ₀ n) := lintegral_mono hpt
    _ = η / 2 + productMeasure M μ θ₀ n S := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_indicator_one hSm]
    _ ≤ η / 2 + η / 2 := by gcongr
    _ = η := ENNReal.add_halves η

end StatLean.Bayesian
