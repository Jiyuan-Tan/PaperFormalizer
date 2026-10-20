module
public import StatLean.Bayesian.BernsteinVonMises.MixtureContiguity
public import StatLean.Bayesian.Dominated.PosteriorLintegral
public import StatLean.Bayesian.Updating.IID

@[expose] public section

/-!
# Step A: posterior concentration on `√n`-balls

The first half of the proof of the Bernstein–von Mises theorem: the posterior mass outside the balls
`‖θ − θ₀‖ ≤ Mₙ/√n` tends to zero in `P^n_{θ₀}`-probability, for every `Mₙ → ∞`, given
exponentially powerful tests (the exponential-tests lemma) and the prior conditions.

* `bvmLocalPosterior_compl_ball` — pushforward bookkeeping: the local posterior's mass
  outside the radius-`Mₙ` ball is the θ-posterior's mass outside the radius-`Mₙ/√n` ball;
* `mixture_posterior_test_bound` — the disintegration/Fubini bound (vdV p. 142, first
  display of Step A): the `P_{n,U}`-mean of `Post(A)(1 − φₙ)` is at most
  `π(Bₙ)⁻¹ ∫_A P^n_θ(1 − φₙ) dπ(θ)`;
* `posterior_mass_compl_ball_tendsto` — the Step-A conclusion.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, proof of
Theorem 10.1, p. 142 ("In view of Lemma 10.3 … the first step of the proof").

**Proof formalization notes.** The a.e. posterior identities
(`posterior_iid_eq_withDensity_prod_likelihood`, `posterior_apply_eq_div`) hold
predictive-a.e.; their exceptional sets are killed under `P^n_{θ₀}` by
`measure_tendsto_zero_of_predictive_null`. The test kills the event `{φₙ ≥ 1/2}`-side under
`P^n_{θ₀}` directly (type-I error → 0 and Markov's inequality); the `(1 − φₙ)`-side is
bounded through the mixture by `mixture_posterior_test_bound`, then by the exponential-tests lemma's
exponential bound integrated against the prior (`prior_tail_split`) and the small-ball lower
bound (`prior_ball_inv_sqrt_lower`), and transferred back by the contiguity swap
(`mutuallyContiguous_mixture_base`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- **Pushforward bookkeeping**: for `n ≥ 1`, the local posterior's mass outside the ball of
radius `R` equals the θ-posterior's mass outside the ball of radius `R/√n` around `θ₀`. -/
theorem bvmLocalPosterior_compl_ball [IsFiniteMeasure π] {n : ℕ}
    -- LEAN-ONLY: `√n ≠ 0` needs `1 ≤ n`; the `n = 0` case is junk
    (hn : 1 ≤ n) (ω : Fin n → 𝓧) (R : ℝ) :
    bvmLocalPosterior κ π θ₀ n ω (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R)ᶜ
      = ((iidKernel κ n)†π) ω {θ | R / Real.sqrt n ≤ ‖θ - θ₀‖} := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  rw [bvmLocalPosterior,
    Kernel.map_apply' _ (measurable_bvmLocalScale θ₀ n) _
      Metric.isOpen_ball.measurableSet.compl]
  congr 1
  ext θ
  simp only [Set.mem_preimage, Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt,
    Set.mem_setOf_eq, bvmLocalScale, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsq.le]
  rw [div_le_iff₀ hsq, mul_comm]

/-- Fubini through the posterior disintegration `(κₙ ∘ₘ π) ⊗ₘ κₙ†π = (π ⊗ₘ κₙ).map swap`: the
predictive mean of `Post(A) · w` is the prior integral over `A` of the sampling means of `w`. -/
private lemma lintegral_posterior_mul_eq {n : ℕ}
    (π : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure π]
    (κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧) [IsMarkovKernel κ]
    {w : (Fin n → 𝓧) → ℝ≥0∞} (hw : Measurable w)
    {A : Set (EuclideanSpace ℝ (Fin k))} (hA : MeasurableSet A) :
    ∫⁻ ω, ((iidKernel κ n)†π) ω A * w ω ∂(iidKernel κ n ∘ₘ π)
      = ∫⁻ θ in A, ∫⁻ ω, w ω ∂(iidKernel κ n θ) ∂π := by
  classical
  set ind : EuclideanSpace ℝ (Fin k) → ℝ≥0∞ :=
    A.indicator (1 : EuclideanSpace ℝ (Fin k) → ℝ≥0∞) with hinddef
  have hind : Measurable ind := by rw [hinddef]; exact measurable_one.indicator hA
  set H : (Fin n → 𝓧) × EuclideanSpace ℝ (Fin k) → ℝ≥0∞ :=
    fun p => ind p.2 * w p.1 with hHdef
  have hH : Measurable H := by
    rw [hHdef]; exact (hind.comp measurable_snd).mul (hw.comp measurable_fst)
  have e1 : ∫⁻ p, H p ∂((iidKernel κ n ∘ₘ π) ⊗ₘ ((iidKernel κ n)†π))
      = ∫⁻ ω, ((iidKernel κ n)†π) ω A * w ω ∂(iidKernel κ n ∘ₘ π) := by
    rw [Measure.lintegral_compProd hH]
    refine lintegral_congr fun ω => ?_
    simp only [hHdef]
    rw [lintegral_mul_const _ hind, hinddef, lintegral_indicator_one hA]
  have e2 : ∫⁻ p, H p ∂((π ⊗ₘ iidKernel κ n).map Prod.swap)
      = ∫⁻ θ in A, ∫⁻ ω, w ω ∂(iidKernel κ n θ) ∂π := by
    rw [lintegral_map hH measurable_swap,
      Measure.lintegral_compProd
        (f := fun q : EuclideanSpace ℝ (Fin k) × (Fin n → 𝓧) => H q.swap)
        (hH.comp measurable_swap), ← lintegral_indicator hA]
    refine lintegral_congr fun θ => ?_
    simp only [hHdef, Prod.swap_prod_mk]
    rw [lintegral_const_mul _ hw]
    by_cases hθ : θ ∈ A
    · rw [Set.indicator_of_mem hθ, hinddef, Set.indicator_of_mem hθ, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem hθ, hinddef, Set.indicator_of_notMem hθ, zero_mul]
  rw [← e1, compProd_posterior_eq_map_swap, e2]

/-- **The disintegration bound of Step A** (vdV p. 142, first display): for a `[0,1]`-valued
test `φ` and a measurable parameter set `A`, the `bvmMixture`-mean of the posterior mass of
`A` damped by `(1 − φ)` is at most `π(B(θ₀, u/√n))⁻¹ · ∫_A P^n_θ(1 − φ) dπ(θ)`. -/
theorem mixture_posterior_test_bound
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    {u : ℝ}
    -- LEAN-ONLY: nontrivial localization radius
    (hu : 0 < u) (n : ℕ) {φ : (Fin n → 𝓧) → ℝ}
    -- LEAN-ONLY: measurable test (regularity)
    (hφ_meas : Measurable φ)
    -- LEAN-ONLY: `[0,1]`-valued test
    (hφ01 : ∀ ω, φ ω ∈ Set.Icc (0 : ℝ) 1)
    {A : Set (EuclideanSpace ℝ (Fin k))}
    -- LEAN-ONLY: measurable parameter set (regularity)
    (hA : MeasurableSet A) :
    ∫⁻ ω, ((iidKernel κ n)†π) ω A * ENNReal.ofReal (1 - φ ω)
        ∂(bvmMixture κ π θ₀ u n)
      ≤ (π (Metric.ball θ₀ (u / Real.sqrt n)))⁻¹ *
          ∫⁻ θ in A, ∫⁻ ω, ENNReal.ofReal (1 - φ ω) ∂(iidKernel κ n θ) ∂π := by
  have hBm : MeasurableSet (Metric.ball θ₀ (u / Real.sqrt n)) :=
    Metric.isOpen_ball.measurableSet
  have hw : Measurable fun ω : Fin n → 𝓧 => ENNReal.ofReal (1 - φ ω) := by fun_prop
  have hF : Measurable
      fun ω => ((iidKernel κ n)†π) ω A * ENNReal.ofReal (1 - φ ω) :=
    (Kernel.measurable_coe _ hA).mul hw
  have hcond_le : π[|Metric.ball θ₀ (u / Real.sqrt n)]
      ≤ (π (Metric.ball θ₀ (u / Real.sqrt n)))⁻¹ • π := by
    refine Measure.le_iff.2 fun s hsm => ?_
    rw [ProbabilityTheory.cond_apply hBm, Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' le_rfl (measure_mono Set.inter_subset_right)
  calc ∫⁻ ω, ((iidKernel κ n)†π) ω A * ENNReal.ofReal (1 - φ ω)
        ∂(bvmMixture κ π θ₀ u n)
      = ∫⁻ θ, ∫⁻ ω, ((iidKernel κ n)†π) ω A * ENNReal.ofReal (1 - φ ω)
            ∂(iidKernel κ n θ) ∂(π[|Metric.ball θ₀ (u / Real.sqrt n)]) := by
        unfold bvmMixture
        exact Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable
    _ ≤ ∫⁻ θ, ∫⁻ ω, ((iidKernel κ n)†π) ω A * ENNReal.ofReal (1 - φ ω)
            ∂(iidKernel κ n θ) ∂((π (Metric.ball θ₀ (u / Real.sqrt n)))⁻¹ • π) :=
        lintegral_mono' hcond_le le_rfl
    _ = (π (Metric.ball θ₀ (u / Real.sqrt n)))⁻¹ *
          ∫⁻ θ, ∫⁻ ω, ((iidKernel κ n)†π) ω A * ENNReal.ofReal (1 - φ ω)
            ∂(iidKernel κ n θ) ∂π := lintegral_smul_measure _ _
    _ = (π (Metric.ball θ₀ (u / Real.sqrt n)))⁻¹ *
          ∫⁻ ω, ((iidKernel κ n)†π) ω A * ENNReal.ofReal (1 - φ ω)
            ∂(iidKernel κ n ∘ₘ π) := by
        rw [Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable]
    _ = _ := by rw [lintegral_posterior_mul_eq π κ hw hA]

/-- Markov's inequality along `atTop`: vanishing integrals force vanishing deviation
probabilities at a fixed positive finite threshold. -/
private lemma tendsto_measure_ge_of_tendsto_lintegral {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} {g : ∀ n, Ω n → ℝ≥0∞}
    (hg : ∀ n, Measurable (g n)) {ε : ℝ≥0∞} (hε : ε ≠ 0) (hε' : ε ≠ ∞)
    (h : Tendsto (fun n => ∫⁻ ω, g n ω ∂(P n)) atTop (𝓝 0)) :
    Tendsto (fun n => P n {ω | ε ≤ g n ω}) atTop (𝓝 0) := by
  have hb : Tendsto (fun n => (∫⁻ ω, g n ω ∂(P n)) / ε) atTop (𝓝 0) := by
    simp only [div_eq_mul_inv]
    have h2 := ENNReal.Tendsto.mul_const h (Or.inr (ENNReal.inv_ne_top.2 hε))
    rwa [zero_mul] at h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall fun n => zero_le)
    (Eventually.of_forall fun n => meas_ge_le_lintegral_div (hg n).aemeasurable hε hε')

/-- For a `[0,1]`-valued measurable statistic on a probability space the `ℝ≥0∞`-integral of
`ofReal` is `ofReal` of the Bochner integral. -/
private lemma lintegral_ofReal_eq_ofReal_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Ω → ℝ} (hg : Measurable g)
    (h0 : ∀ ω, 0 ≤ g ω) (h1 : ∀ ω, g ω ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (g ω) ∂P = ENNReal.ofReal (∫ ω, g ω ∂P) := by
  refine (ofReal_integral_eq_lintegral_ofReal ?_ (Eventually.of_forall h0)).symm
  refine ⟨hg.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 1) ?_⟩
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 ω)]
  exact h1 ω

/-- The elementary test split `P ≤ φ + P·(1 − φ)` for `P ≤ 1` and `φ + (1 − φ) = 1`. -/
private lemma ennreal_test_split {P a b : ℝ≥0∞} (hP : P ≤ 1) (hab : a + b = 1) :
    P ≤ a + P * b := by
  calc P = P * (a + b) := by rw [hab, mul_one]
    _ = P * a + P * b := mul_add _ _ _
    _ ≤ 1 * a + P * b := by gcongr
    _ = a + P * b := by rw [one_mul]

/-- Two quantities below `d/2` add up to less than `d`. -/
private lemma ennreal_add_lt_of_lt_half {d a b : ℝ≥0∞} (ha : a < d / 2) (hb : b < d / 2) :
    a + b < d := by
  have hbne : b ≠ ∞ := (hb.trans_le le_top).ne
  calc a + b < d / 2 + b := ENNReal.add_lt_add_right hbne ha
    _ ≤ d / 2 + d / 2 := by gcongr
    _ = d := ENNReal.add_halves d

/-- **Step A: posterior concentration** (vdV p. 142). Under the model, Fisher, test and prior
conditions of the Bernstein–von Mises theorem, for every `Mₙ → ∞` and every `δ > 0`,
`P^n_{θ₀} { posterior mass of {‖θ − θ₀‖ ≥ Mₙ/√n} ≥ δ } → 0`. The tests are taken in the
Lemma-10.3 conclusion shape (`IsExpConsistentTestSeq`), discharged at assembly by
`exponential_tests`. -/
theorem posterior_mass_compl_ball_tendsto
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
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f)
    {Mseq : ℕ → ℝ}
    -- USER-INPUT: the localization radii diverge; vdV §10.2 (`Mₙ → ∞`)
    (hM : Tendsto Mseq atTop atTop)
    {φ : ∀ n : ℕ, (Fin n → 𝓧) → ℝ} {c : ℝ}
    -- LEAN-ONLY: positive exponential rate (supplied by the exponential-tests lemma)
    (hc : 0 < c)
    -- USER-INPUT: exponentially powerful tests; vdV §10.2 (discharged at assembly)
    (hφ : IsExpConsistentTestSeq M μ θ₀ Mseq c φ) :
    ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun n => productMeasure M μ θ₀ n
          {ω | δ ≤ ((iidKernel κ n)†π) ω {θ | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖}})
        atTop (𝓝 0) := by
  classical
  obtain ⟨N₀, hN₀⟩ := hφ.typeII
  obtain ⟨c₀, hc₀, hball⟩ := prior_ball_inv_sqrt_lower hπ (u := (1 : ℝ)) one_pos
  have htail := prior_tail_split hπ hc hM
  have hPeq : ∀ (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ),
      productMeasure M μ θ n = iidKernel κ n θ :=
    fun θ n => productMeasure_eq_iidKernel_apply hκ θ n
  have hTm : ∀ n : ℕ, MeasurableSet
      {θ : EuclideanSpace ℝ (Fin k) | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖} :=
    fun n => measurableSet_le measurable_const (by fun_prop)
  -- the type-I integral, transported to `ℝ≥0∞`
  have hI1 : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (φ n ω) ∂(productMeasure M μ θ₀ n)
      = ENNReal.ofReal (∫ ω, φ n ω ∂(productMeasure M μ θ₀ n)) := by
    intro n
    haveI : IsProbabilityMeasure (productMeasure M μ θ₀ n) := by
      rw [hPeq θ₀ n]; infer_instance
    exact lintegral_ofReal_eq_ofReal_integral _ (hφ.measurable n)
      (fun ω => (hφ.mem_Icc n ω).1) (fun ω => (hφ.mem_Icc n ω).2)
  -- the exponential type-II bound, transported to `ℝ≥0∞`
  have hI2 : ∀ n : ℕ, N₀ ≤ n → ∀ θ : EuclideanSpace ℝ (Fin k),
      Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖ →
      ∫⁻ ω, ENNReal.ofReal (1 - φ n ω) ∂(iidKernel κ n θ)
        ≤ ENNReal.ofReal (Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) := by
    intro n hn θ hθ
    haveI : IsProbabilityMeasure (productMeasure M μ θ n) := by
      rw [hPeq θ n]; infer_instance
    rw [← hPeq θ n, lintegral_ofReal_eq_ofReal_integral _
      ((hφ.measurable n).const_sub 1)
      (fun ω => by linarith [(hφ.mem_Icc n ω).2]) (fun ω => by linarith [(hφ.mem_Icc n ω).1])]
    exact ENNReal.ofReal_le_ofReal (hN₀ n hn θ hθ)
  intro δ hδ
  -- a positive finite threshold: `ε = (δ ∧ 1)/2`
  have hd0 : min δ 1 ≠ 0 := (lt_min hδ one_pos).ne'
  have hdtop : min δ 1 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hε0 : min δ 1 / 2 ≠ 0 := (ENNReal.half_pos hd0).ne'
  have hεtop : min δ 1 / 2 ≠ ∞ := ne_top_of_le_ne_top hdtop ENNReal.half_le_self
  -- the deviation event splits into a test part and a damped part
  have hsub : ∀ n : ℕ,
      {ω : Fin n → 𝓧 | δ ≤ ((iidKernel κ n)†π) ω
          {θ | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖}}
        ⊆ {ω : Fin n → 𝓧 | min δ 1 / 2 ≤ ENNReal.ofReal (φ n ω)} ∪
          {ω : Fin n → 𝓧 | min δ 1 / 2 ≤ ((iidKernel κ n)†π) ω
            {θ | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖} * ENNReal.ofReal (1 - φ n ω)} := by
    intro n ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    have hone : ENNReal.ofReal (φ n ω) + ENNReal.ofReal (1 - φ n ω) = 1 := by
      rw [← ENNReal.ofReal_add (hφ.mem_Icc n ω).1
        (by linarith [(hφ.mem_Icc n ω).2])]
      norm_num
    have hsplit := ennreal_test_split (P := ((iidKernel κ n)†π) ω
      {θ | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖}) prob_le_one hone
    exact absurd (le_trans (min_le_left δ 1) (le_trans hω hsplit))
      (not_le.2 (ennreal_add_lt_of_lt_half hcon.1 hcon.2))
  -- the test part vanishes by Markov and the type-I condition
  have hS1 : Tendsto (fun n => productMeasure M μ θ₀ n
      {ω | min δ 1 / 2 ≤ ENNReal.ofReal (φ n ω)}) atTop (𝓝 0) := by
    refine tendsto_measure_ge_of_tendsto_lintegral
      (P := fun n => productMeasure M μ θ₀ n)
      (g := fun n ω => ENNReal.ofReal (φ n ω))
      (fun n => ((hφ.measurable n).ennreal_ofReal)) hε0 hεtop ?_
    simp only [hI1]
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp hφ.typeI
    rw [ENNReal.ofReal_zero] at h
    exact h
  -- the damped part vanishes under the mixture, then transfers by contiguity
  have hS2 : Tendsto (fun n => productMeasure M μ θ₀ n
      {ω | min δ 1 / 2 ≤ ((iidKernel κ n)†π) ω
        {θ | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖} * ENNReal.ofReal (1 - φ n ω)})
      atTop (𝓝 0) := by
    have hgm : ∀ n : ℕ, Measurable fun ω : Fin n → 𝓧 => ((iidKernel κ n)†π) ω
        {θ | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖} * ENNReal.ofReal (1 - φ n ω) := by
      intro n
      exact (Kernel.measurable_coe _ (hTm n)).mul
        ((hφ.measurable n).const_sub 1).ennreal_ofReal
    refine (mutuallyContiguous_mixture_base hPDF hsc hDQM hJ_pd hJ hκ hπ
      (u := (1 : ℝ)) one_pos).2 _
      (fun n => measurableSet_le measurable_const (hgm n)) ?_
    refine tendsto_measure_ge_of_tendsto_lintegral
      (P := fun n => bvmMixture κ π θ₀ 1 n) hgm hε0 hεtop ?_
    -- the dominating sequence: `c₀⁻¹ · (√nᵏ · prior tail integral) → 0`
    have hbnd0 : Tendsto (fun n : ℕ => c₀⁻¹ * (ENNReal.ofReal (Real.sqrt n ^ k) *
        ∫⁻ θ in {θ : EuclideanSpace ℝ (Fin k) | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖},
          ENNReal.ofReal (Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := c₀⁻¹) htail
        (Or.inr (ENNReal.inv_ne_top.2 hc₀.ne'))
      rwa [mul_zero] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbnd0
      (Eventually.of_forall fun n => zero_le) ?_
    filter_upwards [hball, eventually_ge_atTop (max N₀ 1)] with n hbn hn
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
    have hpk : (0 : ℝ) < Real.sqrt n ^ k := pow_pos hsq k
    have hstep1 := mixture_posterior_test_bound (M := M) (μ := μ) (π := π) (θ₀ := θ₀)
      hκ hM_joint (u := (1 : ℝ)) one_pos n ((hφ.measurable n)) (hφ.mem_Icc n) (hTm n)
    have hstep2 : ∫⁻ θ in {θ : EuclideanSpace ℝ (Fin k) | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖},
          ∫⁻ ω, ENNReal.ofReal (1 - φ n ω) ∂(iidKernel κ n θ) ∂π
        ≤ ∫⁻ θ in {θ : EuclideanSpace ℝ (Fin k) | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖},
          ENNReal.ofReal (Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π :=
      setLIntegral_mono (by fun_prop) fun θ hθ => hI2 n (le_of_max_le_left hn) θ hθ
    have hstep3 : (π (Metric.ball θ₀ (1 / Real.sqrt n)))⁻¹
        ≤ c₀⁻¹ * ENNReal.ofReal (Real.sqrt n ^ k) := by
      refine (ENNReal.inv_le_inv.2 hbn).trans_eq ?_
      rw [inv_pow, ENNReal.ofReal_inv_of_pos hpk,
        ENNReal.mul_inv (Or.inl hc₀.ne')
          (Or.inr (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)), inv_inv]
    calc ∫⁻ ω, ((iidKernel κ n)†π) ω
            {θ | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖} * ENNReal.ofReal (1 - φ n ω)
          ∂(bvmMixture κ π θ₀ 1 n)
        ≤ (π (Metric.ball θ₀ (1 / Real.sqrt n)))⁻¹ *
            ∫⁻ θ in {θ : EuclideanSpace ℝ (Fin k) | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖},
              ∫⁻ ω, ENNReal.ofReal (1 - φ n ω) ∂(iidKernel κ n θ) ∂π := hstep1
      _ ≤ (c₀⁻¹ * ENNReal.ofReal (Real.sqrt n ^ k)) *
            ∫⁻ θ in {θ : EuclideanSpace ℝ (Fin k) | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖},
              ENNReal.ofReal (Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π :=
          mul_le_mul' hstep3 hstep2
      _ = c₀⁻¹ * (ENNReal.ofReal (Real.sqrt n ^ k) *
            ∫⁻ θ in {θ : EuclideanSpace ℝ (Fin k) | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖},
              ENNReal.ofReal (Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π) := mul_assoc _ _ _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using hS1.add hS2) (Eventually.of_forall fun n => zero_le)
    (Eventually.of_forall fun n => ?_)
  exact le_trans (measure_mono (hsub n)) (measure_union_le _ _)

end StatLean.Bayesian
