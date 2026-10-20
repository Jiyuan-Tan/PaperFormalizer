module
public import StatLean.Bayesian.BayesEstimators.UniformApproximation
public import StatLean.Bayesian.BayesEstimators.ArgminConsistency
public import StatLean.AsymptoticStatistics.ForMathlib.Anderson

@[expose] public section

/-!
# Asymptotics of Bayes point estimators

Assembly of the Bayes-point-estimator theorem. Under the conditions of the Bernstein–von Mises
theorem, for a
loss `ℓ` satisfying the separation and polynomial-growth conditions with a matching prior
moment, any (approximate) minimizer `Tₙ` of the posterior risk
`t ↦ ∫ ℓ(√n(t − θ)) dΠ(θ | X₁..Xₙ)` satisfies
`√n(Tₙ − θ₀) − Δ_{n,θ₀} → u₀` in `P^n_{θ₀}`-probability, where `u₀` is the unique
minimizer of the deterministic criterion `g(u) = ∫ ℓ(u − z) dN(0, J⁻¹)(z)`; consequently
`√n(Tₙ − θ₀) ⇝ N(u₀, J⁻¹)`. For bowl-shaped losses `u₀ = 0` (Anderson's lemma), recovering
vdV's "in particular, for every nonzero subconvex loss it converges to `X`".

* `bpe_tight` — Part 2 of vdV's proof: the standardized estimators are uniformly tight;
* `bayes_estimator_asymptotics` — the recentred in-probability headline;
* `bayes_estimator_weakConverges` — the weak-convergence consequence;
* `gaussCriterion_argmin_zero_of_bowlShaped` — `u₀ = 0` for bowl-shaped losses;
* `bayes_estimator_asymptotics_bowlShaped` — the subconvex/bowl-shaped conclusion.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10 (Bayes
Procedures), §10.3 (Point Estimators), Theorem 10.8, p. 147 (statement), proof pp. 147–149.

**Proof formalization notes.** Deviations from the book's proof, recorded once here:
(i) the argmax-CMT/`ℓ^∞(K)` route (Cor. 5.58) is replaced by the recentred majorant
approximation (`posteriorRisk_shifted_majorant`) plus deterministic argmin consistency
(`argmin_tendsto_of_uniform_approx`) applied pointwise on good events — after recentring by
`Δₙ`, the limit criterion is deterministic, so no weak convergence of processes is needed;
(ii) `Tₙ` is only required to be an `εₙ`-approximate minimizer (with `εₙ → 0`), a
generalization; the book's exact-minimizer hypothesis is the case `εₙ = 0`; measurable
selection of `Tₙ` is a hypothesis, as in the book ("this is an implicit assumption");
(iii) the uniqueness proviso "any two minimizers of the limit process coincide a.s." is
taken in the equivalent recentred form: `g` has the strict unique minimizer `u₀`;
(iv) the conclusion is strengthened to convergence in probability of
`√n(Tₙ − θ₀) − Δ_{n,θ₀}` (the book's weak convergence of `√n(Tₙ − θ₀)` to the law of
`X + u₀` follows by the score CLT and Slutsky).

**Bibliographic comments.** Asymptotics of Bayes point estimators for general loss functions
go back to I. A. Ibragimov and R. Z. Has'minskii, *Statistical Estimation: Asymptotic
Theory*, Springer, 1981, Chapters I–III, who treat locally asymptotically normal (and
non-normal) models by direct analysis of the normalized posterior risk; the streamlined
route through the total-variation Bernstein–von Mises theorem is L. Le Cam's (see
*Asymptotic Methods in Statistical Decision Theory*, Springer, 1986, Chapter 12). The
`u₀ = 0` step for symmetric unimodal criteria is T. W. Anderson's integral inequality,
*Proceedings of the American Mathematical Society* **6** (1955), 170–176.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation BowlShaped WeakConverges)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure scoreSum
  productMeasure_isProbabilityMeasure scoreSum_weakly_converges)
open StatLean.Minimaxity (tvDist tvDist_comm)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
variable {ℓ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞} {p : ℝ}
variable {T : ∀ n : ℕ, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)} {εseq : ℕ → ℝ≥0∞}

/-! ### Elementary bookkeeping for Part 2 -/

/-- `1 + (x+y)ᵍ ≤ 2ᵍ (1+xᵍ)(1+yᵍ)` for nonnegative `x`, `y`, `q`: the multiplicative splitting
of the polynomial envelope, used to detach a bounded shift from the integration variable. -/
private lemma tight_one_add_rpow_add_le {x y q : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hq : 0 ≤ q) :
    1 + (x + y) ^ q ≤ 2 ^ q * (1 + x ^ q) * (1 + y ^ q) := by
  have h2 : (1 : ℝ) ≤ 2 ^ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hq
  have h2p : (0 : ℝ) ≤ 2 ^ q := Real.rpow_nonneg (by norm_num) q
  have hxp : (0 : ℝ) ≤ x ^ q := Real.rpow_nonneg hx q
  have hyp : (0 : ℝ) ≤ y ^ q := Real.rpow_nonneg hy q
  have hmax : (x + y) ^ q ≤ 2 ^ q * (x ^ q + y ^ q) := by
    have hle : x + y ≤ 2 * max x y := by
      rcases le_total x y with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have h0 : (0 : ℝ) ≤ max x y := le_trans hx (le_max_left x y)
    have hmm : (max x y) ^ q ≤ x ^ q + y ^ q := by
      rcases le_total x y with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    calc (x + y) ^ q ≤ (2 * max x y) ^ q := Real.rpow_le_rpow (by linarith) hle hq
      _ = 2 ^ q * (max x y) ^ q := Real.mul_rpow (by norm_num) h0
      _ ≤ 2 ^ q * (x ^ q + y ^ q) := mul_le_mul_of_nonneg_left hmm h2p
  nlinarith [mul_nonneg (mul_nonneg h2p hxp) hyp]

/-- **One radius kills the Gaussian tail, uniformly over a fixed ball of centers.** For every
tolerance `δ > 0` there is a radius `r` (as large as one likes) such that every loss dominated
by the polynomial envelope and vanishing on `B̄(0,r)` has Gaussian criterion at most `δ` at all
`‖u‖ ≤ R`. Deterministic; dominated convergence against the Gaussian polynomial moment. -/
private lemma exists_radius_gaussCriterion_tail_le (J : Matrix (Fin k) (Fin k) ℝ) {q R r₁ : ℝ}
    (hq : 0 ≤ q) (hR : 0 ≤ R) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ r : ℝ, r₁ ≤ r ∧ 0 < r ∧ ∀ w : EuclideanSpace ℝ (Fin k) → ℝ≥0∞,
      (∀ x, ‖x‖ ≤ r → w x = 0) → (∀ x, w x ≤ ENNReal.ofReal (1 + ‖x‖ ^ q)) →
      ∀ u : EuclideanSpace ℝ (Fin k), ‖u‖ ≤ R → bpeGaussCriterion J w u ≤ δ := by
  classical
  have hrpow : Continuous fun s : ℝ => s ^ q :=
    continuous_iff_continuousAt.2 fun s => Real.continuousAt_rpow_const s q (Or.inr hq)
  have hWmeas : Measurable fun z : EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (1 + ‖z‖ ^ q) :=
    (continuous_const.add (hrpow.comp continuous_norm)).measurable.ennreal_ofReal
  obtain ⟨G, hGdef⟩ : ∃ G : EuclideanSpace ℝ (Fin k) → ℝ≥0∞,
      ∀ z, G z = ENNReal.ofReal (1 + (R + ‖z‖) ^ q) := ⟨_, fun _ => rfl⟩
  have hGmeas : Measurable G := by
    rw [funext hGdef]
    exact (continuous_const.add
      (hrpow.comp (continuous_const.add continuous_norm))).measurable.ennreal_ofReal
  have hGfin : ∫⁻ z, G z ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) ≠ ∞ := by
    have hbase : ∫⁻ z, ENNReal.ofReal (1 + ‖z‖ ^ q)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) < ∞ := by
      have h := AsymptoticStatistics.gaussian_loss_convolution_lt_top J⁻¹
        (ℓ := fun x : EuclideanSpace ℝ (Fin k) => ENNReal.ofReal (1 + ‖x‖ ^ q))
        (fun _ => le_rfl) hq 0
      simpa using h
    have hptw : ∀ z, G z
        ≤ ENNReal.ofReal (2 ^ q * (1 + R ^ q)) * ENNReal.ofReal (1 + ‖z‖ ^ q) := by
      intro z
      have h2q : (0 : ℝ) ≤ 2 ^ q := Real.rpow_nonneg (by norm_num) q
      have hRq : (0 : ℝ) ≤ R ^ q := Real.rpow_nonneg hR q
      rw [hGdef z, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h := tight_one_add_rpow_add_le hR (norm_nonneg z) hq
      linarith
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hptw)
    rw [lintegral_const_mul _ hWmeas]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbase.ne
  -- the deterministic tails vanish along integer radii
  have hEtend : Tendsto (fun j : ℕ => ∫⁻ z, ({z : EuclideanSpace ℝ (Fin k) | (j : ℝ) < ‖z‖}
      ).indicator G z ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹))
      atTop (𝓝 0) := by
    have hmeas : ∀ j : ℕ, Measurable
        (({z : EuclideanSpace ℝ (Fin k) | (j : ℝ) < ‖z‖}).indicator G) := fun _ =>
      hGmeas.indicator (measurableSet_lt measurable_const (by fun_prop))
    have hbound : ∀ j : ℕ, ({z : EuclideanSpace ℝ (Fin k) | (j : ℝ) < ‖z‖}).indicator G
        ≤ᵐ[multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹] G := fun _ =>
      Eventually.of_forall fun z => Set.indicator_le_self' (fun _ _ => zero_le) z
    have hlim : ∀ᵐ z ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹),
        Tendsto (fun j : ℕ => ({z : EuclideanSpace ℝ (Fin k) | (j : ℝ) < ‖z‖}).indicator G z)
          atTop (𝓝 0) := by
      refine Eventually.of_forall fun z => ?_
      have hev : ∀ᶠ j : ℕ in atTop,
          ({z : EuclideanSpace ℝ (Fin k) | (j : ℝ) < ‖z‖}).indicator G z = 0 := by
        filter_upwards [eventually_ge_atTop ⌈‖z‖⌉₊] with j hj
        refine Set.indicator_of_notMem ?_ _
        simp only [Set.mem_setOf_eq, not_lt]
        exact le_trans (Nat.le_ceil _) (Nat.cast_le.2 hj)
      exact Tendsto.congr' (hev.mono fun j hj => hj.symm) tendsto_const_nhds
    have h := tendsto_lintegral_of_dominated_convergence G hmeas hbound hGfin hlim
    simpa using h
  obtain ⟨j, hj⟩ := (ENNReal.tendsto_nhds_zero.mp hEtend δ hδ).exists
  refine ⟨max r₁ (max 1 (R + j + 1)), le_max_left _ _,
    lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) (le_max_right _ _)), ?_⟩
  intro w hw0 hwle u hu
  rw [bpeGaussCriterion]
  refine le_trans (lintegral_mono fun z => ?_) hj
  by_cases hz : ‖u - z‖ ≤ max r₁ (max 1 (R + j + 1))
  · rw [hw0 _ hz]; exact zero_le
  · rw [not_le] at hz
    have h1 : ‖u - z‖ ≤ R + ‖z‖ := le_trans (norm_sub_le u z) (by linarith)
    have hj1 : R + (j : ℝ) + 1 ≤ max r₁ (max 1 (R + j + 1)) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have h2 : (j : ℝ) < ‖z‖ := by linarith
    rw [Set.indicator_of_mem
      (show z ∈ {z : EuclideanSpace ℝ (Fin k) | (j : ℝ) < ‖z‖} from h2), hGdef]
    refine le_trans (hwle _) (ENNReal.ofReal_le_ofReal ?_)
    have h3 := Real.rpow_le_rpow (norm_nonneg (u - z)) h1 hq
    linarith

/-- **Uniform tightness of the standardized Bayes point estimators** of the standardized Bayes
point estimators `√n(Tₙ − θ₀)` (vdV p. 148: the separation condition forces the minimizer
into balls of fixed radius with probability tending to one). -/
theorem bpe_tight
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
    -- USER-INPUT: the uniform-tests condition; vdV §10.2
    (hTests : UniformlyConsistentTests M μ θ₀)
    -- USER-INPUT: the prior condition; vdV §10.2
    (hπ : HasLocalDensity π θ₀ r₀ f)
    -- LEAN-ONLY: measurable loss (regularity)
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the loss separation condition; vdV §10.3, p. 147
    (hsep : SeparatedLoss ℓ)
    -- LEAN-ONLY: nonnegative growth exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p)
    -- USER-INPUT: polynomial growth of the loss; vdV §10.3, p. 147
    (hpoly : PolyGrowthLoss p ℓ)
    -- USER-INPUT: finite prior `p`-moment; vdV §10.3
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞)
    -- LEAN-ONLY: measurable estimators (vdV p. 147: "an implicit assumption")
    (hT_meas : ∀ n, Measurable (T n))
    -- LEAN-ONLY: vanishing minimization tolerance (`εₙ = 0` is the book's exact case)
    (hεseq : Tendsto εseq atTop (𝓝 0))
    -- USER-INPUT: `Tₙ` approximately minimizes the posterior risk; vdV §10.3, p. 147
    (hT : ∀ n (ω : Fin n → 𝓧) (t : EuclideanSpace ℝ (Fin k)),
      bpePosteriorRisk κ π θ₀ ℓ n (Real.sqrt n • (T n ω - θ₀)) ω
        ≤ bpePosteriorRisk κ π θ₀ ℓ n t ω + εseq n) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      productMeasure M μ θ₀ n
          {ω | K ≤ ‖Real.sqrt n • (T n ω - θ₀)‖} ≤ ε := by
  -- vdV p. 148, Part 2, with the gap read off the repaired `SeparatedLoss.strict`.
  -- Writing `a` for its scale and `y₀` for any point with `‖y₀‖ = 2a`, the additive gap is
  -- `η := min (ℓ y₀ − c) 1 > 0`, and `‖x‖ ≤ a`, `4a ≤ ‖y‖` force `ℓ x + η ≤ ℓ y`.
  -- Two facts drive the argument: (i) `ℓ(−h) ≤ ℓ(τ − h)` whenever `3‖h‖ ≤ ‖τ‖` (`mono` at the
  -- scale `‖τ‖/3`), so truncating the posterior at a *fixed* radius `ρ` and comparing `Zₙ(τ)`
  -- with `Zₙ(0)` costs only the tail `∫_{‖h‖ > ρ} (1 + ‖h‖ᵖ) d(local posterior)`; (ii) that
  -- tail is itself a posterior risk for the truncated envelope loss, so the majorant of Part 3
  -- plus the *deterministic* Gaussian tail bound (`exists_radius_gaussCriterion_tail_le`) make
  -- it `≤ 2γ` in probability. Against the gain `η · Post(B̄(0,a)) ≥ η p₀ = δ₀ > 3γ` obtained
  -- from the Bernstein–von Mises theorem and the Gaussian density lower bound, `hT` at `t = 0` then
  -- rules out
  -- `‖√n(Tₙ − θ₀)‖ ≥ K := max (5a) (3ρ)`.
  classical
  haveI hprob : ∀ n : ℕ, IsProbabilityMeasure (productMeasure M μ θ₀ n) := fun n =>
    productMeasure_isProbabilityMeasure M μ hPDF θ₀ n
  intro ε hε
  rcases isEmpty_or_nonempty (Fin k) with hk | hk
  · -- degenerate parameter space: the standardized estimator is identically `0`
    haveI := hk
    refine ⟨1, one_pos, Filter.Eventually.of_forall fun n => ?_⟩
    have hempty : {ω : Fin n → 𝓧 | (1 : ℝ) ≤ ‖Real.sqrt n • (T n ω - θ₀)‖} = ∅ := by
      ext ω
      simp [EuclideanSpace.norm_eq]
    rw [hempty, measure_empty]
    exact zero_le
  obtain ⟨i⟩ := hk
  -- (1) the separation gap `η` at the scale `a`, in the additive form of vdV p. 148
  obtain ⟨a, ha, c, hcle, hclt⟩ := hsep.strict
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : EuclideanSpace ℝ (Fin k), ‖y₀‖ = 2 * a := by
    refine ⟨EuclideanSpace.single i (2 * a), ?_⟩
    simp [ha.le]
  have hcc : c < ℓ y₀ := hclt y₀ hy₀.ge
  set η : ℝ≥0∞ := min (ℓ y₀ - c) 1 with hηdef
  have hηpos : 0 < η := lt_min (tsub_pos_of_lt hcc) one_pos
  have hηtop : η ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hcη : c + η ≤ ℓ y₀ := by
    calc c + η ≤ c + (ℓ y₀ - c) := by gcongr; exact min_le_left _ _
      _ = ℓ y₀ - c + c := add_comm _ _
      _ = ℓ y₀ := tsub_add_cancel_of_le hcc.le
  have hgapl : ∀ x y : EuclideanSpace ℝ (Fin k), ‖x‖ ≤ a → 4 * a ≤ ‖y‖ → ℓ x + η ≤ ℓ y := by
    intro x y hx hy
    calc ℓ x + η ≤ c + η := by gcongr; exact hcle x hx
      _ ≤ ℓ y₀ := hcη
      _ ≤ ℓ y := hsep.mono (2 * a) (by linarith) y₀ y hy₀.le (by linarith)
  have hmono3 : ∀ h τ : EuclideanSpace ℝ (Fin k), 0 < ‖τ‖ → 3 * ‖h‖ ≤ ‖τ‖ →
      ℓ (-h) ≤ ℓ (τ - h) := by
    intro h τ hτ hh
    refine hsep.mono (‖τ‖ / 3) (by linarith) (-h) (τ - h) (by rw [norm_neg]; linarith) ?_
    have h1 : ‖τ‖ - ‖h‖ ≤ ‖τ - h‖ := norm_sub_norm_le τ h
    linarith
  -- (2) the probability budget
  set t : ℝ≥0∞ := ε / 2 / 2 with htdef
  have ht0 : 0 < t := ENNReal.half_pos (ENNReal.half_pos hε.ne').ne'
  have htt : t + t = ε / 2 := by rw [htdef]; exact ENNReal.add_halves _
  have ht3 : t + (t + t) ≤ ε := by
    calc t + (t + t) ≤ (t + t) + (t + t) := add_le_add le_add_self le_rfl
      _ = ε / 2 + ε / 2 := by rw [htt]
      _ = ε := ENNReal.add_halves ε
  -- (3) tightness of the centering sequence
  obtain ⟨K₂, hK₂pos, hK₂⟩ := scoreSum_uniformly_tight hPDF hsc hDQM hJ_pd hJ ht0
  set A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ with hAdef
  have hAeq : ∀ (n : ℕ) (ω : Fin n → 𝓧), bvmEffScore J sc n ω = A (scoreSum sc n ω) :=
    fun _ _ => by rw [hAdef]; rfl
  set C : ℝ := ‖A‖ * K₂ with hCdef
  have hCnn : 0 ≤ C := mul_nonneg (norm_nonneg _) hK₂pos.le
  -- (4) the Gaussian lower bound on the small ball, uniformly over the tight centerings
  set Bs : Set (EuclideanSpace ℝ (Fin k)) := Metric.closedBall 0 a with hBsdef
  have hBmeas : MeasurableSet Bs := measurableSet_closedBall
  obtain ⟨c₀, hc₀pos, hc₀⟩ :=
    AsymptoticStatistics.exists_pos_smul_volume_le_multivariateGaussian hJ_pd.inv C a
  set q₀ : ℝ≥0∞ := c₀ * volume Bs with hq₀def
  have hq₀pos : 0 < q₀ :=
    ENNReal.mul_pos hc₀pos.ne' (Metric.measure_closedBall_pos volume 0 ha).ne'
  have hq₀le : q₀ ≤ 1 := by
    refine le_trans (hc₀ 0 (by simpa using hCnn) Bs Set.Subset.rfl hBmeas) ?_
    exact prob_le_one
  have hq₀top : q₀ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hq₀le
  set p₀ : ℝ≥0∞ := q₀ / 2 with hp₀def
  have hp₀pos : 0 < p₀ := ENNReal.half_pos hq₀pos.ne'
  have hp₀top : p₀ ≠ ∞ := by
    rw [hp₀def]; exact ne_top_of_le_ne_top hq₀top ENNReal.half_le_self
  -- (5) the gain budget `δ₀ = η · p₀` and its quarters
  set δ₀ : ℝ≥0∞ := η * p₀ with hδ₀def
  have hδ₀pos : 0 < δ₀ := ENNReal.mul_pos hηpos.ne' hp₀pos.ne'
  have hδ₀top : δ₀ ≠ ∞ := ENNReal.mul_ne_top hηtop hp₀top
  set γ : ℝ≥0∞ := δ₀ / 2 / 2 with hγdef
  have hγpos : 0 < γ := ENNReal.half_pos (ENNReal.half_pos hδ₀pos.ne').ne'
  have hγsum : γ + (γ + γ) < δ₀ := by
    have hh0 : δ₀ / 2 ≠ 0 := (ENNReal.half_pos hδ₀pos.ne').ne'
    have hhtop : δ₀ / 2 ≠ ∞ := ne_top_of_le_ne_top hδ₀top ENNReal.half_le_self
    have hγγ : γ + γ = δ₀ / 2 := by rw [hγdef]; exact ENNReal.add_halves _
    have hγlt : γ < δ₀ / 2 := by rw [hγdef]; exact ENNReal.half_lt_self hh0 hhtop
    calc γ + (γ + γ) = γ + δ₀ / 2 := by rw [hγγ]
      _ < δ₀ / 2 + δ₀ / 2 := by exact ENNReal.add_lt_add_right hhtop hγlt
      _ = δ₀ := ENNReal.add_halves δ₀
  -- (6) a truncation radius killing the Gaussian tail, and the truncated envelope loss
  obtain ⟨ρ, hρa, hρpos, hρtail⟩ :=
    exists_radius_gaussCriterion_tail_le J (q := p) (R := C + 1) (r₁ := a)
      hp (by linarith) hγpos
  obtain ⟨ℓ', hℓ'⟩ : ∃ w : EuclideanSpace ℝ (Fin k) → ℝ≥0∞,
      ∀ x, w x = if ρ < ‖x‖ then ENNReal.ofReal (1 + ‖x‖ ^ p) else 0 := ⟨_, fun _ => rfl⟩
  have hrpow : Continuous fun s : ℝ => s ^ p :=
    continuous_iff_continuousAt.2 fun s => Real.continuousAt_rpow_const s p (Or.inr hp)
  have hWmeas : Measurable fun z : EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (1 + ‖z‖ ^ p) :=
    (continuous_const.add (hrpow.comp continuous_norm)).measurable.ennreal_ofReal
  have hℓ'meas : Measurable ℓ' := by
    rw [funext hℓ']
    exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) hWmeas
      measurable_const
  have hℓ'poly : PolyGrowthLoss p ℓ' := by
    intro h
    rw [hℓ' h]
    split_ifs
    · exact le_rfl
    · exact zero_le
  have hℓ'0 : ∀ x : EuclideanSpace ℝ (Fin k), ‖x‖ ≤ ρ → ℓ' x = 0 := by
    intro x hx; rw [hℓ' x, if_neg (not_lt.2 hx)]
  -- (7) the uniform majorant for the truncated loss
  obtain ⟨Mn, -, hMntend, hMnapprox⟩ :=
    posteriorRisk_shifted_majorant hPDF hsc hDQM hJ_pd hJ hκ hM_joint hTests hπ hℓ'meas hp
      hℓ'poly hmom (R := C + 1) (by linarith)
  -- (8) the tightness radius
  set K : ℝ := max (5 * a) (3 * ρ) with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨K, hKpos, ?_⟩
  have hbvm := bernstein_von_mises hPDF hsc hDQM hJ_pd hJ hκ hM_joint hTests hπ p₀ hp₀pos
  filter_upwards [hK₂, ENNReal.tendsto_nhds_zero.mp hbvm t ht0,
    ENNReal.tendsto_nhds_zero.mp (hMntend γ hγpos) t ht0,
    ENNReal.tendsto_nhds_zero.mp hεseq γ hγpos] with n h1 h2 h3 h4
  have hsub : {ω : Fin n → 𝓧 | K ≤ ‖Real.sqrt n • (T n ω - θ₀)‖} ⊆
      {ω | K₂ < ‖scoreSum sc n ω‖} ∪
        ({ω | p₀ ≤ bvmTV κ π θ₀ J sc n ω} ∪ {ω | γ ≤ Mn n ω}) := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le, not_lt] at hnot
    obtain ⟨hb1, hb2, hb3⟩ := hnot
    simp only [Set.mem_setOf_eq] at hω
    set τ : EuclideanSpace ℝ (Fin k) := Real.sqrt n • (T n ω - θ₀) with hτdef
    set Δ : EuclideanSpace ℝ (Fin k) := bvmEffScore J sc n ω with hΔdef
    set Post : Measure (EuclideanSpace ℝ (Fin k)) := bvmLocalPosterior κ π θ₀ n ω with hPostdef
    haveI hPostP : IsProbabilityMeasure Post := by rw [hPostdef]; infer_instance
    have hΔC : ‖Δ‖ ≤ C := by
      rw [hΔdef, hAeq n ω, hCdef]
      exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb1 (norm_nonneg A))
    have hτpos : 0 < ‖τ‖ := lt_of_lt_of_le hKpos hω
    -- the posterior mass of the small ball is bounded below
    have hPostB : p₀ ≤ Post Bs := by
      haveI hGP : IsProbabilityMeasure (bvmGaussian J sc n ω) := by
        change IsProbabilityMeasure (multivariateGaussian _ _); infer_instance
      have hGB : q₀ ≤ bvmGaussian J sc n ω Bs := hc₀ Δ hΔC Bs Set.Subset.rfl hBmeas
      have htvc : tvDist (bvmGaussian J sc n ω) Post = bvmTV κ π θ₀ J sc n ω :=
        (tvDist_comm _ _).symm
      have hsupr : bvmGaussian J sc n ω Bs - Post Bs ≤ bvmTV κ π θ₀ J sc n ω := by
        rw [← htvc]
        exact le_iSup₂ (f := fun s (_ : MeasurableSet s) =>
          bvmGaussian J sc n ω s - Post s) Bs hBmeas
      have hstep : bvmGaussian J sc n ω Bs ≤ Post Bs + bvmTV κ π θ₀ J sc n ω :=
        le_trans (tsub_le_iff_right.1 hsupr) (le_of_eq (add_comm _ _))
      have h5 : q₀ ≤ Post Bs + p₀ :=
        le_trans hGB (le_trans hstep (add_le_add le_rfl hb2.le))
      have hq : p₀ + p₀ = q₀ := by rw [hp₀def]; exact ENNReal.add_halves q₀
      rw [← hq] at h5
      exact (ENNReal.add_le_add_iff_right hp₀top).1 h5
    -- the truncation set
    set S : Set (EuclideanSpace ℝ (Fin k)) := {h | ‖h‖ ≤ ρ} with hSdef
    have hSmeas : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
    have hBS : Bs ⊆ S := fun x hx => le_trans (mem_closedBall_zero_iff.1 hx) hρa
    have hℓneg : Measurable fun h : EuclideanSpace ℝ (Fin k) => ℓ (-h) := hℓ.comp (by fun_prop)
    set Aq : ℝ≥0∞ := ∫⁻ h in S, ℓ (-h) ∂Post with hAqdef
    -- the truncated part is finite
    have hAqle : Aq ≤ ENNReal.ofReal (1 + ρ ^ p) := by
      calc Aq ≤ ∫⁻ _ in S, ENNReal.ofReal (1 + ρ ^ p) ∂Post := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem hSmeas] with h hh
            refine (hpoly (-h)).trans ?_
            rw [norm_neg]
            exact ENNReal.ofReal_le_ofReal
              (by linarith [Real.rpow_le_rpow (norm_nonneg h) hh hp])
        _ = ENNReal.ofReal (1 + ρ ^ p) * Post S := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal (1 + ρ ^ p) * 1 := by gcongr; exact prob_le_one
        _ = ENNReal.ofReal (1 + ρ ^ p) := mul_one _
    have hAqtop : Aq ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hAqle
    -- the lower bound on the risk at a far-away point
    have hind : ∫⁻ h in S, Bs.indicator (fun _ => η) h ∂Post = η * Post Bs := by
      rw [lintegral_indicator hBmeas, setLIntegral_const, Measure.restrict_apply hBmeas,
        Set.inter_eq_self_of_subset_left hBS]
    have hZτ : Aq + δ₀ ≤ bpePosteriorRisk κ π θ₀ ℓ n τ ω := by
      have hδ₀le : δ₀ ≤ η * Post Bs := by rw [hδ₀def]; gcongr
      have hptw : ∀ h ∈ S, ℓ (-h) + Bs.indicator (fun _ => η) h ≤ ℓ (τ - h) := by
        intro h hh
        have hhρ : ‖h‖ ≤ ρ := hh
        have h3 : 3 * ‖h‖ ≤ ‖τ‖ := by
          have h3ρ : 3 * ρ ≤ K := le_max_right _ _
          linarith
        by_cases hB : h ∈ Bs
        · have hha : ‖h‖ ≤ a := mem_closedBall_zero_iff.1 hB
          have h5a : 5 * a ≤ K := le_max_left _ _
          have h4a : 4 * a ≤ ‖τ - h‖ := by
            have hns := norm_sub_norm_le τ h
            linarith
          rw [Set.indicator_of_mem hB]
          exact hgapl (-h) (τ - h) (by rw [norm_neg]; exact hha) h4a
        · rw [Set.indicator_of_notMem hB, add_zero]
          exact hmono3 h τ hτpos h3
      calc Aq + δ₀ ≤ Aq + η * Post Bs := add_le_add le_rfl hδ₀le
        _ = ∫⁻ h in S, (ℓ (-h) + Bs.indicator (fun _ => η) h) ∂Post := by
              rw [lintegral_add_left hℓneg, hind, ← hAqdef]
        _ ≤ ∫⁻ h in S, ℓ (τ - h) ∂Post := by
              refine lintegral_mono_ae ?_
              filter_upwards [ae_restrict_mem hSmeas] with h hh
              exact hptw h hh
        _ ≤ ∫⁻ h, ℓ (τ - h) ∂Post := lintegral_mono' Measure.restrict_le_self le_rfl
    -- the upper bound on the risk at the origin
    have hZ0 : bpePosteriorRisk κ π θ₀ ℓ n 0 ω ≤ Aq + (γ + γ) := by
      have hsplit0 : bpePosteriorRisk κ π θ₀ ℓ n 0 ω = Aq + ∫⁻ h in Sᶜ, ℓ (-h) ∂Post := by
        rw [hAqdef, bpePosteriorRisk]
        simp_rw [zero_sub]
        exact (lintegral_add_compl _ hSmeas).symm
      have heq : bpePosteriorRisk κ π θ₀ ℓ' n 0 ω
          = ∫⁻ h in Sᶜ, ENNReal.ofReal (1 + ‖h‖ ^ p) ∂Post := by
        rw [bpePosteriorRisk, ← lintegral_indicator hSmeas.compl]
        refine lintegral_congr fun h => ?_
        rw [zero_sub, hℓ' (-h), norm_neg, Set.indicator_apply]
        congr 1
        simp [hSdef, not_le]
      have hmaj : bpePosteriorRisk κ π θ₀ ℓ' n 0 ω ≤ γ + γ := by
        have h5 := (hMnapprox n ω (-Δ) (by rw [norm_neg]; linarith)).1
        rw [neg_add_cancel] at h5
        exact le_trans h5 (add_le_add (hρtail ℓ' hℓ'0 (fun x => hℓ'poly x) (-Δ)
          (by rw [norm_neg]; linarith)) hb3.le)
      rw [heq] at hmaj
      have htail : ∫⁻ h in Sᶜ, ℓ (-h) ∂Post ≤ γ + γ := by
        refine le_trans (lintegral_mono_ae ?_) hmaj
        filter_upwards with h
        have hh := hpoly (-h)
        rwa [norm_neg] at hh
      rw [hsplit0]
      exact add_le_add le_rfl htail
    -- the two bounds are incompatible
    have hfinal : Aq + δ₀ ≤ Aq + (γ + (γ + γ)) := by
      calc Aq + δ₀ ≤ bpePosteriorRisk κ π θ₀ ℓ n τ ω := hZτ
        _ ≤ bpePosteriorRisk κ π θ₀ ℓ n 0 ω + εseq n := hT n ω 0
        _ ≤ (Aq + (γ + γ)) + γ := add_le_add hZ0 h4
        _ = Aq + (γ + (γ + γ)) := by ring
    exact absurd ((ENNReal.add_le_add_iff_left hAqtop).1 hfinal) (not_le.2 hγsum)
  calc productMeasure M μ θ₀ n {ω | K ≤ ‖Real.sqrt n • (T n ω - θ₀)‖}
      ≤ productMeasure M μ θ₀ n ({ω | K₂ < ‖scoreSum sc n ω‖} ∪
        ({ω | p₀ ≤ bvmTV κ π θ₀ J sc n ω} ∪ {ω | γ ≤ Mn n ω})) := measure_mono hsub
    _ ≤ t + (t + t) := (measure_union_le _ _).trans
        (add_le_add h1 ((measure_union_le _ _).trans (add_le_add h2 h3)))
    _ ≤ ε := ht3

/-- **Pointwise argmin consistency** (the single-`ω` form of `argmin_tendsto_of_uniform_approx`,
whose sequential shape does not fit the `ω`-wise application needed below): if `τ` is an
`e`-approximate minimizer of `z` over the ball `B̄(0,R)`, `z` approximates `g` within `δ` on
that ball, and the total slack `e + 2δ` undercuts the separation gap `η`, then `τ` is within
`ρ` of the unique minimizer `u₀`. -/
private theorem argmin_close_of_gap {g z : EuclideanSpace ℝ (Fin k) → ℝ≥0∞}
    {u₀ τ : EuclideanSpace ℝ (Fin k)} {R ρ : ℝ} {η δ e : ℝ≥0∞}
    (hunique : ∀ u, u ≠ u₀ → g u₀ < g u)
    (hgap : ∀ u, ‖u‖ ≤ R → ρ ≤ ‖u - u₀‖ → g u₀ + η ≤ g u)
    (hρ : 0 < ρ) (hu₀R : ‖u₀‖ ≤ R) (hτR : ‖τ‖ ≤ R)
    (happrox : ∀ u, ‖u‖ ≤ R → z u ≤ g u + δ ∧ g u ≤ z u + δ)
    (hmin : ∀ u, ‖u‖ ≤ R → z τ ≤ z u + e)
    (hslack : e + (δ + δ) < η) :
    ‖τ - u₀‖ < ρ := by
  by_contra hcon'
  have hcon : ρ ≤ ‖τ - u₀‖ := not_lt.1 hcon'
  have hne : τ ≠ u₀ := by
    intro h
    rw [h, sub_self, norm_zero] at hcon
    exact absurd hcon (not_le.2 hρ)
  have hfin : g u₀ ≠ ∞ := ne_top_of_lt (hunique _ hne)
  have hlow : g u₀ + η ≤ g τ := hgap _ hτR hcon
  have hup : g τ ≤ g u₀ + (e + (δ + δ)) :=
    calc g τ ≤ z τ + δ := (happrox τ hτR).2
      _ ≤ z u₀ + e + δ := by gcongr; exact hmin u₀ hu₀R
      _ ≤ g u₀ + δ + e + δ := by gcongr; exact (happrox u₀ hu₀R).1
      _ = g u₀ + (e + (δ + δ)) := by ring
  exact absurd ((ENNReal.add_le_add_iff_left hfin).1 (hlow.trans hup)) (not_le.2 hslack)

/-- **Bayes point estimators, recentred form.** Under the Bernstein–von Mises
conditions, the loss conditions, the prior moment, and the uniqueness of the minimizer `u₀`
of the limit criterion `g`, the approximate posterior-risk minimizers satisfy
`√n(Tₙ − θ₀) − Δ_{n,θ₀} → u₀` in `P^n_{θ₀}`-probability. -/
theorem bayes_estimator_asymptotics
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
    -- USER-INPUT: the uniform-tests condition; vdV §10.2
    (hTests : UniformlyConsistentTests M μ θ₀)
    -- USER-INPUT: the prior condition; vdV §10.2
    (hπ : HasLocalDensity π θ₀ r₀ f)
    -- LEAN-ONLY: measurable loss (regularity)
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the loss separation condition; vdV §10.3, p. 147
    (hsep : SeparatedLoss ℓ)
    -- LEAN-ONLY: nonnegative growth exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p)
    -- USER-INPUT: polynomial growth of the loss; vdV §10.3, p. 147
    (hpoly : PolyGrowthLoss p ℓ)
    -- USER-INPUT: finite prior `p`-moment; vdV §10.3
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞)
    -- LEAN-ONLY: measurable estimators (vdV p. 147: "an implicit assumption")
    (hT_meas : ∀ n, Measurable (T n))
    -- LEAN-ONLY: vanishing minimization tolerance (`εₙ = 0` is the book's exact case)
    (hεseq : Tendsto εseq atTop (𝓝 0))
    -- USER-INPUT: `Tₙ` approximately minimizes the posterior risk; vdV §10.3, p. 147
    (hT : ∀ n (ω : Fin n → 𝓧) (t : EuclideanSpace ℝ (Fin k)),
      bpePosteriorRisk κ π θ₀ ℓ n (Real.sqrt n • (T n ω - θ₀)) ω
        ≤ bpePosteriorRisk κ π θ₀ ℓ n t ω + εseq n)
    {u₀ : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: the limit criterion has the unique minimizer `u₀`; vdV §10.3
    -- ("provided that any two minimizers of this process coincide almost surely")
    (hunique : ∀ u, u ≠ u₀ → bpeGaussCriterion J ℓ u₀ < bpeGaussCriterion J ℓ u) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
          {ω | ε ≤ ‖Real.sqrt n • (T n ω - θ₀) - bvmEffScore J sc n ω - u₀‖})
        atTop (𝓝 0) := by
  classical
  intro ε hε
  haveI hprob : ∀ n : ℕ, IsProbabilityMeasure (productMeasure M μ θ₀ n) := fun n =>
    productMeasure_isProbabilityMeasure M μ hPDF θ₀ n
  set A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ with hAdef
  have hAeq : ∀ (n : ℕ) (ω : Fin n → 𝓧), bvmEffScore J sc n ω = A (scoreSum sc n ω) :=
    fun _ _ => by rw [hAdef]; rfl
  refine Metric.tendsto_atTop.2 fun ε' hε' => ?_
  set t : ℝ≥0∞ := ENNReal.ofReal (ε' / 4) with htdef
  have ht0 : 0 < t := by rw [htdef]; exact ENNReal.ofReal_pos.2 (by linarith)
  have httop : t ≠ ∞ := ENNReal.ofReal_ne_top
  -- Part 2: uniform tightness of the estimators; and tightness of the score sums.
  obtain ⟨K₁, hK₁pos, hK₁⟩ := bpe_tight hPDF hsc hDQM hJ_pd hJ hκ hM_joint hTests hπ hℓ
    hsep hp hpoly hmom hT_meas hεseq hT t ht0
  obtain ⟨K₂, hK₂pos, hK₂⟩ := scoreSum_uniformly_tight hPDF hsc hDQM hJ_pd hJ ht0
  -- a ball containing both the minimizer and (with high probability) the estimators
  set R : ℝ := ‖u₀‖ + 1 + K₁ + ‖A‖ * K₂ with hRdef
  have hAnn : 0 ≤ ‖A‖ * K₂ := mul_nonneg (norm_nonneg _) hK₂pos.le
  have hu₀R : ‖u₀‖ < R := by rw [hRdef]; linarith
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg u₀) hu₀R
  -- the limit criterion is continuous, hence well-separated at its unique minimizer
  have hg : Continuous (bpeGaussCriterion J ℓ) :=
    AsymptoticStatistics.gaussian_loss_convolution_continuous hJ_pd.inv hℓ hpoly hp
  obtain ⟨η, hη, hgap⟩ := exists_gap_of_unique_argmin hg hunique hu₀R hε
  -- a deterministic majorant tolerance `γ` whose triple undercuts the gap
  set η' : ℝ≥0∞ := min η 1 with hη'def
  have hη'pos : 0 < η' := lt_min hη zero_lt_one
  have hη'top : η' ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  set γ : ℝ≥0∞ := η' / 2 / 2 with hγdef
  have hγpos : 0 < γ := ENNReal.half_pos (ENNReal.half_pos hη'pos.ne').ne'
  have hγsum : γ + γ < η := by
    rw [hγdef, ENNReal.add_halves]
    exact lt_of_lt_of_le (ENNReal.half_lt_self hη'pos.ne' hη'top) (min_le_left _ _)
  -- Part 3: the uniform majorant approximation of the recentred posterior risk
  obtain ⟨Mn, -, hMn_tendsto, hMn_approx⟩ :=
    posteriorRisk_shifted_majorant hPDF hsc hDQM hJ_pd hJ hκ hM_joint hTests hπ hℓ hp hpoly
      hmom hR
  have hslack : ∀ᶠ n : ℕ in atTop, εseq n + (γ + γ) < η := by
    have hlim : Tendsto (fun n => εseq n + (γ + γ)) atTop (𝓝 (0 + (γ + γ))) :=
      hεseq.add tendsto_const_nhds
    rw [zero_add] at hlim
    exact (tendsto_order.1 hlim).2 η hγsum
  have hbad3 : ∀ᶠ n : ℕ in atTop,
      productMeasure M μ θ₀ n {ω | γ ≤ Mn n ω} < t :=
    (tendsto_order.1 (hMn_tendsto γ hγpos)).2 t ht0
  refine Filter.eventually_atTop.1 ?_
  filter_upwards [hK₁, hK₂, hbad3, hslack] with n h1 h2 h3 h4
  -- the bad event is covered by the three tight events
  have hsub : {ω : Fin n → 𝓧 |
        ε ≤ ‖Real.sqrt n • (T n ω - θ₀) - bvmEffScore J sc n ω - u₀‖} ⊆
      {ω | K₁ ≤ ‖Real.sqrt n • (T n ω - θ₀)‖} ∪
        ({ω | K₂ < ‖scoreSum sc n ω‖} ∪ {ω | γ ≤ Mn n ω}) := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le, not_lt] at hnot
    obtain ⟨hb1, hb2, hb3⟩ := hnot
    simp only [Set.mem_setOf_eq] at hω
    set Rn : EuclideanSpace ℝ (Fin k) :=
      Real.sqrt n • (T n ω - θ₀) - bvmEffScore J sc n ω with hRn
    have hΔnorm : ‖bvmEffScore J sc n ω‖ ≤ ‖A‖ * K₂ := by
      rw [hAeq n ω]
      exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb2 (norm_nonneg A))
    have hRnR : ‖Rn‖ ≤ R := by
      have hle := norm_sub_le (Real.sqrt n • (T n ω - θ₀)) (bvmEffScore J sc n ω)
      rw [← hRn] at hle
      rw [hRdef]
      linarith [norm_nonneg u₀]
    have hminz : ∀ u : EuclideanSpace ℝ (Fin k), ‖u‖ ≤ R →
        bpePosteriorRisk κ π θ₀ ℓ n (Rn + bvmEffScore J sc n ω) ω
          ≤ bpePosteriorRisk κ π θ₀ ℓ n (u + bvmEffScore J sc n ω) ω + εseq n := by
      intro u _
      have hid : Rn + bvmEffScore J sc n ω = Real.sqrt n • (T n ω - θ₀) := by
        rw [hRn]; abel
      rw [hid]
      exact hT n ω (u + bvmEffScore J sc n ω)
    have hsl : εseq n + (Mn n ω + Mn n ω) < η :=
      lt_of_le_of_lt (by gcongr) h4
    have hclose : ‖Rn - u₀‖ < ε :=
      argmin_close_of_gap hunique hgap hε hu₀R.le hRnR
        (fun u hu => hMn_approx n ω u hu) hminz hsl
    exact absurd hω (not_le.2 hclose)
  -- assemble the three probability bounds
  have hle : productMeasure M μ θ₀ n
      {ω | ε ≤ ‖Real.sqrt n • (T n ω - θ₀) - bvmEffScore J sc n ω - u₀‖} ≤ t + (t + t) := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    exact add_le_add h1 ((measure_union_le _ _).trans (add_le_add h2 h3.le))
  have hsumtop : t + (t + t) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨httop, ENNReal.add_ne_top.2 ⟨httop, httop⟩⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hcalc : (t + (t + t)).toReal = 3 * (ε' / 4) := by
    rw [ENNReal.toReal_add httop (ENNReal.add_ne_top.2 ⟨httop, httop⟩),
      ENNReal.toReal_add httop httop, htdef, ENNReal.toReal_ofReal (by linarith)]
    ring
  calc (productMeasure M μ θ₀ n).real
        {ω | ε ≤ ‖Real.sqrt n • (T n ω - θ₀) - bvmEffScore J sc n ω - u₀‖}
      ≤ (t + (t + t)).toReal := ENNReal.toReal_mono hsumtop hle
    _ = 3 * (ε' / 4) := hcalc
    _ < ε' := by linarith

/-- **Bayes point estimators, weak-convergence form**: `√n(Tₙ − θ₀) ⇝ N(u₀, J⁻¹)` under `P^n_{θ₀}`
(the law of `X + u₀` for `X ∼ N(0, J⁻¹)`, i.e. of the minimizer of the limit process). -/
theorem bayes_estimator_weakConverges
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
    -- USER-INPUT: the uniform-tests condition; vdV §10.2
    (hTests : UniformlyConsistentTests M μ θ₀)
    -- USER-INPUT: the prior condition; vdV §10.2
    (hπ : HasLocalDensity π θ₀ r₀ f)
    -- LEAN-ONLY: measurable loss (regularity)
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the loss separation condition; vdV §10.3, p. 147
    (hsep : SeparatedLoss ℓ)
    -- LEAN-ONLY: nonnegative growth exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p)
    -- USER-INPUT: polynomial growth of the loss; vdV §10.3, p. 147
    (hpoly : PolyGrowthLoss p ℓ)
    -- USER-INPUT: finite prior `p`-moment; vdV §10.3
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞)
    -- LEAN-ONLY: measurable estimators (vdV p. 147: "an implicit assumption")
    (hT_meas : ∀ n, Measurable (T n))
    -- LEAN-ONLY: vanishing minimization tolerance (`εₙ = 0` is the book's exact case)
    (hεseq : Tendsto εseq atTop (𝓝 0))
    -- USER-INPUT: `Tₙ` approximately minimizes the posterior risk; vdV §10.3, p. 147
    (hT : ∀ n (ω : Fin n → 𝓧) (t : EuclideanSpace ℝ (Fin k)),
      bpePosteriorRisk κ π θ₀ ℓ n (Real.sqrt n • (T n ω - θ₀)) ω
        ≤ bpePosteriorRisk κ π θ₀ ℓ n t ω + εseq n)
    {u₀ : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: the limit criterion has the unique minimizer `u₀`; vdV §10.3
    (hunique : ∀ u, u ≠ u₀ → bpeGaussCriterion J ℓ u₀ < bpeGaussCriterion J ℓ u) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map
        (fun ω => Real.sqrt n • (T n ω - θ₀)))
      (multivariateGaussian u₀ J⁻¹) := by
  classical
  haveI hprob : ∀ n : ℕ, IsProbabilityMeasure (productMeasure M μ θ₀ n) := fun n =>
    productMeasure_isProbabilityMeasure M μ hPDF θ₀ n
  haveI hGprob : IsProbabilityMeasure (multivariateGaussian u₀ J⁻¹) := inferInstance
  -- measurability of the score sums and of the estimators
  have hscsum : ∀ n : ℕ, Measurable (scoreSum sc n) := by
    intro n
    unfold AsymptoticStatistics.AsymptoticRepresentation.scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hsc.comp (measurable_pi_apply i))).const_smul ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  -- the affine map `z ↦ u₀ + J⁻¹ z`
  set A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ with hA
  have hfc : Continuous fun z : EuclideanSpace ℝ (Fin k) => u₀ + A z :=
    continuous_const.add A.continuous
  have hfm : Measurable fun z : EuclideanSpace ℝ (Fin k) => u₀ + A z :=
    measurable_const.add A.measurable
  -- the score CLT `scoreSum ⇝ N(0, J)`
  have hCLT := scoreSum_weakly_converges M μ θ₀ sc hsc (hPDF.density_integral_eq_one θ₀)
    (hPDF.density_integrable θ₀) (fun _ _ => hPDF.density_integral_eq_one _)
    (fun _ _ => hPDF.density_integrable _) hDQM J hJ_pd.posSemidef hJ
  -- push forward by the affine map: `u₀ + Δₙ ⇝ N(u₀, J⁻¹)`
  have hlim : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map
      (fun z => u₀ + A z) = multivariateGaussian u₀ J⁻¹ := by
    rw [show (fun z : EuclideanSpace ℝ (Fin k) => u₀ + A z) = (fun x => u₀ + x) ∘ A from rfl,
      ← Measure.map_map (measurable_const_add u₀) A.measurable,
      show (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map A
        = multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹ from
        AsymptoticStatistics.multivariateGaussian_map_matrix_inv hJ_pd,
      AsymptoticStatistics.multivariateGaussian_map_const_add]
  have hX : WeakConverges (fun n => (productMeasure M μ θ₀ n).map
      (fun ω => u₀ + bvmEffScore J sc n ω)) (multivariateGaussian u₀ J⁻¹) := by
    have hmap := hCLT.map hfc hfm
    rw [hlim] at hmap
    have hcomp : ∀ n : ℕ, ((productMeasure M μ θ₀ n).map (scoreSum sc n)).map
        (fun z => u₀ + A z) = (productMeasure M μ θ₀ n).map
          (fun ω => u₀ + bvmEffScore J sc n ω) := by
      intro n
      rw [Measure.map_map hfm (hscsum n)]
      rfl
    simpa only [hcomp] using hmap
  -- Slutsky: the estimators differ from `u₀ + Δₙ` by an `oₚ(1)`
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (X := fun n ω => u₀ + bvmEffScore J sc n ω)
    (Y := fun n ω => Real.sqrt n • (T n ω - θ₀))
    (fun n => (measurable_const.add (A.measurable.comp (hscsum n))).aemeasurable)
    (fun n => (((hT_meas n).sub measurable_const).const_smul
      (Real.sqrt (n : ℝ))).aemeasurable) hX ?_
  intro ε hε
  have hkey := bayes_estimator_asymptotics hPDF hsc hDQM hJ_pd hJ hκ hM_joint hTests hπ
    hℓ hsep hp hpoly hmom hT_meas hεseq hT hunique ε hε
  refine hkey.congr fun n => ?_
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, dist_eq_norm]
  rw [show u₀ + bvmEffScore J sc n ω - Real.sqrt n • (T n ω - θ₀)
      = -(Real.sqrt n • (T n ω - θ₀) - bvmEffScore J sc n ω - u₀) by abel, norm_neg]

/-- **Anderson step**: for a bowl-shaped loss, the unique minimizer of the limit criterion
is the origin (`anderson_lemma_loss` gives `g(0) ≤ g(u)`; uniqueness upgrades it to
`u₀ = 0`). -/
theorem gaussCriterion_argmin_zero_of_bowlShaped
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef)
    -- USER-INPUT: bowl-shaped loss; vdV §8.5
    (hL : BowlShaped ℓ) {u₀ : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: the limit criterion has the unique minimizer `u₀`; vdV §10.3
    (hunique : ∀ u, u ≠ u₀ → bpeGaussCriterion J ℓ u₀ < bpeGaussCriterion J ℓ u) :
    u₀ = 0 := by
  -- Anderson's lemma: the criterion is minimized at the origin.
  have hmin : ∀ u, bpeGaussCriterion J ℓ 0 ≤ bpeGaussCriterion J ℓ u := by
    intro u
    have hzero : bpeGaussCriterion J ℓ 0
        = ∫⁻ z, ℓ z ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := by
      simp only [bpeGaussCriterion, zero_sub]
      exact lintegral_congr fun z => hL.symm z
    have hu : bpeGaussCriterion J ℓ u
        = ∫⁻ z, ℓ (z + -u) ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := by
      refine lintegral_congr fun z => ?_
      rw [← hL.symm (u - z)]
      congr 1
      abel
    rw [hzero, hu]
    exact AsymptoticStatistics.anderson_lemma_loss hJ_pd.inv.posSemidef hL (-u)
  by_contra hne
  exact absurd (hmin u₀) (not_le.2 (hunique 0 (Ne.symm hne)))

/-- **Bayes point estimators for bowl-shaped losses** (vdV: "In particular, for every nonzero,
subconvex loss function it converges to `X`"): the standardized Bayes estimators are
asymptotically efficient, `√n(Tₙ − θ₀) ⇝ N(0, J⁻¹)`. -/
theorem bayes_estimator_asymptotics_bowlShaped
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
    -- USER-INPUT: the uniform-tests condition; vdV §10.2
    (hTests : UniformlyConsistentTests M μ θ₀)
    -- USER-INPUT: the prior condition; vdV §10.2
    (hπ : HasLocalDensity π θ₀ r₀ f)
    -- USER-INPUT: bowl-shaped loss; vdV §8.5
    (hL : BowlShaped ℓ)
    -- USER-INPUT: the loss separation condition; vdV §10.3, p. 147
    (hsep : SeparatedLoss ℓ)
    -- LEAN-ONLY: nonnegative growth exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p)
    -- USER-INPUT: polynomial growth of the loss; vdV §10.3, p. 147
    (hpoly : PolyGrowthLoss p ℓ)
    -- USER-INPUT: finite prior `p`-moment; vdV §10.3
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞)
    -- LEAN-ONLY: measurable estimators (vdV p. 147: "an implicit assumption")
    (hT_meas : ∀ n, Measurable (T n))
    -- LEAN-ONLY: vanishing minimization tolerance (`εₙ = 0` is the book's exact case)
    (hεseq : Tendsto εseq atTop (𝓝 0))
    -- USER-INPUT: `Tₙ` approximately minimizes the posterior risk; vdV §10.3, p. 147
    (hT : ∀ n (ω : Fin n → 𝓧) (t : EuclideanSpace ℝ (Fin k)),
      bpePosteriorRisk κ π θ₀ ℓ n (Real.sqrt n • (T n ω - θ₀)) ω
        ≤ bpePosteriorRisk κ π θ₀ ℓ n t ω + εseq n)
    {u₀ : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: the limit criterion has the unique minimizer `u₀`; vdV §10.3
    (hunique : ∀ u, u ≠ u₀ → bpeGaussCriterion J ℓ u₀ < bpeGaussCriterion J ℓ u) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map
        (fun ω => Real.sqrt n • (T n ω - θ₀)))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := by
  have hu₀ : u₀ = 0 := gaussCriterion_argmin_zero_of_bowlShaped hJ_pd hL hunique
  subst hu₀
  exact bayes_estimator_weakConverges hPDF hsc hDQM hJ_pd hJ hκ hM_joint hTests hπ
    hL.measurable hsep hp hpoly hmom hT_meas hεseq hT hunique

end StatLean.Bayesian
