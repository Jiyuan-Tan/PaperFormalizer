module
public import StatLean.HypothesisTesting.GoodnessOfFit.AsymptoticMaximin
public import StatLean.PointEstimation.ExponentialFamily.Defs
public import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity
public import StatLean.AsymptoticStatistics.ParametricFamily.ScoreCLT
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianWeakLimit
public import Mathlib.Probability.HasLawExists

@[expose] public section

/-!
# Smooth tests of fit: the fixed-`k` theory

To test a fully specified null law `P₀` on an arbitrary sample space, embed it in the
`k`-parameter exponential family of densities with respect to `P₀`
$$ p_\theta(x) \;=\; C_k(\theta)\,
     \exp\Bigl(\sum_{j=1}^{k} \theta_j\, \psi_j(x)\Bigr), \qquad \theta \in \mathbb R^k, $$
where `ψ₁, …, ψ_k` — together with the constant function `ψ₀ = 1` — are orthonormal in
`L²(P₀)`. The null hypothesis is `θ = 0`, and the score test for it rejects for large
values of
$$ S_n \;=\; \sum_{j=1}^{k} Z_{n,j}^2, \qquad
   Z_{n,j} \;=\; n^{-1/2}\sum_{i=1}^{n} \psi_j(X_i). $$
This is the smooth test. It is the score (Rao) test of the embedding family, whence its
optimality; and it contains the chi-squared test of the previous files as the special case
of a multinomial sample space with `ψ` the standardized cell indicators.

Contents:

* `smoothModel` — the embedding exponential family, built through the point-estimation
  area's `ExpFamily.ofDensity` over the base `P₀`;
* `smoothScore`, `smoothStat` — the score components `Z_{n,j}` and the statistic `Sₙ`;
* `smoothStat_weakConverges_chiSquared` — under `P₀`, `Sₙ ⇒ χ²_k`;
* `smoothTest_maximin_upper_bound` — no asymptotically level-`α` test beats
  `P{χ²_k(b²) > c_{k,1−α}}` in minimum power over `b ≤ |h| ≤ B`;
* `smoothTest_asymptotically_maximin` — the smooth test attains that value.

The last two are the instances of `AsymptoticMaximin.asymptotic_maximin_upper_bound` in
which the information matrix is the identity: orthonormality of the `ψⱼ` in `L²(P₀)` makes
the Fisher information of the embedding family at `θ = 0` equal to `Iₖ`, so the local shell
of the transfer lemma is the Euclidean shell `b ≤ |h| ≤ B` and the maximin value is the
same noncentral chi-squared number that appeared for Pearson's test.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 16 (Testing Goodness of
Fit), §16.4 (Neyman's Smooth Tests), Theorem 16.4.1 (§16.4.1, Fixed `k` Asymptotics): Neyman's
smooth test is asymptotically maximin. (`TSH4 §16.4 Thm 16.4.1`.)

**Proof formalization notes.**
* `smoothModel` is `ExpFamily.ofDensity P₀ 1 ψ⃗ _`: the carrier is trivial and the base of
  the exponential family is `P₀` itself (`P₀.withDensity 1 = P₀`, a lemma at the point of
  use, not a definitional equality). The natural statistic is the vector
  `x ↦ (ψ₁ x, …, ψ_k x)` in `EuclideanSpace ℝ (Fin k)`, so `E.P θ` is exactly the density
  displayed above, with `A(θ) = −log C_k(θ)` the log-partition function. The prototype —
  testing uniformity on `[0,1]` with normalized Legendre polynomials — is the case
  `P₀ = ` uniform, and nothing in this file is special to it.
* Orthonormality is recorded as two hypotheses: `∫ ψᵢψⱼ dP₀ = δᵢⱼ` and `∫ ψⱼ dP₀ = 0`. The
  second is orthogonality to the constant function `ψ₀ = 1` and is what makes the score at
  `θ = 0` centred; it is a consequence of the first only if the constant is included in
  the system, which is why it is stated separately.
* `θ = 0` is required to be an interior point of the natural parameter set — the full-rank
  condition making the family q.m.d. at the null and its information matrix invertible.
* The score is scaled as `n^{-1/2} ∑ᵢ ψⱼ(Xᵢ)` rather than as a derivative of the
  log-likelihood: the identification of the two (the derivative of the log-partition
  function vanishes at `θ = 0` because `E₀ψⱼ = 0`) is a lemma about `smoothModel`, not
  part of the definition of the statistic.
* The local experiments of the two maximin statements are carried as data `Q n h` and tied
  to `smoothModel` by the requirement that the observations be i.i.d. with law
  `E.P (n^{-1/2} • h)`; this is the same format as in `ChiSquaredMaximin.lean`.
* The upper bound is stated for a finite outer radius `B`. The unbounded case `B = ∞`
  follows a fortiori, the infimum over a larger set being smaller. The *attainment* half,
  in contrast, genuinely needs `B < ∞`: its `liminf ≥` direction is a compactness argument
  on the shell (see `smoothTest_shell_minPower_tendsto`), and an unbounded shell admits
  near-minimising sequences with `‖hₙ‖ → ∞`, for which a separate divergence estimate would
  be required.

**Bibliographic comments.** The smooth test, the embedding family, and the asymptotic
maximin property against the alternatives it generates are due to J. Neyman ("Smooth test
for goodness of fit," *Skandinavisk Aktuarietidskrift* **20** (1937), 149–199). The score
statistic it specialises is due to C. R. Rao ("Large sample tests of statistical hypotheses
concerning several parameters with applications to problems of estimation," *Proc. Camb.
Phil. Soc.* **44** (1948), 50–57). The reduction of the local optimality question to a
Gaussian shift experiment follows L. Le Cam (*Univ. California Publ. Statist.* **3**
(1960), 37–98); the special case in which the statistic reduces to Pearson's is due to
K. Pearson (*Phil. Mag.* **50** (1900), 157–175). Later developments, including data-driven
choice of `k`, are surveyed in J. C. W. Rayner and D. J. Best, *Smooth Tests of Goodness of
Fit*, Oxford University Press, 1989.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators InnerProductSpace

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)
open StatLean.MultipleTesting (chiSquared)
open StatLean.PointEstimation (ExpFamily)

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]

/-! ### The embedding family and the statistic -/

/-- The **smooth model**: the `k`-parameter exponential family through the score functions
`ψ₁, …, ψ_k`, with densities `C_k(θ) exp(∑ⱼ θⱼ ψⱼ(x))` with respect to the null law `P₀`.

Built with the point-estimation area's `ExpFamily.ofDensity` with trivial carrier, so that
the base measure of the family is `P₀` itself and the natural statistic is the vector of
score functions. The null hypothesis is the canonical parameter `θ = 0`, at which the
member measure is `P₀`. -/
noncomputable def smoothModel {k : ℕ} (P₀ : Measure 𝓧) (ψ : Fin k → 𝓧 → ℝ)
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k))) :
    ExpFamily 𝓧 (EuclideanSpace ℝ (Fin k)) :=
  ExpFamily.ofDensity P₀ (fun _ => 1) (fun x => WithLp.toLp 2 fun j => ψ j x) hψ

/-- The **`j`-th smooth score component** `Z_{n,j} = n^{-1/2} ∑ᵢ ψⱼ(Xᵢ)`. Under the null
law it is centred (because `∫ ψⱼ dP₀ = 0`) with variance one (because `∫ ψⱼ² dP₀ = 1`), and
its components are asymptotically uncorrelated (because `∫ ψᵢψⱼ dP₀ = 0` for `i ≠ j`).
For `n = 0` it is the junk value `0`. -/
noncomputable def smoothScore {n k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (X : Fin n → Ω → 𝓧)
    (j : Fin k) (ω : Ω) : ℝ :=
  (∑ i, ψ j (X i ω)) / Real.sqrt (n : ℝ)

/-- **Neyman's smooth statistic** `Sₙ = ∑_{j=1}^{k} Z_{n,j}²`: the squared Euclidean norm
of the score vector, i.e. the score (Rao) statistic of the smooth model at `θ = 0`, the
Fisher information there being the identity. -/
noncomputable def smoothStat {n k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (X : Fin n → Ω → 𝓧)
    (ω : Ω) : ℝ :=
  ∑ j : Fin k, (smoothScore ψ X j ω) ^ 2

/-! #### Vectorised scores and the multivariate CLT brick

The null-limit proof mirrors `GoodnessOfFit/ChiSquaredMultinomial.lean`. The score functions
are already centred in `L²(P₀)` (`E₀ψⱼ = 0`) with covariance the identity (`∫ψᵢψⱼ = δᵢⱼ`),
so the per-observation vector `psiVec x = (ψ₁ x, …, ψ_k x)` has mean zero and covariance
`Iₖ`; the standardised sum converges to `N(0, Iₖ)` and the squared norm is `Sₙ`. -/

/-- The per-observation score vector `x ↦ (ψ₁ x, …, ψ_k x)` in `EuclideanSpace ℝ (Fin k)`.

Not private: the multinomial maximin bound of `ChiSquaredMaximin.lean` runs this file's
canonical-experiment machinery with `𝓧 = Fin (k+1)` and the whitened multinomial scores. -/
noncomputable def psiVec {k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (x : 𝓧) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j => ψ j x)

/-- The standardised score vector `Zₙ = (√n)⁻¹ ∑ᵢ ψ(Xᵢ)`, whose `j`-th coordinate is
`smoothScore ψ X j` and whose squared norm is `smoothStat`. -/
private noncomputable def scoreVec {n k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (X : Fin n → Ω → 𝓧) (ω : Ω) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j => smoothScore ψ X j ω)

/-- The real inner product on `EuclideanSpace ℝ (Fin k)` as a coordinate sum. -/
private lemma inner_euclidean_sum {k : ℕ} (u w : EuclideanSpace ℝ (Fin k)) :
    ⟪u, w⟫_ℝ = ∑ i, u i * w i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The standardised score vector is measurable. -/
private lemma measurable_scoreVec {n k : ℕ} {ψ : Fin k → 𝓧 → ℝ}
    {X : Fin n → Ω → 𝓧} (hψmeas : ∀ j, Measurable (ψ j)) (hX : ∀ i, Measurable (X i)) :
    Measurable (scoreVec ψ X) := by
  have hg : Measurable (fun ω (j : Fin k) => smoothScore ψ X j ω) := by
    refine measurable_pi_iff.mpr (fun j => ?_)
    simp only [smoothScore]
    exact (Finset.univ.measurable_sum (fun i _ => (hψmeas j).comp (hX i))).div measurable_const
  exact (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp hg

/-- `scoreVec` is the standardised sum of the per-observation score vectors. -/
private lemma scoreVec_eq_smul_sum {n k : ℕ} (ψ : Fin k → 𝓧 → ℝ)
    (X : Fin n → Ω → 𝓧) (ω : Ω) :
    scoreVec ψ X ω = (Real.sqrt n)⁻¹ • ∑ i : Fin n, psiVec ψ (X i ω) := by
  rw [scoreVec]
  simp only [psiVec]
  rw [← WithLp.toLp_sum, ← WithLp.toLp_smul]
  refine congrArg (WithLp.toLp 2) ?_
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [smoothScore, div_eq_inv_mul]

/-- **Multivariate CLT for the score vector** (the single deep analytic brick of the
null-limit proof). Under `P₀`, with the score functions orthonormal and centred in `L²(P₀)`,
the standardised score vector converges in law to the standard Gaussian `N(0, Iₖ)`.

The proof realises `scoreVec` as the standardised sum of the per-observation score vectors
`psiVec x = (ψⱼ x)ⱼ` (`scoreVec_eq_smul_sum`), transfers the per-stage law to the canonical
infinite-product i.i.d. model produced by `ProbabilityTheory.exists_iid` (matching both
sequences to `(Measure.pi …).map` via `iIndepFun_iff_map_fun_eq_pi_map`), and applies the
reusable fixed-i.i.d. CLT `AsymptoticStatistics.ParametricFamily.ScoreCLT.clt_finDim`. The
zero-mean side-condition is `hcentred`, and the covariance side-condition
`∫ ⟪u, g⟫⟪v, g⟫ = u ⬝ᵥ Iₖ v` is `hortho`. -/
private lemma scoreVec_weakConverges_gaussian {k : ℕ} {P₀ : Measure 𝓧}
    [IsProbabilityMeasure P₀] {ψ : Fin k → 𝓧 → ℝ} {P : ℕ → Measure Ω}
    [∀ n, IsProbabilityMeasure (P n)] {X : (n : ℕ) → Fin n → Ω → 𝓧}
    (hψmeas : ∀ j, Measurable (ψ j))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    (hX : ∀ n i, Measurable (X n i))
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hlaw : ∀ n i, (P n).map (X n i) = P₀) :
    WeakConverges (fun n => (P n).map (scoreVec ψ (X n)))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
        (1 : Matrix (Fin k) (Fin k) ℝ)) := by
  classical
  -- Integrability from `L²` (the covariance identity `∫ ψᵢ² = 1` forces `ψᵢ ∈ L²`).
  have hsqint : ∀ i, Integrable (fun x => ψ i x ^ 2) P₀ := by
    intro i
    have h1 : (∫ x, ψ i x * ψ i x ∂P₀) = 1 := by rw [hortho i i]; simp
    simpa [sq] using integrable_of_integral_eq_one h1
  have hψL2 : ∀ i, MemLp (ψ i) 2 P₀ := fun i =>
    (memLp_two_iff_integrable_sq (hψmeas i).aestronglyMeasurable).2 (hsqint i)
  have hψint : ∀ i, Integrable (ψ i) P₀ := fun i => (hψL2 i).integrable one_le_two
  have hψψint : ∀ i j, Integrable (fun x => ψ i x * ψ j x) P₀ := fun i j => by
    simpa using! (hψL2 i).integrable_mul (hψL2 j)
  -- the canonical i.i.d. model `(Ω₀, P₀c, Z)` with marginal law `P₀`
  obtain ⟨Ω₀, mΩ₀, P₀c, Z, hZmeas, hZlaw, hZindep, hP₀cprob⟩ :=
    ProbabilityTheory.exists_iid ℕ P₀
  letI : MeasurableSpace Ω₀ := mΩ₀
  haveI : IsProbabilityMeasure P₀c := hP₀cprob
  -- per-observation score map `g` and per-observation vectors `Y`
  set g : 𝓧 → EuclideanSpace ℝ (Fin k) := fun x => psiVec ψ x with hg
  have hgmeas : Measurable g :=
    (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp (measurable_pi_lambda _ (fun j => hψmeas j))
  set Y : ℕ → Ω₀ → EuclideanSpace ℝ (Fin k) := fun i ω => g (Z i ω) with hY
  -- an integral of `F ∘ Z 0` reduces to an integral over `P₀`
  have hkey : ∀ (F : 𝓧 → ℝ), AEStronglyMeasurable F P₀ →
      ∫ ω, F (Z 0 ω) ∂P₀c = ∫ x, F x ∂P₀ := by
    intro F hF
    rw [show (∫ ω, F (Z 0 ω) ∂P₀c) = ∫ x, F x ∂(P₀c.map (Z 0)) from
          (integral_map (hZmeas 0).aemeasurable (by rw [(hZlaw 0).map_eq]; exact hF)).symm,
        (hZlaw 0).map_eq]
  -- inputs to `clt_finDim`
  have hYmeas : ∀ i, Measurable (Y i) := fun i => hgmeas.comp (hZmeas i)
  have hYindep : iIndepFun Y P₀c := hZindep.comp (fun _ => g) (fun _ => hgmeas)
  have hYident : ∀ i, IdentDistrib (Y i) (Y 0) P₀c P₀c := fun i =>
    (show IdentDistrib (Z i) (Z 0) P₀c P₀c from
      ⟨(hZmeas i).aemeasurable, (hZmeas 0).aemeasurable,
        (hZlaw i).map_eq.trans (hZlaw 0).map_eq.symm⟩).comp hgmeas
  -- the score vector has zero mean
  have h_zero_mean : ∀ u : EuclideanSpace ℝ (Fin k), ∫ ω, ⟪u, Y 0 ω⟫_ℝ ∂P₀c = 0 := by
    intro u
    have hFint : Integrable (fun x => ⟪u, g x⟫_ℝ) P₀ := by
      have hpt : (fun x => ⟪u, g x⟫_ℝ) = (fun x => ∑ i, u i * ψ i x) := by
        funext x; rw [inner_euclidean_sum]; rfl
      rw [hpt]
      exact integrable_finset_sum _ (fun i _ => (hψint i).const_mul (u i))
    rw [hkey _ hFint.aestronglyMeasurable]
    have hpt : (fun x => ⟪u, g x⟫_ℝ) = (fun x => ∑ i, u i * ψ i x) := by
      funext x; rw [inner_euclidean_sum]; rfl
    rw [hpt, integral_finset_sum _ (fun i _ => (hψint i).const_mul (u i))]
    simp_rw [integral_const_mul, hcentred, mul_zero, Finset.sum_const_zero]
  -- the covariance identity `∫ ⟪u,·⟫⟪v,·⟫ = u ⬝ Iₖ v`
  have h_cov : ∀ u v : EuclideanSpace ℝ (Fin k),
      ∫ ω, ⟪u, Y 0 ω⟫_ℝ * ⟪v, Y 0 ω⟫_ℝ ∂P₀c
        = u.ofLp ⬝ᵥ (1 : Matrix (Fin k) (Fin k) ℝ).mulVec v.ofLp := by
    intro u v
    have hpt : (fun x => ⟪u, g x⟫_ℝ * ⟪v, g x⟫_ℝ)
        = (fun x => ∑ i, ∑ j, (u i * v j) * (ψ i x * ψ j x)) := by
      funext x
      rw [inner_euclidean_sum, inner_euclidean_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      show (u i * ψ i x) * (v j * ψ j x) = (u i * v j) * (ψ i x * ψ j x)
      ring
    have hFint : Integrable (fun x => ⟪u, g x⟫_ℝ * ⟪v, g x⟫_ℝ) P₀ := by
      rw [hpt]
      exact integrable_finset_sum _
        (fun i _ => integrable_finset_sum _ (fun j _ => (hψψint i j).const_mul (u i * v j)))
    rw [hkey _ hFint.aestronglyMeasurable, hpt,
      integral_finset_sum _
        (fun i _ => integrable_finset_sum _ (fun j _ => (hψψint i j).const_mul (u i * v j)))]
    have hRHS : u.ofLp ⬝ᵥ (1 : Matrix (Fin k) (Fin k) ℝ).mulVec v.ofLp = ∑ i, u i * v i := by
      rw [Matrix.one_mulVec]; rfl
    rw [hRHS]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finset_sum _ (fun j _ => (hψψint i j).const_mul (u i * v j))]
    simp_rw [integral_const_mul, hortho i]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [if_neg (Ne.symm hji), mul_zero])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [if_pos rfl, mul_one]
  -- the score vector is square-integrable
  have h_L2 : MemLp (Y 0) 2 P₀c := by
    have hg_L2 : MemLp g 2 P₀ := by
      refine (memLp_two_iff_integrable_sq_norm hgmeas.aestronglyMeasurable).2 ?_
      have hnorm : (fun x => ‖g x‖ ^ 2) = (fun x => ∑ i, ψ i x ^ 2) := by
        funext x
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Real.norm_eq_abs, sq_abs]
        rfl
      rw [hnorm]
      exact integrable_finset_sum _ (fun i _ => hsqint i)
    have hmap : MemLp g 2 (P₀c.map (Z 0)) := by rw [(hZlaw 0).map_eq]; exact hg_L2
    exact (memLp_map_measure_iff hmap.aestronglyMeasurable (hZmeas 0).aemeasurable).1 hmap
  -- the fixed-i.i.d. CLT for the canonical model
  have hclt := AsymptoticStatistics.ParametricFamily.ScoreCLT.clt_finDim
    P₀c Y hYmeas hYindep hYident h_zero_mean (1 : Matrix (Fin k) (Fin k) ℝ)
    Matrix.PosDef.one.posSemidef h_cov h_L2
  -- the canonical standardised sum matches `scoreVec` in law at each `n`
  have hmatch : ∀ n : ℕ,
      P₀c.map (fun ω => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω)
        = (P n).map (scoreVec ψ (X n)) := by
    intro n
    set F : (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k) :=
      fun d => (Real.sqrt n)⁻¹ • ∑ i : Fin n, g (d i) with hF
    have hsum : Measurable (fun d : Fin n → 𝓧 => ∑ i : Fin n, g (d i)) :=
      Finset.univ.measurable_sum (fun i _ => hgmeas.comp (measurable_pi_apply i))
    have hFmeas : Measurable F := by rw [hF]; exact measurable_const.fun_smul hsum
    have hgZ : Measurable (fun ω (i : Fin n) => Z (i : ℕ) ω) :=
      measurable_pi_lambda _ (fun i => hZmeas i)
    have hgX : Measurable (fun ω (i : Fin n) => X n i ω) :=
      measurable_pi_lambda _ (fun i => hX n i)
    have hLHSfun : (fun ω => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω)
        = F ∘ (fun ω (i : Fin n) => Z (i : ℕ) ω) := by
      funext ω
      simp only [hF, hY, Function.comp]
      rw [← Fin.sum_univ_eq_sum_range (fun i => g (Z i ω)) n]
    have hRHSfun : scoreVec ψ (X n) = F ∘ (fun ω (i : Fin n) => X n i ω) := by
      funext ω
      rw [scoreVec_eq_smul_sum ψ (X n) ω]
      simp only [hF, hg, Function.comp]
    have hpiZ : P₀c.map (fun ω (i : Fin n) => Z (i : ℕ) ω)
        = Measure.pi (fun _ : Fin n => P₀) := by
      have hsub : iIndepFun (fun (i : Fin n) => Z (i : ℕ)) P₀c :=
        hZindep.precomp Fin.val_injective
      rw [(iIndepFun_iff_map_fun_eq_pi_map (f := fun (i : Fin n) => Z (i : ℕ))
        (fun i => (hZmeas (i : ℕ)).aemeasurable)).1 hsub]
      congr 1; funext i; exact (hZlaw (i : ℕ)).map_eq
    have hpiX : (P n).map (fun ω (i : Fin n) => X n i ω)
        = Measure.pi (fun _ : Fin n => P₀) := by
      rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX n i).aemeasurable)).1 (hindep n)]
      congr 1; funext i; exact hlaw n i
    rw [hLHSfun, hRHSfun, ← Measure.map_map hFmeas hgZ, ← Measure.map_map hFmeas hgX,
      hpiZ, hpiX]
  simp only [hmatch] at hclt
  exact hclt

/-! ### The null limiting distribution -/

/-- **Null limit of the smooth statistic.** For an i.i.d. sample from the null law `P₀`
and score functions orthonormal in `L²(P₀)` and orthogonal to the constants, the smooth
statistic converges in law to `χ²_k`. Hence the test rejecting when `Sₙ > c_{k,1−α}` is
asymptotically of level `α`.

This is the multivariate central limit theorem for the score vector (`Zₙ ⇒ N(0, Iₖ)`)
followed by the continuous mapping theorem applied to the squared norm. -/
theorem smoothStat_weakConverges_chiSquared {k : ℕ} {P₀ : Measure 𝓧}
    [IsProbabilityMeasure P₀] {ψ : Fin k → 𝓧 → ℝ} {P : ℕ → Measure Ω}
    [∀ n, IsProbabilityMeasure (P n)] {X : (n : ℕ) → Fin n → Ω → 𝓧}
    -- USER-INPUT: at least one score direction; `χ²₀` is degenerate
    (hk : 0 < k)
    -- USER-INPUT: the score functions are measurable
    (hψmeas : ∀ j, Measurable (ψ j))
    -- USER-INPUT: the score functions are orthonormal in `L²(P₀)`; Neyman 1937
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    -- USER-INPUT: the score functions are orthogonal to the constants, i.e. `E₀ψⱼ = 0`
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the observations are i.i.d.; Neyman 1937
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: the null hypothesis: every observation has law `P₀`
    (hlaw : ∀ n, ∀ i, (P n).map (X n i) = P₀) :
    WeakConverges (fun n => (P n).map (smoothStat ψ (X n))) (chiSquared k) := by
  -- the continuous quadratic form `q z = ⟪z, Iₖ⁻¹ z⟫ = ‖z‖²`
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Matrix (Fin k) (Fin k) ℝ)⁻¹ with hTdef
  set q : EuclideanSpace ℝ (Fin k) → ℝ := fun z => ⟪z, T z⟫_ℝ with hqdef
  have hq_cont : Continuous q := continuous_id.inner T.continuous
  -- pointwise: `q (scoreVec ω) = smoothStat ω`
  have hq : ∀ n ω, q (scoreVec ψ (X n) ω) = smoothStat ψ (X n) ω := by
    intro n ω
    simp only [hqdef, hTdef]
    rw [Matrix.inner_toEuclideanCLM, inv_one, Matrix.one_mulVec]
    simp only [smoothStat, dotProduct]
    exact Finset.sum_congr rfl (fun j _ => by rw [sq]; rfl)
  -- the lifted CLT brick, then continuous mapping
  have hbrick := scoreVec_weakConverges_gaussian (P₀ := P₀) (ψ := ψ) (P := P) (X := X)
    hψmeas hortho hcentred hX hindep hlaw
  have hmapped := hbrick.map hq_cont hq_cont.measurable
  -- the target is `χ²_k` (Gaussian → chi-squared bridge, covariance the identity)
  have htarget : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
      (1 : Matrix (Fin k) (Fin k) ℝ)).map q = chiSquared k := by
    simp only [hqdef, hTdef]
    exact multivariateGaussian_map_inner_inv_eq_chiSquared hk Matrix.PosDef.one
  -- each pushforward term equals the law of `smoothStat`
  have hseq : (fun n => ((P n).map (scoreVec ψ (X n))).map q)
      = fun n => (P n).map (smoothStat ψ (X n)) := by
    funext n
    rw [Measure.map_map hq_cont.measurable (measurable_scoreVec hψmeas (hX n))]
    exact Measure.map_congr (Filter.Eventually.of_forall (fun ω => hq n ω))
  rw [hseq, htarget] at hmapped
  exact hmapped

/-! ### Bricks for the maximin upper bound

The upper bound is the instance of `AsymptoticMaximin.asymptotic_maximin_upper_bound` in which
the local experiments are the canonical i.i.d. experiments of the smooth model.  The bricks
below supply, in order: the coordinate form of the inner product against the score vector; the
elementary real inequalities behind the quadratic expansion of the log-partition function; the
sign-vector envelope that makes every exponential moment finite; the expansion itself; the
weak limit of the canonical score law; and the explicit exponential-tilt representation of the
members of the smooth model. -/

/-- The inner product against the per-observation score vector, in coordinates. -/
lemma inner_psiVec {k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (u : EuclideanSpace ℝ (Fin k))
    (x : 𝓧) : ⟪u, psiVec ψ x⟫_ℝ = ∑ j, u j * ψ j x := by
  rw [inner_euclidean_sum]
  exact Finset.sum_congr rfl fun j _ => rfl

/-! ### Elementary real inequalities -/

/-- `|e^z − (1 + z + z²/2)| ≤ 4 |z|³ e^{|z|}` for every real `z`. -/
private lemma abs_exp_sub_quadratic_le (z : ℝ) :
    |Real.exp z - (1 + z + z ^ 2 / 2)| ≤ 4 * |z| ^ 3 * Real.exp |z| := by
  have hexp1 : (1 : ℝ) ≤ Real.exp |z| := Real.one_le_exp (abs_nonneg z)
  have hcube0 : (0 : ℝ) ≤ |z| ^ 3 := pow_nonneg (abs_nonneg z) 3
  rcases le_or_gt |z| 1 with hle | hgt
  · have h := Real.exp_bound hle (n := 3) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 3, z ^ m / (Nat.factorial m) = 1 + z + z ^ 2 / 2 := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    rw [hsum] at h
    have hcoef : ((Nat.succ 3 : ℝ) / ((Nat.factorial 3 : ℝ) * 3)) ≤ 4 := by
      norm_num [Nat.factorial]
    calc |Real.exp z - (1 + z + z ^ 2 / 2)|
        ≤ |z| ^ 3 * ((Nat.succ 3 : ℝ) / ((Nat.factorial 3) * 3)) := h
      _ ≤ |z| ^ 3 * 4 := by nlinarith
      _ ≤ 4 * |z| ^ 3 * Real.exp |z| := by nlinarith
  · -- `|z| > 1`: crude triangle-inequality bound
    have habs0 : (0 : ℝ) ≤ |z| := abs_nonneg z
    have h1 : (1 : ℝ) ≤ |z| ^ 3 := one_le_pow₀ hgt.le
    have hd : 0 ≤ |z| * ((|z| - 1) * (|z| + 1)) :=
      mul_nonneg habs0 (mul_nonneg (by linarith) (by linarith))
    have hz : |z| ≤ |z| ^ 3 := by nlinarith
    have hd2 : 0 ≤ (|z| * |z|) * (|z| - 1) :=
      mul_nonneg (mul_nonneg habs0 habs0) (by linarith)
    have hz2 : z ^ 2 ≤ |z| ^ 3 := by
      have hsq : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
      nlinarith
    have hexpz : Real.exp z ≤ Real.exp |z| := Real.exp_le_exp.mpr (le_abs_self z)
    have htri : |Real.exp z - (1 + z + z ^ 2 / 2)|
        ≤ |Real.exp z| + |1 + z + z ^ 2 / 2| := by
      rw [sub_eq_add_neg]
      refine (abs_add_le _ _).trans_eq ?_
      rw [abs_neg]
    have hterm : |1 + z + z ^ 2 / 2| ≤ 3 * |z| ^ 3 := by
      have hb : |1 + z + z ^ 2 / 2| ≤ 1 + |z| + z ^ 2 / 2 := by
        have h₁ : |1 + z + z ^ 2 / 2| ≤ |1 + z| + |z ^ 2 / 2| := abs_add_le _ _
        have h₂ : |1 + z| ≤ 1 + |z| := by
          calc |1 + z| ≤ |(1 : ℝ)| + |z| := abs_add_le _ _
            _ = 1 + |z| := by norm_num
        have h₃ : |z ^ 2 / 2| = z ^ 2 / 2 := abs_of_nonneg (by positivity)
        linarith
      linarith
    have hexpabs : |Real.exp z| = Real.exp z := abs_of_nonneg (Real.exp_pos z).le
    have hstep : Real.exp |z| ≤ |z| ^ 3 * Real.exp |z| := by nlinarith [Real.exp_pos |z|]
    calc |Real.exp z - (1 + z + z ^ 2 / 2)|
        ≤ |Real.exp z| + |1 + z + z ^ 2 / 2| := htri
      _ ≤ Real.exp |z| + 3 * |z| ^ 3 := by rw [hexpabs]; linarith
      _ ≤ 4 * |z| ^ 3 * Real.exp |z| := by nlinarith

/-- `|log (1 + w) − w| ≤ w²` for `w ≥ 0`. -/
private lemma abs_log_one_add_sub_le (w : ℝ) (hw : 0 ≤ w) :
    |Real.log (1 + w) - w| ≤ w ^ 2 := by
  have hpos : (0 : ℝ) < 1 + w := by linarith
  have hup : Real.log (1 + w) ≤ w := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlow : w - w ^ 2 ≤ Real.log (1 + w) := by
    have h := Real.log_le_sub_one_of_pos (x := (1 + w)⁻¹) (by positivity)
    rw [Real.log_inv] at h
    have hne : (1 : ℝ) + w ≠ 0 := ne_of_gt hpos
    have hkey : 1 - (1 + w)⁻¹ = w / (1 + w) := by field_simp; ring
    have h3 : w - w ^ 2 ≤ 1 - (1 + w)⁻¹ := by
      rw [hkey, le_div_iff₀ hpos]
      nlinarith [pow_nonneg hw 3]
    linarith
  rw [abs_le]
  constructor <;> nlinarith

/-- `u³ ≤ 6 t⁻³ e^{t u}` for `u ≥ 0`, `t > 0`. -/
private lemma cube_le_exp (t : ℝ) (ht : 0 < t) (u : ℝ) (hu : 0 ≤ u) :
    u ^ 3 ≤ 6 / t ^ 3 * Real.exp (t * u) := by
  have h := Real.sum_le_exp_of_nonneg (x := t * u) (by positivity) 4
  have hsum : ∑ m ∈ Finset.range 4, (t * u) ^ m / (Nat.factorial m)
      = 1 + t * u + (t * u) ^ 2 / 2 + (t * u) ^ 3 / 6 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have htu : 0 ≤ t * u := by positivity
  have hcube : (t * u) ^ 3 / 6 ≤ Real.exp (t * u) := by nlinarith [sq_nonneg (t * u)]
  have ht3 : (0 : ℝ) < t ^ 3 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ ht3]
  nlinarith


/-! ### Envelope integrability from the natural parameter set -/

/-- **Sign-vector envelope.** If every exponential tilt `e^{⟪θ, ψ(x)⟫}` is `P₀`-integrable,
then so is `e^{t ∑ⱼ |ψⱼ(x)|}` for every `t ≥ 0`: the `ℓ¹` exponential is dominated by the
sum of the `2^k` sign tilts. -/
private lemma integrable_exp_l1 {k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} (hψmeas : ∀ j, Measurable (ψ j))
    (hint : ∀ θ : EuclideanSpace ℝ (Fin k),
      Integrable (fun x => Real.exp ⟪θ, psiVec ψ x⟫_ℝ) P₀)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => Real.exp (t * ∑ j, |ψ j x|)) P₀ := by
  classical
  set Θ : Finset (Fin k) → EuclideanSpace ℝ (Fin k) :=
    fun s => WithLp.toLp 2 (fun j => if j ∈ s then t else -t) with hΘ
  have hmeas : Measurable (fun x => Real.exp (t * ∑ j, |ψ j x|)) :=
    Real.continuous_exp.measurable.comp
      ((Finset.univ.measurable_sum fun j _ => (hψmeas j).abs).const_mul t)
  have hbound : ∀ x, Real.exp (t * ∑ j, |ψ j x|)
      ≤ ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, Real.exp ⟪Θ s, psiVec ψ x⟫_ℝ := by
    intro x
    have hprod : Real.exp (t * ∑ j, |ψ j x|) = ∏ j, Real.exp (t * |ψ j x|) := by
      rw [← Real.exp_sum, Finset.mul_sum]
    have hpt : ∀ j : Fin k,
        Real.exp (t * |ψ j x|) ≤ Real.exp (t * ψ j x) + Real.exp (-(t * ψ j x)) := by
      intro j
      rcases abs_cases (ψ j x) with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]
        nlinarith [Real.exp_pos (-(t * ψ j x)), le_refl (Real.exp (t * ψ j x))]
      · rw [h1, mul_neg, ← neg_mul]
        nlinarith [Real.exp_pos (t * ψ j x)]
    have hle : ∏ j, Real.exp (t * |ψ j x|)
        ≤ ∏ j, (Real.exp (t * ψ j x) + Real.exp (-(t * ψ j x))) :=
      Finset.prod_le_prod (fun j _ => (Real.exp_pos _).le) (fun j _ => hpt j)
    have hexpand : ∏ j, (Real.exp (t * ψ j x) + Real.exp (-(t * ψ j x)))
        = ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, Real.exp ⟪Θ s, psiVec ψ x⟫_ℝ := by
      rw [Finset.prod_add]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hsub : s ⊆ (Finset.univ : Finset (Fin k)) := Finset.subset_univ s
      have hL : (∏ j ∈ s, Real.exp (t * ψ j x))
          * ∏ j ∈ (Finset.univ : Finset (Fin k)) \ s, Real.exp (-(t * ψ j x))
          = Real.exp ((∑ j ∈ s, t * ψ j x)
              + ∑ j ∈ (Finset.univ : Finset (Fin k)) \ s, -(t * ψ j x)) := by
        rw [Real.exp_add, Real.exp_sum, Real.exp_sum]
      rw [hL]
      congr 1
      rw [inner_psiVec]
      rw [← Finset.sum_sdiff hsub]
      have h1 : ∑ j ∈ (Finset.univ : Finset (Fin k)) \ s, (Θ s) j * ψ j x
          = ∑ j ∈ (Finset.univ : Finset (Fin k)) \ s, -(t * ψ j x) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjs : j ∉ s := (Finset.mem_sdiff.mp hj).2
        show (if j ∈ s then t else -t) * ψ j x = -(t * ψ j x)
        rw [if_neg hjs]; ring
      have h2 : ∑ j ∈ s, (Θ s) j * ψ j x = ∑ j ∈ s, t * ψ j x := by
        refine Finset.sum_congr rfl fun j hj => ?_
        show (if j ∈ s then t else -t) * ψ j x = t * ψ j x
        rw [if_pos hj]
      rw [h1, h2, add_comm]
    calc Real.exp (t * ∑ j, |ψ j x|) = ∏ j, Real.exp (t * |ψ j x|) := hprod
      _ ≤ ∏ j, (Real.exp (t * ψ j x) + Real.exp (-(t * ψ j x))) := hle
      _ = _ := hexpand
  have hsumint : Integrable (fun x => ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset,
      Real.exp ⟪Θ s, psiVec ψ x⟫_ℝ) P₀ :=
    integrable_finset_sum (Finset.univ : Finset (Fin k)).powerset (fun s _ => hint (Θ s))
  refine Integrable.mono' hsumint hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact hbound x


/-! ### The quadratic expansion of the log-partition function -/

/-- `|θ j| ≤ ‖θ‖` in `EuclideanSpace`. -/
private lemma abs_coord_le_norm {k : ℕ} (θ : EuclideanSpace ℝ (Fin k)) (j : Fin k) :
    |θ j| ≤ ‖θ‖ := by
  have hle : (θ j) ^ 2 ≤ ‖θ‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (f := fun i => (θ i) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [sq_abs (θ j), abs_nonneg (θ j), norm_nonneg θ]

/-- Integrability facts for an orthonormal centred score system. -/
private lemma score_L2_facts {k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} (hψmeas : ∀ j, Measurable (ψ j))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0) :
    (∀ i, Integrable (ψ i) P₀) ∧ (∀ i j, Integrable (fun x => ψ i x * ψ j x) P₀) := by
  have hsqint : ∀ i, Integrable (fun x => ψ i x ^ 2) P₀ := by
    intro i
    have h1 : (∫ x, ψ i x * ψ i x ∂P₀) = 1 := by rw [hortho i i]; simp
    simpa [sq] using integrable_of_integral_eq_one h1
  have hψL2 : ∀ i, MemLp (ψ i) 2 P₀ := fun i =>
    (memLp_two_iff_integrable_sq (hψmeas i).aestronglyMeasurable).2 (hsqint i)
  exact ⟨fun i => (hψL2 i).integrable one_le_two,
    fun i j => by simpa using! (hψL2 i).integrable_mul (hψL2 j)⟩

/-- **Quadratic expansion of the log-partition function of the smooth model.**  For a centred
orthonormal score system whose exponential tilts are all integrable, the log-partition
function `A(θ) = log ∫ e^{⟪θ,ψ⟫} dP₀` satisfies `|A(θ) − ‖θ‖²/2| ≤ C‖θ‖³` on the ball of
radius `r`.  Purely elementary: a third-order Taylor bound on `e^z`, the moment identities
`∫⟪θ,ψ⟫ = 0` and `∫⟪θ,ψ⟫² = ‖θ‖²`, and `|log(1+w) − w| ≤ w²`. -/
private lemma logPartition_quadratic_bound {k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} (hψmeas : ∀ j, Measurable (ψ j))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    (hint : ∀ θ : EuclideanSpace ℝ (Fin k),
      Integrable (fun x => Real.exp ⟪θ, psiVec ψ x⟫_ℝ) P₀)
    {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ‖ ≤ r →
      |Real.log (∫ x, Real.exp ⟪θ, psiVec ψ x⟫_ℝ ∂P₀) - ‖θ‖ ^ 2 / 2| ≤ C * ‖θ‖ ^ 3 := by
  classical
  obtain ⟨hψint, hψψint⟩ := score_L2_facts hψmeas hortho
  set W : 𝓧 → ℝ := fun x => ∑ j, |ψ j x| with hW
  have hWnn : ∀ x, 0 ≤ W x := fun x => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hWmeas : Measurable W := Finset.univ.measurable_sum fun j _ => (hψmeas j).abs
  -- the cubic envelope `G` and its integral `K`
  set G : 𝓧 → ℝ := fun x => (W x) ^ 3 * Real.exp (r * W x) with hG
  have hGnn : ∀ x, 0 ≤ G x := fun x => by positivity
  have hGmeas : Measurable G :=
    (hWmeas.pow_const 3).mul (Real.continuous_exp.measurable.comp (hWmeas.const_mul r))
  have hGint : Integrable G P₀ := by
    have hdom : Integrable (fun x => 6 / r ^ 3 * Real.exp (2 * r * W x)) P₀ := by
      have h2 := integrable_exp_l1 (P₀ := P₀) hψmeas hint (t := 2 * r) (by positivity)
      exact h2.const_mul _
    refine hdom.mono' hGmeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (hGnn x)]
    have hcube := cube_le_exp r hr (W x) (hWnn x)
    have hexp : Real.exp (r * W x) * Real.exp (r * W x) = Real.exp (2 * r * W x) := by
      rw [← Real.exp_add]; ring_nf
    calc (W x) ^ 3 * Real.exp (r * W x)
        ≤ (6 / r ^ 3 * Real.exp (r * W x)) * Real.exp (r * W x) := by
          exact mul_le_mul_of_nonneg_right hcube (Real.exp_pos _).le
      _ = 6 / r ^ 3 * Real.exp (2 * r * W x) := by rw [mul_assoc, hexp]
  set K : ℝ := ∫ x, G x ∂P₀ with hK
  have hKnn : 0 ≤ K := integral_nonneg hGnn
  refine ⟨4 * K + r * (1 / 2 + 4 * K * r) ^ 2, by positivity, ?_⟩
  intro θ hθ
  have hθ0 : 0 ≤ ‖θ‖ := norm_nonneg θ
  set z : 𝓧 → ℝ := fun x => ⟪θ, psiVec ψ x⟫_ℝ with hz
  have hzval : ∀ x, z x = ∑ j, θ j * ψ j x := fun x => inner_psiVec ψ θ x
  have hzmeas : Measurable z := by
    have : z = fun x => ∑ j, θ j * ψ j x := funext hzval
    rw [this]
    exact Finset.univ.measurable_sum fun j _ => (hψmeas j).const_mul _
  have hzint : Integrable z P₀ := by
    have : z = fun x => ∑ j, θ j * ψ j x := funext hzval
    rw [this]
    exact integrable_finset_sum _ fun j _ => (hψint j).const_mul _
  have hzsqint : Integrable (fun x => z x ^ 2) P₀ := by
    have hpt : (fun x => z x ^ 2) = fun x => ∑ i, ∑ j, (θ i * θ j) * (ψ i x * ψ j x) := by
      funext x
      rw [hzval x, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hpt]
    exact integrable_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => (hψψint i j).const_mul _
  -- the two moment identities
  have hmom1 : ∫ x, z x ∂P₀ = 0 := by
    have : z = fun x => ∑ j, θ j * ψ j x := funext hzval
    rw [this, integral_finset_sum _ fun j _ => (hψint j).const_mul _]
    simp_rw [integral_const_mul, hcentred, mul_zero, Finset.sum_const_zero]
  have hmom2 : ∫ x, z x ^ 2 ∂P₀ = ‖θ‖ ^ 2 := by
    have hpt : (fun x => z x ^ 2) = fun x => ∑ i, ∑ j, (θ i * θ j) * (ψ i x * ψ j x) := by
      funext x
      rw [hzval x, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hpt, integral_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => (hψψint i j).const_mul _,
      EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => (hψψint i j).const_mul _]
    simp_rw [integral_const_mul, hortho i]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [if_neg (Ne.symm hji), mul_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [if_pos rfl, mul_one, sq]
  -- the pointwise third-order bound
  have hzbd : ∀ x, |z x| ≤ ‖θ‖ * W x := by
    intro x
    rw [hzval x]
    calc |∑ j, θ j * ψ j x| ≤ ∑ j, |θ j * ψ j x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ‖θ‖ * |ψ j x| := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_coord_le_norm θ j) (abs_nonneg _)
      _ = ‖θ‖ * W x := by rw [hW, Finset.mul_sum]
  have hptbd : ∀ x, |Real.exp (z x) - (1 + z x + (z x) ^ 2 / 2)| ≤ 4 * ‖θ‖ ^ 3 * G x := by
    intro x
    refine (abs_exp_sub_quadratic_le (z x)).trans ?_
    have h1 : |z x| ^ 3 ≤ ‖θ‖ ^ 3 * (W x) ^ 3 := by
      have := hzbd x
      have hpow : |z x| ^ 3 ≤ (‖θ‖ * W x) ^ 3 :=
        pow_le_pow_left₀ (abs_nonneg _) this 3
      calc |z x| ^ 3 ≤ (‖θ‖ * W x) ^ 3 := hpow
        _ = ‖θ‖ ^ 3 * (W x) ^ 3 := by ring
    have h2 : Real.exp |z x| ≤ Real.exp (r * W x) := by
      refine Real.exp_le_exp.mpr ((hzbd x).trans ?_)
      exact mul_le_mul_of_nonneg_right hθ (hWnn x)
    calc 4 * |z x| ^ 3 * Real.exp |z x|
        ≤ 4 * (‖θ‖ ^ 3 * (W x) ^ 3) * Real.exp (r * W x) := by
          have hc : (0 : ℝ) ≤ 4 * |z x| ^ 3 := by positivity
          have := mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
          nlinarith [Real.exp_pos (r * W x), pow_nonneg (abs_nonneg (z x)) 3]
      _ = 4 * ‖θ‖ ^ 3 * G x := by rw [hG]; ring
  -- the integral of the exponential
  set M : ℝ := ∫ x, Real.exp (z x) ∂P₀ with hM
  have hMint : Integrable (fun x => Real.exp (z x)) P₀ := hint θ
  have hquadint : Integrable (fun x => 1 + z x + (z x) ^ 2 / 2) P₀ :=
    ((integrable_const 1).add hzint).add (hzsqint.div_const 2)
  have hlinint : Integrable (fun x : 𝓧 => (1 : ℝ) + z x) P₀ := (integrable_const 1).add hzint
  have hquadval : ∫ x, (1 + z x + (z x) ^ 2 / 2) ∂P₀ = 1 + ‖θ‖ ^ 2 / 2 := by
    rw [show (∫ x, (1 + z x + (z x) ^ 2 / 2) ∂P₀)
          = (∫ x, ((1 : ℝ) + z x) ∂P₀) + ∫ x, (z x) ^ 2 / 2 ∂P₀ from
        integral_add hlinint (hzsqint.div_const 2),
      show (∫ x, ((1 : ℝ) + z x) ∂P₀) = (∫ _x : 𝓧, (1 : ℝ) ∂P₀) + ∫ x, z x ∂P₀ from
        integral_add (integrable_const 1) hzint,
      integral_div, hmom1, hmom2]
    simp
  have hMbd : |M - (1 + ‖θ‖ ^ 2 / 2)| ≤ 4 * ‖θ‖ ^ 3 * K := by
    have hdiff : M - (1 + ‖θ‖ ^ 2 / 2)
        = ∫ x, (Real.exp (z x) - (1 + z x + (z x) ^ 2 / 2)) ∂P₀ := by
      rw [integral_sub hMint hquadint, hquadval]
    rw [hdiff]
    refine (abs_integral_le_integral_abs).trans ?_
    have hb : ∫ x, |Real.exp (z x) - (1 + z x + (z x) ^ 2 / 2)| ∂P₀
        ≤ ∫ x, 4 * ‖θ‖ ^ 3 * G x ∂P₀ := by
      refine integral_mono ((hMint.sub hquadint).abs) (hGint.const_mul _) ?_
      intro x; exact hptbd x
    rw [integral_const_mul] at hb
    calc _ ≤ 4 * ‖θ‖ ^ 3 * K := hb
      _ = 4 * ‖θ‖ ^ 3 * K := rfl
  -- `M ≥ 1`
  have hM1 : 1 ≤ M := by
    have hmono : ∫ x, ((1 : ℝ) + z x) ∂P₀ ≤ M := by
      refine integral_mono hlinint hMint fun x => ?_
      have := Real.add_one_le_exp (z x)
      linarith
    rw [show (∫ x, ((1 : ℝ) + z x) ∂P₀) = (∫ _x : 𝓧, (1 : ℝ) ∂P₀) + ∫ x, z x ∂P₀ from
      integral_add (integrable_const 1) hzint, hmom1] at hmono
    simpa using hmono
  set w : ℝ := M - 1 with hw
  have hwnn : 0 ≤ w := by simp [hw]; linarith
  have hwbd : |w - ‖θ‖ ^ 2 / 2| ≤ 4 * K * ‖θ‖ ^ 3 := by
    have : w - ‖θ‖ ^ 2 / 2 = M - (1 + ‖θ‖ ^ 2 / 2) := by rw [hw]; ring
    rw [this]
    calc |M - (1 + ‖θ‖ ^ 2 / 2)| ≤ 4 * ‖θ‖ ^ 3 * K := hMbd
      _ = 4 * K * ‖θ‖ ^ 3 := by ring
  have hlog : |Real.log M - ‖θ‖ ^ 2 / 2| ≤ w ^ 2 + 4 * K * ‖θ‖ ^ 3 := by
    have hMw : M = 1 + w := by rw [hw]; ring
    have h1 := abs_log_one_add_sub_le w hwnn
    rw [hMw]
    calc |Real.log (1 + w) - ‖θ‖ ^ 2 / 2|
        ≤ |Real.log (1 + w) - w| + |w - ‖θ‖ ^ 2 / 2| := by
          have hsum : (Real.log (1 + w) - w) + (w - ‖θ‖ ^ 2 / 2)
              = Real.log (1 + w) - ‖θ‖ ^ 2 / 2 := by ring
          rw [← hsum]
          exact abs_add_le _ _
      _ ≤ w ^ 2 + 4 * K * ‖θ‖ ^ 3 := add_le_add h1 hwbd
  have hwle : w ≤ (1 / 2 + 4 * K * r) * ‖θ‖ ^ 2 := by
    have h1 : w ≤ ‖θ‖ ^ 2 / 2 + 4 * K * ‖θ‖ ^ 3 := by
      have := (abs_le.mp hwbd).2; linarith
    have h2 : 4 * K * ‖θ‖ ^ 3 ≤ 4 * K * r * ‖θ‖ ^ 2 := by
      have : ‖θ‖ ^ 3 = ‖θ‖ ^ 2 * ‖θ‖ := by ring
      rw [this]
      have hkk : (0 : ℝ) ≤ 4 * K * ‖θ‖ ^ 2 := by positivity
      nlinarith [sq_nonneg ‖θ‖]
    linarith
  have hwsq : w ^ 2 ≤ r * (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 := by
    have hc : (0 : ℝ) ≤ 1 / 2 + 4 * K * r := by positivity
    have h1 : w ^ 2 ≤ ((1 / 2 + 4 * K * r) * ‖θ‖ ^ 2) ^ 2 :=
      pow_le_pow_left₀ hwnn hwle 2
    have h2 : ((1 / 2 + 4 * K * r) * ‖θ‖ ^ 2) ^ 2
        = (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * ‖θ‖ := by ring
    have h3 : (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * ‖θ‖
        ≤ (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * r := by
      have hnn : (0 : ℝ) ≤ (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 := by positivity
      exact mul_le_mul_of_nonneg_left hθ hnn
    calc w ^ 2 ≤ ((1 / 2 + 4 * K * r) * ‖θ‖ ^ 2) ^ 2 := h1
      _ = (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * ‖θ‖ := h2
      _ ≤ (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * r := h3
      _ = r * (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 := by ring
  calc |Real.log M - ‖θ‖ ^ 2 / 2| ≤ w ^ 2 + 4 * K * ‖θ‖ ^ 3 := hlog
    _ ≤ r * (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 + 4 * K * ‖θ‖ ^ 3 := by linarith
    _ = (4 * K + r * (1 / 2 + 4 * K * r) ^ 2) * ‖θ‖ ^ 3 := by ring


/-! ### The canonical experiment -/

/-- `N(0, Iₖ)` is the standard Gaussian of `EuclideanSpace`. -/
private lemma mvGaussian_zero_one_eq_stdGaussian {k : ℕ} :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (1 : Matrix (Fin k) (Fin k) ℝ)
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := by
  rw [multivariateGaussian]
  simp only [CFC.sqrt_one, map_one, ContinuousLinearMap.one_apply, zero_add]
  exact Measure.map_id

/-- The stage-`n` law of the score vector is the standardised product law. -/
private lemma law_scoreVec_pi {n k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin n → Ω → 𝓧}
    (hψmeas : ∀ j, Measurable (ψ j)) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = P₀) :
    P.map (scoreVec ψ X)
      = (Measure.pi fun _ : Fin n => P₀).map
          (fun d => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i)) := by
  classical
  have hgmeas : Measurable (psiVec ψ) :=
    (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp (measurable_pi_lambda _ hψmeas)
  set F : (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k) :=
    fun d => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i) with hF
  have hFmeas : Measurable F :=
    measurable_const.fun_smul
      (Finset.univ.measurable_sum fun i _ => hgmeas.comp (measurable_pi_apply i))
  have hXmeas : Measurable (fun ω (i : Fin n) => X i ω) := measurable_pi_lambda _ hX
  have hpiX : P.map (fun ω (i : Fin n) => X i ω) = Measure.pi (fun _ : Fin n => P₀) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).1 hindep]
    congr 1; funext i; exact hlaw i
  have hcomp : scoreVec ψ X = F ∘ (fun ω (i : Fin n) => X i ω) := by
    funext ω
    rw [scoreVec_eq_smul_sum ψ X ω]
    rfl
  rw [hcomp, ← Measure.map_map hFmeas hXmeas, hpiX]

/-- **The canonical score law converges to the standard Gaussian.** -/
lemma pi_scoreLaw_weakConverges {k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} (hψmeas : ∀ j, Measurable (ψ j))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0) :
    WeakConverges (fun n => (Measure.pi fun _ : Fin n => P₀).map
        (fun d => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i)))
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  classical
  obtain ⟨Ω₀, mΩ₀, P₀c, Z, hZmeas, hZlaw, hZindep, hP₀cprob⟩ :=
    ProbabilityTheory.exists_iid ℕ P₀
  letI : MeasurableSpace Ω₀ := mΩ₀
  haveI : IsProbabilityMeasure P₀c := hP₀cprob
  have hbrick := scoreVec_weakConverges_gaussian (P₀ := P₀) (ψ := ψ)
    (P := fun _ : ℕ => P₀c) (X := fun n (i : Fin n) ω => Z (i : ℕ) ω)
    hψmeas hortho hcentred
    (fun n i => hZmeas i) (fun n => hZindep.precomp Fin.val_injective)
    (fun n i => (hZlaw (i : ℕ)).map_eq)
  have heq : ∀ n : ℕ, P₀c.map (scoreVec ψ (fun (i : Fin n) ω => Z (i : ℕ) ω))
      = (Measure.pi fun _ : Fin n => P₀).map
          (fun d => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i)) :=
    fun n => law_scoreVec_pi hψmeas (fun i => hZmeas i)
      (hZindep.precomp Fin.val_injective) (fun i => (hZlaw (i : ℕ)).map_eq)
  simp only [heq] at hbrick
  rwa [mvGaussian_zero_one_eq_stdGaussian] at hbrick


/-! ### The smooth model as an explicit exponential tilt -/

private lemma smoothModel_base {k : ℕ} (P₀ : Measure 𝓧) (ψ : Fin k → 𝓧 → ℝ)
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k))) :
    (smoothModel P₀ ψ hψ).base = P₀ := by
  show P₀.withDensity (fun _ => 1) = P₀
  simp

private lemma smoothModel_P_eq {k : ℕ} (P₀ : Measure 𝓧) (ψ : Fin k → 𝓧 → ℝ)
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k)))
    (θ : EuclideanSpace ℝ (Fin k)) :
    (smoothModel P₀ ψ hψ).P θ = P₀.tilted (fun x => ⟪θ, psiVec ψ x⟫_ℝ) := by
  have h : (smoothModel P₀ ψ hψ).P θ
      = ((smoothModel P₀ ψ hψ).base).tilted (fun x => ⟪θ, psiVec ψ x⟫_ℝ) := rfl
  rw [h, smoothModel_base]

/-- A tilt that is a probability measure has an integrable exponential. -/
private lemma integrable_exp_of_isProbabilityMeasure_tilted {P₀ : Measure 𝓧} {f : 𝓧 → ℝ}
    (h : IsProbabilityMeasure (P₀.tilted f)) :
    Integrable (fun x => Real.exp (f x)) P₀ := by
  by_contra hcon
  rw [tilted_of_not_integrable hcon] at h
  have h1 : (0 : Measure 𝓧) Set.univ = 1 := h.measure_univ
  simp only [Measure.coe_zero, Pi.zero_apply] at h1
  exact zero_ne_one h1

/-- The tilt written with the log-partition normalisation. -/
private lemma tilted_eq_withDensity_log (μ : Measure 𝓧) (f : 𝓧 → ℝ)
    (hpos : 0 < ∫ x, Real.exp (f x) ∂μ) :
    μ.tilted f = μ.withDensity (fun x =>
      ENNReal.ofReal (Real.exp (f x - Real.log (∫ y, Real.exp (f y) ∂μ)))) := by
  rw [Measure.tilted]
  congr 1
  funext x
  rw [Real.exp_sub, Real.exp_log hpos]

/-- The `n`-fold product of an exponential tilt is the tilt of the product by the sum. -/
lemma pi_withDensity_exp {n : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {u : 𝓧 → ℝ} (hu : Measurable u)
    [hprob : IsProbabilityMeasure
      (P₀.withDensity (fun x => ENNReal.ofReal (Real.exp (u x))))] :
    Measure.pi (fun _ : Fin n => P₀.withDensity (fun x => ENNReal.ofReal (Real.exp (u x))))
      = (Measure.pi fun _ : Fin n => P₀).withDensity
          (fun d => ENNReal.ofReal (Real.exp (∑ i, u (d i)))) := by
  classical
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (u x))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp hu)
  have hprod : (fun d : Fin n → 𝓧 => ENNReal.ofReal (Real.exp (∑ i, u (d i))))
      = fun d => ∏ i, ENNReal.ofReal (Real.exp (u (d i))) := by
    funext d
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _)]
  rw [hprod, pi_withDensity_prod (μ := fun _ : Fin n => P₀)
    (f := fun _ : Fin n => fun x => ENNReal.ofReal (Real.exp (u x))) (fun _ => hmeas)]

/-! ### Asymptotic maximin optimality over the `O(n^{-1/2})` sphere -/

/-- **No test beats the chi-squared value on the local shell.** For any test sequence whose
power at `θ = 0` tends to `α`, and any radii `0 < b < B < ∞`, the limiting minimum power
over the local alternatives `θ = h n^{-1/2}` with `b ≤ |h| ≤ B` is at most
`P{χ²_k(b²) > c_{k,1−α}}`.

The instance of `asymptotic_maximin_upper_bound` in which the information matrix is the
identity — see the module docstring. The statement remains true, a fortiori, with the
outer radius removed. -/
theorem smoothTest_maximin_upper_bound {k : ℕ} {α b B c : ℝ} {P₀ : Measure 𝓧}
    [IsProbabilityMeasure P₀] {ψ : Fin k → 𝓧 → ℝ}
    {Q : ℕ → EuclideanSpace ℝ (Fin k) → Measure Ω} [∀ n h, IsProbabilityMeasure (Q n h)]
    {X : (n : ℕ) → Fin n → Ω → 𝓧} {φ : ℕ → Ω → ℝ}
    -- USER-INPUT: at least one score direction
    (hk : 0 < k)
    -- USER-INPUT: the shell is nondegenerate
    (hb : 0 < b) (hbB : b < B)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c` is the `1 − α` quantile of `χ²_k`, i.e. the critical value
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    -- USER-INPUT: the vector of score functions is measurable; this is the certificate
    -- the exponential-family structure carries, and it implies measurability of each `ψⱼ`
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k)))
    -- USER-INPUT: the score functions are orthonormal in `L²(P₀)`; Neyman 1937
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    -- USER-INPUT: the score functions are orthogonal to the constants, i.e. `E₀ψⱼ = 0`
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    -- USER-INPUT: the null parameter is interior to the natural parameter set (full rank)
    (hint : (0 : EuclideanSpace ℝ (Fin k)) ∈ interior (smoothModel P₀ ψ hψ).natSet)
    -- USER-INPUT: at every stage and every local parameter each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: under every local parameter the observations are i.i.d.
    (hindep : ∀ n h, iIndepFun (X n) (Q n h))
    -- USER-INPUT: under the local parameter `h` the observations have law
    -- `p_{h n^{-1/2}}`, the smooth model at the local alternative
    (hlaw : ∀ n h, ∀ i, (Q n h).map (X n i)
      = (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h))
    -- USER-INPUT: the competitors are randomized tests
    (hφ : ∀ n, IsCriticalFn (φ n))
    -- REPAIRED HYPOTHESIS (the frozen statement without it is FALSE — counterexample in the
    -- proof note below): the competitors are tests *based on the sample*, i.e. each `φ n` is
    -- a measurable function of `(X n 1, …, X n n)`.  `Q` is abstract data, and nothing in the
    -- remaining hypotheses prevents `Q n h` from encoding `h` in a part of `Ω` that the
    -- observations do not see
    (hφX : ∀ n, ∃ ρ : (Fin n → 𝓧) → ℝ,
      Measurable ρ ∧ ∀ ω, φ n ω = ρ (fun i => X n i ω))
    -- USER-INPUT: the competitors are asymptotically of level `α` at the null
    (hlevel : Tendsto (fun n => power (Q n) (φ n) 0) atTop (nhds α)) :
    limsup (fun n => sInf ((fun h => power (Q n) (φ n) h) ''
        {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖ ∧ ‖h‖ ≤ B})) atTop
      ≤ ((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal := by
  -- CLOSED this batch (the STATEMENT WAS FALSE AS FROZEN — repaired by `hφX` above).
  --
  -- COUNTEREXAMPLE to the frozen statement (no `hφX`).  Take `Ω = (ℕ → 𝓧) × ℝ`,
  -- `X n i ω = ω.1 i`, and `Q n h = (i.i.d. sample from `p_{h n^{-1/2}}`) ⊗ δ_{‖h‖}`.  All the
  -- frozen hypotheses hold (measurability, independence and the prescribed marginal laws
  -- concern only `ω.1`).  Take `φ n ω = if ω.2 = 0 then α else 1`; it is a critical function
  -- with `power (Q n) (φ n) 0 = α` for every `n`, so `hlevel` holds.  Every `h` in the shell
  -- `{b ≤ ‖h‖ ≤ B}` has `‖h‖ ≥ b > 0`, hence `power (Q n) (φ n) h = 1` there, so the left-hand
  -- side is `1`, while the right-hand side `ncχ²_k(b²)(c,∞)` is `< 1`.  Domination
  -- `Q n h ≪ Q n 0` does not repair it either (replace `δ_{‖h‖}` by `Unif[0, δₙ]` versus
  -- `Unif[0,1]`, `δₙ → 0`); what is missing is not absolute continuity but any
  -- local-asymptotic-normality link between `Q n h` and the sample.  The minimal repair is to
  -- restrict the competitors to tests based on the sample, which is `hφX` and is how the
  -- source states the theorem (Neyman 1937; TSH4 §16.4.1).
  --
  -- PROOF.  Transfer along `hφX` to the CANONICAL experiment `QC n h = ⨂_{i<n} p_{h n^{-1/2}}`
  -- on `Fin n → 𝓧` (the varying sample space that `asymptotic_maximin_upper_bound` now allows),
  -- where `hindep` + `hlaw` identify the law of the sample and hence the power function; the
  -- competitor is the `[0,1]`-truncation of the function of the sample supplied by `hφX`, which
  -- agrees with `φ n` on the sample because `φ n` is a critical function.  On the canonical
  -- experiment every ingredient is explicit:
  -- • `hlaw` at `n = 1` forces every member `p_θ` to be a probability measure, so every
  --   exponential tilt is `P₀`-integrable and the natural parameter set is the whole space —
  --   `hint` is therefore not needed, and is kept only because it is part of the frozen
  --   signature;
  -- • the log-likelihood field is `L n h d = ∑_{i<n} (⟪n^{-1/2}h, ψ(dᵢ)⟫ − A(n^{-1/2}h))`,
  --   jointly measurable because `A` is measurable by Fubini;
  -- • `Zₙ ⇒ N(0, Iₖ)` is `scoreVec_weakConverges_gaussian` transported to the product law;
  -- • the LAN remainder is DETERMINISTIC, `n A(n^{-1/2}h) − b²/2`, the family being linear in
  --   the sufficient statistic, so the envelope `D n` is the constant `C b³/√n`; the estimate
  --   `|A(θ) − ‖θ‖²/2| ≤ C‖θ‖³` on the ball of radius `b` is `logPartition_quadratic_bound`,
  --   proved above by an elementary third-order Taylor bound on `e^z` together with the moment
  --   identities `∫⟪θ,ψ⟫ dP₀ = 0` and `∫⟪θ,ψ⟫² dP₀ = ‖θ‖²` supplied by `hcentred`/`hortho`.
  -- The bounded shell `{b ≤ ‖h‖ ≤ B}` contains the least-favourable sphere `‖h‖ = b` (here
  -- `b < B`), which is what the shell-parametrised form of the transfer lemma requires.
  classical
  have hψmeas : ∀ j, Measurable (ψ j) := fun j =>
    ((measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 (Fin k → ℝ))).comp hψ
  have hgmeas : Measurable (psiVec ψ) :=
    (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp (measurable_pi_lambda _ hψmeas)
  -- ### The log-partition function
  set A : EuclideanSpace ℝ (Fin k) → ℝ :=
    fun θ => Real.log (∫ x, Real.exp ⟪θ, psiVec ψ x⟫_ℝ ∂P₀) with hAdef
  -- every member of the smooth family is a probability measure, hence every tilt is
  -- integrable: the natural parameter set is all of the space
  have hEprob : ∀ θ : EuclideanSpace ℝ (Fin k),
      IsProbabilityMeasure ((smoothModel P₀ ψ hψ).P θ) := by
    intro θ
    have h1 := hlaw 1 θ (0 : Fin 1)
    have hs : (Real.sqrt ((1 : ℕ) : ℝ))⁻¹ • θ = θ := by
      norm_num
    rw [hs] at h1
    rw [← h1]
    exact Measure.isProbabilityMeasure_map (hX 1 (0 : Fin 1)).aemeasurable
  haveI hEprobI : ∀ θ, IsProbabilityMeasure ((smoothModel P₀ ψ hψ).P θ) := hEprob
  have hEint : ∀ θ, Integrable (fun x => Real.exp ⟪θ, psiVec ψ x⟫_ℝ) P₀ := by
    intro θ
    refine integrable_exp_of_isProbabilityMeasure_tilted (P₀ := P₀) ?_
    rw [← smoothModel_P_eq P₀ ψ hψ θ]
    exact hEprob θ
  have hMpos : ∀ θ, 0 < ∫ x, Real.exp ⟪θ, psiVec ψ x⟫_ℝ ∂P₀ :=
    fun θ => integral_exp_pos (hEint θ)
  -- the explicit density of each member with respect to `P₀`
  have hEdens : ∀ θ, (smoothModel P₀ ψ hψ).P θ
      = P₀.withDensity (fun x => ENNReal.ofReal (Real.exp (⟪θ, psiVec ψ x⟫_ℝ - A θ))) := by
    intro θ
    rw [smoothModel_P_eq P₀ ψ hψ θ]
    exact tilted_eq_withDensity_log P₀ _ (hMpos θ)
  have hEP0 : (smoothModel P₀ ψ hψ).P 0 = P₀ := by
    rw [smoothModel_P_eq]
    have hz : (fun x => ⟪(0 : EuclideanSpace ℝ (Fin k)), psiVec ψ x⟫_ℝ) = fun _ => (0 : ℝ) := by
      funext x; simp
    rw [hz, tilted_const]
  -- measurability of the log-partition function
  have hAmeas : Measurable A := by
    have hjoint : Measurable
        (fun p : EuclideanSpace ℝ (Fin k) × 𝓧 => Real.exp ⟪p.1, psiVec ψ p.2⟫_ℝ) := by
      refine Real.continuous_exp.measurable.comp ?_
      exact (continuous_inner.measurable).comp
        (measurable_fst.prodMk (hgmeas.comp measurable_snd))
    have := (hjoint.stronglyMeasurable).integral_prod_right' (ν := P₀)
    exact Real.measurable_log.comp this.measurable
  -- ### The quadratic expansion, on the ball of radius `b`
  obtain ⟨Cst, hCst0, hCstbd⟩ :=
    logPartition_quadratic_bound (P₀ := P₀) hψmeas hortho hcentred hEint hb
  -- ### The canonical experiment
  choose ρ0 hρ0meas hρ0val using hφX
  set ρ : (n : ℕ) → (Fin n → 𝓧) → ℝ := fun n d => min 1 (max 0 (ρ0 n d)) with hρdef
  have hρmeas : ∀ n, Measurable (ρ n) := fun n =>
    measurable_const.min (measurable_const.max (hρ0meas n))
  have hρcrit : ∀ n, IsCriticalFn (ρ n) := by
    intro n
    refine ⟨hρmeas n, fun d => ⟨?_, ?_⟩⟩
    · exact le_min zero_le_one (le_max_left _ _)
    · exact min_le_left _ _
  have hρval : ∀ n ω, φ n ω = ρ n (fun i => X n i ω) := by
    intro n ω
    obtain ⟨h0, h1⟩ := (hφ n).2 ω
    rw [hρdef]
    simp only
    rw [← hρ0val n ω, max_eq_right h0, min_eq_right h1]
  set QC : (n : ℕ) → EuclideanSpace ℝ (Fin k) → Measure (Fin n → 𝓧) :=
    fun n h => Measure.pi (fun _ : Fin n =>
      (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h)) with hQCdef
  haveI : ∀ n h, IsProbabilityMeasure (QC n h) := by
    intro n h
    rw [hQCdef]
    infer_instance
  have hQC0 : ∀ n : ℕ, QC n 0 = Measure.pi (fun _ : Fin n => P₀) := by
    intro n
    rw [hQCdef]
    simp only [smul_zero, hEP0]
  -- the sample map transports the power function
  have hsample : ∀ n h, (Q n h).map (fun ω (i : Fin n) => X n i ω) = QC n h := by
    intro n h
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX n i).aemeasurable)).1 (hindep n h),
      hQCdef]
    congr 1
    funext i
    exact hlaw n h i
  have hpower : ∀ n h, power (Q n) (φ n) h = power (QC n) (ρ n) h := by
    intro n h
    simp only [power]
    rw [show (∫ ω, φ n ω ∂(Q n h)) = ∫ ω, ρ n (fun i => X n i ω) ∂(Q n h) from
      integral_congr_ae (Filter.Eventually.of_forall (fun ω => hρval n ω))]
    rw [← hsample n h,
      integral_map (measurable_pi_lambda _ (fun i => hX n i)).aemeasurable
        (hρmeas n).aestronglyMeasurable]
  have hQCval : ∀ n h, QC n h = Measure.pi (fun _ : Fin n =>
      (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h)) := fun n h => rfl
  -- ### The centring statistics and the log-likelihood field
  set ZC : (n : ℕ) → (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k) :=
    fun n d => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i) with hZCdef
  have hZCval : ∀ n (d : Fin n → 𝓧),
      ZC n d = (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i) := fun n d => rfl
  have hZCmeas : ∀ n, Measurable (ZC n) := fun n =>
    measurable_const.fun_smul (Finset.univ.measurable_sum
      fun i _ => hgmeas.comp (measurable_pi_apply i))
  have hZ : WeakConverges (fun n => (QC n 0).map (ZC n))
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    have hbrick := pi_scoreLaw_weakConverges (P₀ := P₀) hψmeas hortho hcentred
    have heq : ∀ n : ℕ, (QC n 0).map (ZC n)
        = (Measure.pi fun _ : Fin n => P₀).map
            (fun d => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i)) := by
      intro n; rw [hQC0 n]
    simp only [heq]
    exact hbrick
  set LC : (n : ℕ) → EuclideanSpace ℝ (Fin k) → (Fin n → 𝓧) → ℝ :=
    fun n h d => ∑ i, (⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ (d i)⟫_ℝ
      - A ((Real.sqrt (n : ℝ))⁻¹ • h)) with hLCdef
  have hLCval : ∀ n h (d : Fin n → 𝓧), LC n h d
      = ∑ i, (⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ (d i)⟫_ℝ
        - A ((Real.sqrt (n : ℝ))⁻¹ • h)) := fun n h d => rfl
  have hsmulmeas : ∀ n : ℕ, Measurable
      (fun h : EuclideanSpace ℝ (Fin k) => (Real.sqrt (n : ℝ))⁻¹ • h) :=
    fun n => (continuous_const_smul ((Real.sqrt (n : ℝ))⁻¹)).measurable
  have hLCmeas : ∀ n, Measurable
      fun p : EuclideanSpace ℝ (Fin k) × (Fin n → 𝓧) => LC n p.1 p.2 := by
    intro n
    simp only [hLCval]
    refine Finset.univ.measurable_sum fun i _ => Measurable.sub ?_ ?_
    · exact continuous_inner.measurable.comp
        (((hsmulmeas n).comp measurable_fst).prodMk
          (hgmeas.comp ((measurable_pi_apply i).comp measurable_snd)))
    · exact (hAmeas.comp (hsmulmeas n)).comp measurable_fst
  -- ### The (deterministic) LAN envelope
  set DC : (n : ℕ) → (Fin n → 𝓧) → ℝ :=
    fun n _ => if n = 0 then b ^ 2 else Cst * b ^ 3 / Real.sqrt (n : ℝ) with hDCdef
  have hDCval : ∀ n (d : Fin n → 𝓧),
      DC n d = if n = 0 then b ^ 2 else Cst * b ^ 3 / Real.sqrt (n : ℝ) := fun n d => rfl
  have hLAN : ∀ n h (d : Fin n → 𝓧), ‖h‖ = b →
      |LC n h d - (⟪h, ZC n d⟫_ℝ - b ^ 2 / 2)| ≤ DC n d := by
    intro n h d hh
    have hinner : ⟪h, ZC n d⟫_ℝ
        = ∑ i, ⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ (d i)⟫_ℝ := by
      rw [hZCval n d, real_inner_smul_right, inner_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => (real_inner_smul_left _ _ _).symm
    have hL : LC n h d
        = (∑ i, ⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ (d i)⟫_ℝ)
          - (n : ℝ) * A ((Real.sqrt (n : ℝ))⁻¹ • h) := by
      rw [hLCval n h d, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hL, hinner, hDCval n d]
    have hgoal : (∑ i, ⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ (d i)⟫_ℝ)
          - (n : ℝ) * A ((Real.sqrt (n : ℝ))⁻¹ • h)
          - ((∑ i, ⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ (d i)⟫_ℝ) - b ^ 2 / 2)
        = -((n : ℝ) * A ((Real.sqrt (n : ℝ))⁻¹ • h) - b ^ 2 / 2) := by ring
    rw [hgoal, abs_neg]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, zero_mul, zero_sub, abs_neg, if_true]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ b ^ 2 / 2)]
      nlinarith [sq_nonneg b]
    · rw [if_neg hn.ne']
      have hCstbd' : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ‖ ≤ b →
          |A θ - ‖θ‖ ^ 2 / 2| ≤ Cst * ‖θ‖ ^ 3 := hCstbd
      set t : ℝ := Real.sqrt (n : ℝ) with htdef
      have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have htpos : 0 < t := by rw [htdef]; exact Real.sqrt_pos.mpr hnn
      have ht2 : t ^ 2 = (n : ℝ) := by rw [htdef]; exact Real.sq_sqrt hnn.le
      have ht1 : (1 : ℝ) ≤ t := by
        rw [htdef, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
      have hnorm : ‖t⁻¹ • h‖ = t⁻¹ * b := by
        rw [norm_smul, hh, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hinvle : t⁻¹ ≤ 1 := by
        rw [inv_le_one₀ htpos]; exact ht1
      have hle : t⁻¹ * b ≤ b := by nlinarith
      have h1 := hCstbd' (t⁻¹ • h) (by rw [hnorm]; exact hle)
      rw [hnorm] at h1
      have hq : (n : ℝ) * ((t⁻¹ * b) ^ 2 / 2) = b ^ 2 / 2 := by
        rw [← ht2]; field_simp
      calc |(n : ℝ) * A (t⁻¹ • h) - b ^ 2 / 2|
          = (n : ℝ) * |A (t⁻¹ • h) - (t⁻¹ * b) ^ 2 / 2| := by
            rw [← hq, ← mul_sub, abs_mul, abs_of_nonneg hnn.le]
        _ ≤ (n : ℝ) * (Cst * (t⁻¹ * b) ^ 3) := mul_le_mul_of_nonneg_left h1 hnn.le
        _ = Cst * b ^ 3 / t := by rw [← ht2]; field_simp
  -- ### The envelope is `o_P(1)`
  have hD0 : ∀ ε > 0, Tendsto (fun n => ((QC n 0) {d | ε ≤ DC n d}).toReal) atTop (nhds 0) := by
    intro ε hε
    have htend : Tendsto (fun n : ℕ => Cst * b ^ 3 / Real.sqrt (n : ℝ)) atTop (nhds 0) := by
      refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
      exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hsmall : ∀ᶠ n : ℕ in atTop, Cst * b ^ 3 / Real.sqrt (n : ℝ) < ε :=
      htend.eventually (gt_mem_nhds hε)
    have hev : ∀ᶠ n : ℕ in atTop, ((QC n 0) {d | ε ≤ DC n d}).toReal = 0 := by
      filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hn0
      have hset : {d : Fin n → 𝓧 | ε ≤ DC n d} = (∅ : Set (Fin n → 𝓧)) := by
        ext d
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le, hDCval,
          if_neg hn0.ne']
        exact hn
      rw [hset]
      simp
    have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
    refine Filter.Tendsto.congr' ?_ hconst
    filter_upwards [hev] with n hn
    exact hn.symm
  -- ### The likelihood-ratio representation
  have hdens : ∀ n h, QC n h
      = (QC n 0).withDensity (fun d => ENNReal.ofReal (Real.exp (LC n h d))) := by
    intro n h
    simp only [hLCval]
    rw [hQCval n h, hQC0 n]
    have hu : Measurable (fun x => ⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ x⟫_ℝ
        - A ((Real.sqrt (n : ℝ))⁻¹ • h)) :=
      ((continuous_const.inner continuous_id).measurable.comp hgmeas).sub measurable_const
    haveI hpm : IsProbabilityMeasure (P₀.withDensity (fun x => ENNReal.ofReal
        (Real.exp (⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ x⟫_ℝ
          - A ((Real.sqrt (n : ℝ))⁻¹ • h))))) := by
      rw [← hEdens ((Real.sqrt (n : ℝ))⁻¹ • h)]
      exact hEprob _
    rw [show (fun _ : Fin n => (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h))
        = (fun _ : Fin n => P₀.withDensity (fun x => ENNReal.ofReal
            (Real.exp (⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ x⟫_ℝ
              - A ((Real.sqrt (n : ℝ))⁻¹ • h))))) from funext fun _ => hEdens _,
      pi_withDensity_exp (n := n) (P₀ := P₀) hu]
  -- ### Assembly
  have hlevel' : Tendsto (fun n => power (QC n) (ρ n) 0) atTop (nhds α) :=
    hlevel.congr fun n => hpower n 0
  have hS : ∀ᶠ n : ℕ in atTop, {h : EuclideanSpace ℝ (Fin k) | ‖h‖ = b} ⊆
      {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖ ∧ ‖h‖ ≤ B} :=
    Filter.Eventually.of_forall fun _ h hh => ⟨le_of_eq hh.symm, by rw [hh]; exact hbB.le⟩
  have hmain := asymptotic_maximin_upper_bound (Ω := fun n => (Fin n → 𝓧)) (Q := QC)
    (φ := ρ) (Z := ZC) (L := LC) (D := DC)
    (S := fun _ : ℕ => {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖ ∧ ‖h‖ ≤ B})
    hk hb hα hα1 hc hρcrit hlevel' hZCmeas hZ hLCmeas hdens hLAN hD0 hS
  have hfun : ∀ n, (fun h => power (Q n) (φ n) h) = fun h => power (QC n) (ρ n) h :=
    fun n => funext (hpower n)
  simp only [hfun]
  exact hmain
/-! ### Bricks for the attainment half

The attainment half needs the local limit law of the score vector under a *drifting* local
parameter `hₙ → h₀`.  That is Le Cam's third lemma applied to the exponential tilt: the
log-likelihood ratio of the `n`-fold product `p_{hₙ/√n}` against `P₀ⁿ` is the *exact* affine
function `⟪hₙ, Zₙ⟫ − n·A(hₙ/√n)` of the score vector `Zₙ`, so the joint weak limit of
`(Zₙ, Lₙ)` under the null follows from `pi_scoreLaw_weakConverges` plus a Slutsky step, and
the uniform-integrability hypothesis of Le Cam 3 follows from the exact second-moment
identity `∫ exp(2Lₙ) dP₀ⁿ = exp(n·A(2hₙ/√n) − 2n·A(hₙ/√n))`, bounded because
`n·A(θₙ) → ‖h₀‖²/2` by `logPartition_quadratic_bound`.  The tilted limit is then the
Cameron–Martin shift `N(h₀, Iₖ)`. -/

section Attainment

variable {k : ℕ}

/-- **1-D Gaussian Girsanov shift**, measure form. -/
private lemma gaussianReal_withDensity_shift (a : ℝ) :
    (gaussianReal 0 1).withDensity
        (fun x => ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2)))
      = gaussianReal a 1 := by
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0),
    gaussianReal_of_var_ne_zero a (by norm_num : (1 : NNReal) ≠ 0),
    ← MeasureTheory.withDensity_mul volume (measurable_gaussianPDF 0 1) (by fun_prop)]
  congr 1
  ext x
  simp only [Pi.mul_apply, gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Product-form Gaussian Girsanov shift** on `ι → ℝ`. -/
private lemma pi_gaussianReal_withDensity_shift {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).withDensity
        (fun y => ENNReal.ofReal (Real.exp ((∑ i, a i * y i) - (∑ i, (a i) ^ 2) / 2)))
      = Measure.pi (fun i : ι => gaussianReal (a i) 1) := by
  classical
  have h1d : ∀ i, (gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a i * x - (a i) ^ 2 / 2)))
        = gaussianReal (a i) 1 :=
    fun i => gaussianReal_withDensity_shift (a i)
  haveI : ∀ i : ι, IsProbabilityMeasure ((gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a i * x - (a i) ^ 2 / 2)))) := by
    intro i; rw [h1d i]; infer_instance
  have hdensity : (fun y : ι → ℝ =>
        ENNReal.ofReal (Real.exp ((∑ i, a i * y i) - (∑ i, (a i) ^ 2) / 2)))
      = fun y => ∏ i, ENNReal.ofReal (Real.exp (a i * y i - (a i) ^ 2 / 2)) := by
    funext y
    rw [show ((∑ i, a i * y i) - (∑ i, (a i) ^ 2) / 2)
          = ∑ i, (a i * y i - (a i) ^ 2 / 2) from by
          rw [Finset.sum_sub_distrib, Finset.sum_div],
      Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _)]
  rw [hdensity, pi_withDensity_prod
    (f := fun i (x : ℝ) => ENNReal.ofReal (Real.exp (a i * x - (a i) ^ 2 / 2)))
    (fun i => by fun_prop)]
  congr 1
  funext i
  exact h1d i

/-- Transport of a `withDensity` through the coordinate map `WithLp.toLp 2`. -/
private lemma map_toLp_withDensity (μ : Measure (Fin k → ℝ))
    {w : (Fin k → ℝ) → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity w).map (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k))
      = (μ.map (WithLp.toLp 2)).withDensity (fun z => w z.ofLp) := by
  have hT : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    WithLp.measurable_toLp 2 (Fin k → ℝ)
  have hw' : Measurable (fun z : EuclideanSpace ℝ (Fin k) => w z.ofLp) :=
    hw.comp (WithLp.measurable_ofLp 2 (Fin k → ℝ))
  ext A hA
  rw [Measure.map_apply hT hA, withDensity_apply _ (hT hA), withDensity_apply _ hA,
    ← lintegral_indicator (hT hA), ← lintegral_indicator hA,
    lintegral_map (hw'.indicator hA) hT]
  classical
  refine lintegral_congr fun x => ?_
  simp only [Set.indicator_apply, Set.mem_preimage]

/-- **Cameron–Martin identity, measure form.**  Translating the standard Gaussian on
`EuclideanSpace ℝ (Fin k)` by `v` is the same as tilting it by `exp(⟪v, ·⟫ − ‖v‖²/2)`. -/
private lemma stdGaussian_map_add_eq_withDensity (v : EuclideanSpace ℝ (Fin k)) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun z => v + z)
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).withDensity
          (fun z => ENNReal.ofReal (Real.exp (⟪v, z⟫_ℝ - ‖v‖ ^ 2 / 2))) := by
  classical
  set a : Fin k → ℝ := fun i => v i with ha
  set π₀ : Measure (Fin k → ℝ) := Measure.pi (fun _ : Fin k => gaussianReal 0 1) with hπ₀
  have hT : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    WithLp.measurable_toLp 2 (Fin k → ℝ)
  have hmapT : π₀.map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin k)) :=
    map_pi_eq_stdGaussian
  have hsum : ∀ u w : EuclideanSpace ℝ (Fin k), ⟪u, w⟫_ℝ = ∑ i, u i * w i := by
    intro u w
    simp only [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hnorm : ‖v‖ ^ 2 = ∑ i, (a i) ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]
  have hshiftpi : π₀.map (fun x i => a i + x i) = Measure.pi (fun i => gaussianReal (a i) 1) := by
    haveI : ∀ i : Fin k, SigmaFinite ((gaussianReal 0 1).map (fun t : ℝ => a i + t)) := by
      intro i
      rw [gaussianReal_map_const_add]
      infer_instance
    rw [hπ₀, Measure.pi_map_pi (f := fun i (t : ℝ) => a i + t)
      (fun i => (measurable_const_add (a i)).aemeasurable)]
    congr 1
    funext i
    rw [gaussianReal_map_const_add]
    simp
  have hLHS : (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun z => v + z)
      = (π₀.map (fun x i => a i + x i)).map (WithLp.toLp 2) := by
    rw [← hmapT, Measure.map_map (by fun_prop) hT,
      Measure.map_map hT
        (measurable_pi_lambda _ (fun i => (measurable_pi_apply i).const_add (a i)))]
    congr 1
  rw [hLHS, hshiftpi, ← pi_gaussianReal_withDensity_shift a, ← hπ₀,
    map_toLp_withDensity π₀ (by fun_prop), hmapT]
  congr 1
  funext z
  rw [hsum, hnorm]

/-- With unit covariance, `multivariateGaussian` is a translate of the standard Gaussian. -/
private lemma mvGaussian_one_eq_map_add (v : EuclideanSpace ℝ (Fin k)) :
    multivariateGaussian v 1
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => v + x) := by
  rw [multivariateGaussian]
  simp only [CFC.sqrt_one, map_one, ContinuousLinearMap.one_apply]

/-- If tilting `μ` by `exp f` produces a probability measure, then `exp f` is `μ`-integrable
with integral one.  Used both for the exact normalisation of the product likelihood ratio and
for its square. -/
private lemma integrable_exp_of_withDensity_isProbability {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Measurable f)
    (h : IsProbabilityMeasure
      (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (f x))))) :
    Integrable (fun x => Real.exp (f x)) μ ∧ ∫ x, Real.exp (f x) ∂μ = 1 := by
  have hone : ∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂μ = 1 := by
    have hu := h.measure_univ
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hu
  have hmeas : AEStronglyMeasurable (fun x => Real.exp (f x)) μ :=
    (Real.continuous_exp.measurable.comp hf).aestronglyMeasurable
  have heq : ∫⁻ x, ‖Real.exp (f x)‖ₑ ∂μ = 1 := by
    rw [← hone]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hint : Integrable (fun x => Real.exp (f x)) μ := by
    refine ⟨hmeas, ?_⟩
    change ∫⁻ x, ‖Real.exp (f x)‖ₑ ∂μ < ⊤
    rw [heq]
    exact ENNReal.one_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hmeas, hone]
  simp

/-- The bounded continuous cut-off `min 1 (max 0 (‖z‖ − r))`: one outside the ball of radius
`r + 1`, zero inside the ball of radius `r`.  The test function that turns weak convergence
into the tightness estimate of `tendsto_measure_smul_norm_of_weakConverges`. -/
private noncomputable def normCutoff {E : Type*} [NormedAddCommGroup E] (r : ℝ) :
    BoundedContinuousFunction E ℝ where
  toFun z := min 1 (max 0 (‖z‖ - r))
  continuous_toFun := by fun_prop
  map_bounded' := by
    refine ⟨1, fun x y => ?_⟩
    have hx : min 1 (max 0 (‖x‖ - r)) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
    have hy : min 1 (max 0 (‖y‖ - r)) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
    rw [Real.dist_eq, abs_le]
    exact ⟨by linarith [hx.1, hx.2, hy.1, hy.2], by linarith [hx.1, hx.2, hy.1, hy.2]⟩

private lemma normCutoff_apply {E : Type*} [NormedAddCommGroup E] (r : ℝ) (z : E) :
    normCutoff r z = min 1 (max 0 (‖z‖ - r)) := rfl

/-- **Vanishing shrinking-multiple tails.**  If `μ n ⇝ ν` on a normed space and the
nonnegative scalars `cs n` tend to zero, then for every `ε > 0` the masses
`μ n {z | ε ≤ cs n · ‖z‖}` tend to zero.  This is the only consequence of tightness that the
Slutsky step of the drifting local limit needs. -/
private lemma tendsto_measure_smul_norm_of_weakConverges {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : ℕ → Measure E} [∀ n, IsProbabilityMeasure (μ n)] {ν : Measure E}
    [IsProbabilityMeasure ν]
    (hconv : AsymptoticStatistics.WeakConverges μ ν)
    {cs : ℕ → ℝ} (hcs0 : ∀ n, 0 ≤ cs n) (hcs : Tendsto cs atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (μ n).real {z : E | ε ≤ cs n * ‖z‖}) atTop (𝓝 0) := by
  classical
  have hmeasset : ∀ (t : ℝ), MeasurableSet {z : E | t ≤ ‖z‖} :=
    fun t => measurableSet_le measurable_const measurable_norm
  -- the ν-tails vanish
  have hνtail : Tendsto (fun m : ℕ => ν.real {z : E | (m : ℝ) ≤ ‖z‖}) atTop (𝓝 0) := by
    have hanti : Antitone (fun m : ℕ => {z : E | (m : ℝ) ≤ ‖z‖}) := by
      intro m m' hmm z hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      exact le_trans (by exact_mod_cast hmm) hz
    have hinter : (⋂ m : ℕ, {z : E | (m : ℝ) ≤ ‖z‖}) = (∅ : Set E) := by
      ext z
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hz
      obtain ⟨m, hm⟩ := exists_nat_gt ‖z‖
      exact absurd (hz m) (not_le.mpr hm)
    have h := MeasureTheory.tendsto_measure_iInter_atTop
      (μ := ν) (s := fun m : ℕ => {z : E | (m : ℝ) ≤ ‖z‖})
      (fun m => (hmeasset _).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hinter, measure_empty] at h
    have := (ENNReal.tendsto_toReal (by simp)).comp h
    simpa [MeasureTheory.Measure.real] using! this
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro δ hδ
  -- choose the radius from the limit tail
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ν.real {z : E | (m : ℝ) ≤ ‖z‖} < δ / 2 := by
    have := (NormedAddGroup.tendsto_nhds_zero.mp hνtail) (δ / 2) (by linarith)
    obtain ⟨m, hm⟩ := this.exists
    exact ⟨m, lt_of_abs_lt (by simpa [Real.norm_eq_abs] using hm)⟩
  set r : ℝ := (m : ℝ) with hr
  -- the cut-off dominates the indicator of the outer tail and is dominated by the inner one
  have hlow : ∀ (ρ : Measure E), IsProbabilityMeasure ρ →
      ρ.real {z : E | r + 1 ≤ ‖z‖} ≤ ∫ z, normCutoff (E := E) r z ∂ρ := by
    intro ρ hρ
    haveI := hρ
    rw [← integral_indicator_one (hmeasset (r + 1))]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator (hmeasset (r + 1)))
      ((normCutoff (E := E) r).integrable ρ) (fun z => ?_)
    by_cases hz : z ∈ {z : E | r + 1 ≤ ‖z‖}
    · rw [Set.indicator_of_mem hz, normCutoff_apply]
      have hz' : r + 1 ≤ ‖z‖ := hz
      have : (1 : ℝ) ≤ max 0 (‖z‖ - r) := le_max_of_le_right (by linarith)
      simp only [Pi.one_apply]
      exact le_min le_rfl this
    · rw [Set.indicator_of_notMem hz, normCutoff_apply]
      exact le_min zero_le_one (le_max_left _ _)
  have hhigh : ∫ z, normCutoff (E := E) r z ∂ν ≤ ν.real {z : E | r ≤ ‖z‖} := by
    rw [← integral_indicator_one (hmeasset r)]
    refine integral_mono ((normCutoff (E := E) r).integrable ν)
      ((integrable_const (1 : ℝ)).indicator (hmeasset r)) (fun z => ?_)
    by_cases hz : z ∈ {z : E | r ≤ ‖z‖}
    · rw [Set.indicator_of_mem hz]
      exact min_le_left _ _
    · rw [Set.indicator_of_notMem hz, normCutoff_apply]
      have hz' : ‖z‖ - r ≤ 0 := by
        simp only [Set.mem_setOf_eq, not_le] at hz
        linarith
      rw [max_eq_left hz']
      simp
  -- eventually the sequence's cut-off integral is small
  have hev1 : ∀ᶠ n in atTop, ∫ z, normCutoff (E := E) r z ∂(μ n) < δ := by
    have hlim := hconv (normCutoff (E := E) r)
    refine (hlim.eventually (gt_mem_nhds (show ∫ z, normCutoff (E := E) r z ∂ν < δ from ?_)))
    calc ∫ z, normCutoff (E := E) r z ∂ν ≤ ν.real {z : E | r ≤ ‖z‖} := hhigh
      _ < δ / 2 := hm
      _ < δ := by linarith
  have hev2 : ∀ᶠ n in atTop, cs n * (r + 1) < ε := by
    have hrpos : (0 : ℝ) < r + 1 := by positivity
    have := hcs.const_mul (r + 1)
    rw [mul_zero] at this
    have h2 : Tendsto (fun n => cs n * (r + 1)) atTop (𝓝 0) := by
      simpa [mul_comm] using this
    exact h2.eventually (gt_mem_nhds hε)
  filter_upwards [hev1, hev2] with n hn1 hn2
  have hsub : {z : E | ε ≤ cs n * ‖z‖} ⊆ {z : E | r + 1 ≤ ‖z‖} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    by_contra hcon
    rw [not_le] at hcon
    have : cs n * ‖z‖ ≤ cs n * (r + 1) :=
      mul_le_mul_of_nonneg_left hcon.le (hcs0 n)
    linarith
  have hbd := (measureReal_mono (μ := μ n) hsub (measure_ne_top _ _)).trans (hlow (μ n) inferInstance)
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  linarith

end Attainment

/-- **Drifting-parameter local limit law for the score vector.**  If the local parameters
`u n` converge to `h₀`, then under `Q n (u n)` — i.i.d. sampling from the smooth model at the
canonical parameter `u n/√n` — the standardised score vector converges in law to `N(h₀, Iₖ)`.

This is Le Cam's third lemma, in the case where the log-likelihood ratio is an *exact* affine
function of the statistic: with `Zₙ = (√n)⁻¹ ∑ᵢ ψ(Xᵢ)` and
`A(θ) = log ∫ exp⟪θ, ψ⟫ dP₀`, the density of the product tilt against `P₀ⁿ` is
`exp(Lₙ)` with `Lₙ = ⟪u n, Zₙ⟫ − n·A(u n/√n)`.  Hence the joint law of `(Zₙ, Lₙ)` under the
null is a continuous image of the law of `Zₙ` up to a drift that vanishes by Slutsky
(`tendsto_measure_smul_norm_of_weakConverges`), whose limit is
`pi_scoreLaw_weakConverges`; and Le Cam's uniform-integrability hypothesis follows from the
exact second-moment identity `∫ exp(2Lₙ) dP₀ⁿ = exp(n·A(2u n/√n) − 2n·A(u n/√n))`, bounded
because `n·A(t·u n/√n) → t²‖h₀‖²/2` by `logPartition_quadratic_bound`.  The tilted limit is
the Cameron–Martin shift `N(h₀, Iₖ)`. -/
private lemma scoreVec_weakConverges_drift {k : ℕ} {P₀ : Measure 𝓧}
    [IsProbabilityMeasure P₀] {ψ : Fin k → 𝓧 → ℝ}
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k)))
    {Q : ℕ → EuclideanSpace ℝ (Fin k) → Measure Ω} [∀ n h, IsProbabilityMeasure (Q n h)]
    {X : (n : ℕ) → Fin n → Ω → 𝓧}
    {u : ℕ → EuclideanSpace ℝ (Fin k)} {h₀ : EuclideanSpace ℝ (Fin k)}
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    (hX : ∀ n, ∀ i, Measurable (X n i))
    (hindep : ∀ n h, iIndepFun (X n) (Q n h))
    (hlaw : ∀ n h, ∀ i, (Q n h).map (X n i)
      = (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h))
    (hu : Tendsto u atTop (𝓝 h₀)) :
    WeakConverges (fun n => (Q n (u n)).map (scoreVec ψ (X n)))
      (multivariateGaussian h₀ 1) := by
  classical
  have hψmeas : ∀ j, Measurable (ψ j) := fun j =>
    ((measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 (Fin k → ℝ))).comp hψ
  have hgmeas : Measurable (psiVec ψ) :=
    (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp (measurable_pi_lambda _ hψmeas)
  -- ### The log-partition function and the exponential-tilt representation
  set A : EuclideanSpace ℝ (Fin k) → ℝ :=
    fun θ => Real.log (∫ x, Real.exp ⟪θ, psiVec ψ x⟫_ℝ ∂P₀) with hAdef
  have hEprob : ∀ θ : EuclideanSpace ℝ (Fin k),
      IsProbabilityMeasure ((smoothModel P₀ ψ hψ).P θ) := by
    intro θ
    have h1 := hlaw 1 θ (0 : Fin 1)
    have hs : (Real.sqrt ((1 : ℕ) : ℝ))⁻¹ • θ = θ := by norm_num
    rw [hs] at h1
    rw [← h1]
    exact Measure.isProbabilityMeasure_map (hX 1 (0 : Fin 1)).aemeasurable
  haveI hEprobI : ∀ θ, IsProbabilityMeasure ((smoothModel P₀ ψ hψ).P θ) := hEprob
  have hEint : ∀ θ, Integrable (fun x => Real.exp ⟪θ, psiVec ψ x⟫_ℝ) P₀ := by
    intro θ
    refine integrable_exp_of_isProbabilityMeasure_tilted (P₀ := P₀) ?_
    rw [← smoothModel_P_eq P₀ ψ hψ θ]
    exact hEprob θ
  have hMpos : ∀ θ, 0 < ∫ x, Real.exp ⟪θ, psiVec ψ x⟫_ℝ ∂P₀ :=
    fun θ => integral_exp_pos (hEint θ)
  have hEdens : ∀ θ, (smoothModel P₀ ψ hψ).P θ
      = P₀.withDensity (fun x => ENNReal.ofReal (Real.exp (⟪θ, psiVec ψ x⟫_ℝ - A θ))) := by
    intro θ
    rw [smoothModel_P_eq P₀ ψ hψ θ]
    exact tilted_eq_withDensity_log P₀ _ (hMpos θ)
  obtain ⟨Cst, hCst0, hCstbd⟩ :=
    logPartition_quadratic_bound (P₀ := P₀) hψmeas hortho hcentred hEint (r := 1) one_pos
  -- ### The canonical null and alternative experiments
  set θs : ℕ → EuclideanSpace ℝ (Fin k) := fun n => (Real.sqrt (n : ℝ))⁻¹ • u n with hθs
  set PN : (n : ℕ) → Measure (Fin n → 𝓧) := fun n => Measure.pi (fun _ : Fin n => P₀) with hPN
  haveI hPNprob : ∀ n, IsProbabilityMeasure (PN n) := by
    intro n; rw [hPN]; infer_instance
  set QN : (n : ℕ) → Measure (Fin n → 𝓧) :=
    fun n => Measure.pi (fun _ : Fin n => (smoothModel P₀ ψ hψ).P (θs n)) with hQN
  haveI hQNprob : ∀ n, IsProbabilityMeasure (QN n) := by
    intro n; rw [hQN]; infer_instance
  set T : (n : ℕ) → (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k) :=
    fun n d => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i) with hT
  have hTmeas : ∀ n, Measurable (T n) := by
    intro n
    simp only [hT]
    exact measurable_const.fun_smul
      (Finset.univ.measurable_sum fun i _ => hgmeas.comp (measurable_pi_apply i))
  have hinnermeas : ∀ v : EuclideanSpace ℝ (Fin k),
      Measurable fun z : EuclideanSpace ℝ (Fin k) => ⟪v, z⟫_ℝ :=
    fun v => (continuous_const.inner continuous_id).measurable
  set aN : ℕ → ℝ := fun n => (n : ℝ) * A (θs n) with haN
  set L : (n : ℕ) → (Fin n → 𝓧) → ℝ := fun n d => ⟪u n, T n d⟫_ℝ - aN n with hL
  have hLmeas : ∀ n, Measurable (L n) := by
    intro n
    simp only [hL]
    exact ((hinnermeas (u n)).comp (hTmeas n)).sub measurable_const
  -- ### The exact likelihood-ratio representation, at every scalar multiple of `θs n`
  have hpidens : ∀ (t : ℝ) (n : ℕ),
      Measure.pi (fun _ : Fin n => (smoothModel P₀ ψ hψ).P (t • θs n))
        = (PN n).withDensity (fun d =>
            ENNReal.ofReal (Real.exp (t * ⟪u n, T n d⟫_ℝ - (n : ℝ) * A (t • θs n)))) := by
    intro t n
    have hum : Measurable (fun x => ⟪t • θs n, psiVec ψ x⟫_ℝ - A (t • θs n)) :=
      ((hinnermeas (t • θs n)).comp hgmeas).sub measurable_const
    haveI hpm : IsProbabilityMeasure (P₀.withDensity (fun x =>
        ENNReal.ofReal (Real.exp (⟪t • θs n, psiVec ψ x⟫_ℝ - A (t • θs n))))) := by
      rw [← hEdens (t • θs n)]; exact hEprob _
    have hsumid : ∀ d : Fin n → 𝓧,
        ∑ i, (⟪t • θs n, psiVec ψ (d i)⟫_ℝ - A (t • θs n))
          = t * ⟪u n, T n d⟫_ℝ - (n : ℝ) * A (t • θs n) := by
      intro d
      have h1 : ∑ i, ⟪t • θs n, psiVec ψ (d i)⟫_ℝ = t * ⟪u n, T n d⟫_ℝ := by
        have h2 : ∑ i, ⟪t • θs n, psiVec ψ (d i)⟫_ℝ
            = ⟪t • θs n, ∑ i, psiVec ψ (d i)⟫_ℝ := (inner_sum _ _ _).symm
        rw [h2, real_inner_smul_left]
        simp only [hT, hθs, real_inner_smul_right, real_inner_smul_left]
      rw [Finset.sum_sub_distrib, h1]
      simp
    rw [show (fun _ : Fin n => (smoothModel P₀ ψ hψ).P (t • θs n))
        = (fun _ : Fin n => P₀.withDensity (fun x =>
            ENNReal.ofReal (Real.exp (⟪t • θs n, psiVec ψ x⟫_ℝ - A (t • θs n)))))
        from funext fun _ => hEdens _,
      pi_withDensity_exp (n := n) (P₀ := P₀) hum, hPN]
    congr 1
    funext d
    rw [hsumid d]
  have hdens : ∀ n, QN n = (PN n).withDensity
      (fun d => ENNReal.ofReal (Real.exp (L n d))) := by
    intro n
    have h := hpidens 1 n
    rw [one_smul] at h
    rw [hQN]
    simp only []
    rw [h]
    congr 1
    funext d
    simp only [hL, haN, one_mul]
  -- ### The null limit of the score vector
  have hμweak : WeakConverges (fun n => (PN n).map (T n))
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    simpa only [hPN, hT] using
      pi_scoreLaw_weakConverges (P₀ := P₀) (ψ := ψ) hψmeas hortho hcentred
  haveI hmuprob : ∀ n, IsProbabilityMeasure ((PN n).map (T n)) :=
    fun n => Measure.isProbabilityMeasure_map (hTmeas n).aemeasurable
  -- ### The log-partition drift `n·A(t θₙ) → t²‖h₀‖²/2`
  obtain ⟨Mb, hMbmem⟩ := hu.norm.bddAbove_range
  have hMb : ∀ n, ‖u n‖ ≤ Mb := fun n => hMbmem ⟨n, rfl⟩
  have hMb0 : 0 ≤ Mb := le_trans (norm_nonneg _) (hMb 0)
  have hsqrtatTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hθnorm : ∀ n : ℕ, 0 < n → ‖θs n‖ = ‖u n‖ / Real.sqrt (n : ℝ) := by
    intro n hn
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    simp only [hθs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hs.le)]
    rw [inv_mul_eq_div]
  have hsmall : ∀ t : ℝ, 0 ≤ t →
      ∀ᶠ n : ℕ in atTop, ‖(t • θs n : EuclideanSpace ℝ (Fin k))‖ ≤ 1 := by
    intro t ht
    have hlim : Tendsto (fun n : ℕ => t * Mb / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hsqrtatTop
    have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hθnorm n hn0]
    calc t * (‖u n‖ / Real.sqrt (n : ℝ)) ≤ t * (Mb / Real.sqrt (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (by gcongr; exact hMb n) ht
      _ = t * Mb / Real.sqrt (n : ℝ) := by ring
      _ ≤ 1 := hn.le
  have hAdrift : ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun n : ℕ => (n : ℝ) * A (t • θs n)) atTop (𝓝 (t ^ 2 * ‖h₀‖ ^ 2 / 2)) := by
    intro t ht
    have hdiff : Tendsto
        (fun n : ℕ => (n : ℝ) * A (t • θs n) - t ^ 2 * ‖u n‖ ^ 2 / 2) atTop (𝓝 0) := by
      refine squeeze_zero_norm'
        (a := fun n : ℕ => Cst * (t * Mb) ^ 3 / Real.sqrt (n : ℝ)) ?_ ?_
      · filter_upwards [hsmall t ht, eventually_gt_atTop 0] with n hn hn0
        have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
        have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
        have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
          Real.mul_self_sqrt (Nat.cast_nonneg n)
        have hnt : ‖(t • θs n : EuclideanSpace ℝ (Fin k))‖
            = t * ‖u n‖ / Real.sqrt (n : ℝ) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hθnorm n hn0]
          ring
        have hb := hCstbd (t • θs n) hn
        have hsq2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
        have hcube3 : Real.sqrt (n : ℝ) ^ 3 = (n : ℝ) * Real.sqrt (n : ℝ) := by
          rw [pow_succ, hsq2]
        have hquad : (n : ℝ) * (‖(t • θs n : EuclideanSpace ℝ (Fin k))‖ ^ 2 / 2)
            = t ^ 2 * ‖u n‖ ^ 2 / 2 := by
          rw [hnt, div_pow, hsq2]
          field_simp
        have hcube : (n : ℝ) * (Cst * ‖(t • θs n : EuclideanSpace ℝ (Fin k))‖ ^ 3)
            = Cst * (t * ‖u n‖) ^ 3 / Real.sqrt (n : ℝ) := by
          rw [hnt, div_pow, hcube3]
          field_simp
        calc ‖(n : ℝ) * A (t • θs n) - t ^ 2 * ‖u n‖ ^ 2 / 2‖
            = (n : ℝ) * |A (t • θs n)
                - ‖(t • θs n : EuclideanSpace ℝ (Fin k))‖ ^ 2 / 2| := by
              rw [Real.norm_eq_abs, ← hquad, ← mul_sub, abs_mul, abs_of_nonneg hnR.le]
          _ ≤ (n : ℝ) * (Cst * ‖(t • θs n : EuclideanSpace ℝ (Fin k))‖ ^ 3) :=
              mul_le_mul_of_nonneg_left hb hnR.le
          _ = Cst * (t * Mb) ^ 3 / Real.sqrt (n : ℝ) - Cst *
                ((t * Mb) ^ 3 - (t * ‖u n‖) ^ 3) / Real.sqrt (n : ℝ) := by
              rw [hcube]; ring
          _ ≤ Cst * (t * Mb) ^ 3 / Real.sqrt (n : ℝ) := by
              have h1 : (t * ‖u n‖) ^ 3 ≤ (t * Mb) ^ 3 := by
                have : t * ‖u n‖ ≤ t * Mb := mul_le_mul_of_nonneg_left (hMb n) ht
                exact pow_le_pow_left₀ (by positivity) this 3
              have h2 : 0 ≤ Cst * ((t * Mb) ^ 3 - (t * ‖u n‖) ^ 3) / Real.sqrt (n : ℝ) := by
                apply div_nonneg _ hs.le
                nlinarith
              linarith
      · exact Filter.Tendsto.div_atTop tendsto_const_nhds hsqrtatTop
    have hmain : Tendsto (fun n => t ^ 2 * ‖u n‖ ^ 2 / 2) atTop (𝓝 (t ^ 2 * ‖h₀‖ ^ 2 / 2)) := by
      have := hu.norm
      exact ((this.pow 2).const_mul (t ^ 2)).div_const 2
    have := hdiff.add hmain
    simpa using this
  have haNlim : Tendsto aN atTop (𝓝 (‖h₀‖ ^ 2 / 2)) := by
    have := hAdrift 1 zero_le_one
    simp only [one_smul, one_pow, one_mul] at this
    simpa only [haN] using this
  -- ### Uniform integrability of the likelihood ratio
  obtain ⟨hexp1int, hexp1one⟩ : (∀ n, Integrable (fun d => Real.exp (L n d)) (PN n)) ∧
      ∀ n, ∫ d, Real.exp (L n d) ∂(PN n) = 1 := by
    constructor
    · intro n
      refine (integrable_exp_of_withDensity_isProbability (hLmeas n) ?_).1
      rw [← hdens n]; exact hQNprob n
    · intro n
      refine (integrable_exp_of_withDensity_isProbability (hLmeas n) ?_).2
      rw [← hdens n]; exact hQNprob n
  set bN : ℕ → ℝ := fun n => (n : ℝ) * A ((2 : ℝ) • θs n) with hbN
  have hsqmeas : ∀ n, Measurable
      (fun d : Fin n → 𝓧 => (2 : ℝ) * ⟪u n, T n d⟫_ℝ - bN n) := by
    intro n
    exact (((hinnermeas (u n)).comp (hTmeas n)).const_mul 2).sub measurable_const
  have hsqprob : ∀ n, IsProbabilityMeasure ((PN n).withDensity
      (fun d => ENNReal.ofReal (Real.exp ((2 : ℝ) * ⟪u n, T n d⟫_ℝ - bN n)))) := by
    intro n
    rw [← hpidens 2 n]
    infer_instance
  have hexp2 : ∀ n, Integrable
      (fun d => Real.exp ((2 : ℝ) * ⟪u n, T n d⟫_ℝ - bN n)) (PN n) ∧
      ∫ d, Real.exp ((2 : ℝ) * ⟪u n, T n d⟫_ℝ - bN n) ∂(PN n) = 1 := fun n =>
    integrable_exp_of_withDensity_isProbability (hsqmeas n) (hsqprob n)
  have hbNlim : Tendsto (fun n => bN n - 2 * aN n) atTop (𝓝 (‖h₀‖ ^ 2)) := by
    have h2 := hAdrift 2 (by norm_num)
    have := h2.sub (haNlim.const_mul 2)
    simp only [hbN]
    convert this using 2
    ring
  have hUI : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∫ d, Real.exp (L n d) - min (Real.exp (L n d)) M ∂(PN n) ≤ ε := by
    intro ε hε
    set K : ℝ := Real.exp (‖h₀‖ ^ 2 + 1) with hK
    have hKpos : 0 < K := Real.exp_pos _
    have hev : ∀ᶠ n in atTop, bN n - 2 * aN n ≤ ‖h₀‖ ^ 2 + 1 := by
      have hlt : ‖h₀‖ ^ 2 < ‖h₀‖ ^ 2 + 1 := by linarith
      exact (hbNlim.eventually (gt_mem_nhds hlt)).mono fun n hn => hn.le
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
    refine ⟨K / ε, by positivity, N₀, ?_⟩
    intro n hn
    set M : ℝ := K / ε with hM
    have hMpos' : 0 < M := by positivity
    have hcomp : ∀ d : Fin n → 𝓧,
        Real.exp (L n d) - min (Real.exp (L n d)) M
          ≤ Real.exp (bN n - 2 * aN n)
            * Real.exp ((2 : ℝ) * ⟪u n, T n d⟫_ℝ - bN n) / M := by
      intro d
      have hfact : Real.exp (bN n - 2 * aN n)
          * Real.exp ((2 : ℝ) * ⟪u n, T n d⟫_ℝ - bN n) = Real.exp (L n d) ^ 2 := by
        rw [← Real.exp_add, ← Real.exp_nat_mul]
        congr 1
        simp only [hL]
        ring
      rw [hfact]
      rcases le_or_gt (Real.exp (L n d)) M with hle | hgt
      · rw [min_eq_left hle, sub_self]
        positivity
      · rw [min_eq_right hgt.le]
        have h1 : Real.exp (L n d) - M ≤ Real.exp (L n d) := by linarith [hMpos'.le]
        have h2 : Real.exp (L n d) ≤ Real.exp (L n d) ^ 2 / M := by
          rw [le_div_iff₀ hMpos', sq]
          exact mul_le_mul_of_nonneg_left hgt.le (Real.exp_pos _).le
        linarith
    have hint1 : Integrable
        (fun d => Real.exp (L n d) - min (Real.exp (L n d)) M) (PN n) := by
      refine (hexp1int n).sub ?_
      refine Integrable.mono' (hexp1int n)
        (((Real.continuous_exp.measurable.comp (hLmeas n)).min
          measurable_const).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun d => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.exp_pos _).le hMpos'.le)]
      exact min_le_left _ _
    have hint2 : Integrable (fun d => Real.exp (bN n - 2 * aN n)
        * Real.exp ((2 : ℝ) * ⟪u n, T n d⟫_ℝ - bN n) / M) (PN n) := by
      simpa [div_eq_mul_inv, mul_assoc] using
        (((hexp2 n).1.const_mul (Real.exp (bN n - 2 * aN n))).mul_const M⁻¹)
    calc ∫ d, Real.exp (L n d) - min (Real.exp (L n d)) M ∂(PN n)
        ≤ ∫ d, Real.exp (bN n - 2 * aN n)
            * Real.exp ((2 : ℝ) * ⟪u n, T n d⟫_ℝ - bN n) / M ∂(PN n) :=
          integral_mono hint1 hint2 hcomp
      _ = Real.exp (bN n - 2 * aN n) / M := by
          rw [show (fun d : Fin n → 𝓧 => Real.exp (bN n - 2 * aN n)
              * Real.exp ((2 : ℝ) * ⟪u n, T n d⟫_ℝ - bN n) / M)
              = fun d => (Real.exp (bN n - 2 * aN n) / M)
                • Real.exp ((2 : ℝ) * ⟪u n, T n d⟫_ℝ - bN n) from by
            funext d; simp only [smul_eq_mul]; ring,
            integral_smul, (hexp2 n).2, smul_eq_mul, mul_one]
      _ ≤ K / M := by
          gcongr
          exact Real.exp_le_exp.mpr (hN₀ n hn)
      _ = ε := by
          rw [hM, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hKpos.ne', mul_one]
  -- ### The joint weak limit under the null
  set gmap : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) × ℝ :=
    fun z => (z, ⟪h₀, z⟫_ℝ - ‖h₀‖ ^ 2 / 2) with hgmap
  have hgmapcont : Continuous gmap := by
    simp only [hgmap]
    exact continuous_id.prodMk ((continuous_const.inner continuous_id).sub continuous_const)
  set π : Measure (EuclideanSpace ℝ (Fin k) × ℝ) :=
    (stdGaussian (EuclideanSpace ℝ (Fin k))).map gmap with hπ
  haveI hπprob : IsProbabilityMeasure π := by
    rw [hπ]; exact Measure.isProbabilityMeasure_map hgmapcont.measurable.aemeasurable
  have hjoint : WeakConverges (fun n => (PN n).map (fun d => (T n d, L n d))) π := by
    refine AsymptoticStatistics.WeakConverges.slutsky_of_tendstoInMeasure_dist
      (X := fun n d => gmap (T n d)) (Y := fun n d => (T n d, L n d))
      (fun n => (hgmapcont.measurable.comp (hTmeas n)).aemeasurable)
      (fun n => ((hTmeas n).prodMk (hLmeas n)).aemeasurable) ?_ ?_
    · have hmapeq : ∀ n, ((PN n).map (T n)).map gmap
          = (PN n).map (fun d => gmap (T n d)) := by
        intro n
        rw [Measure.map_map hgmapcont.measurable (hTmeas n)]
        rfl
      have hw := hμweak.map (f := gmap) hgmapcont hgmapcont.measurable
      simp only [hmapeq] at hw
      rw [hπ]
      exact hw
    · intro ε hε
      have hcs0 : ∀ n, (0 : ℝ) ≤ ‖h₀ - u n‖ := fun n => norm_nonneg _
      have hcslim : Tendsto (fun n => ‖h₀ - u n‖) atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := h₀) (f := atTop (α := ℕ))).sub hu
        simpa using this.norm
      have htail := tendsto_measure_smul_norm_of_weakConverges hμweak hcs0 hcslim
        (show (0 : ℝ) < ε / 2 by linarith)
      have heslim : Tendsto (fun n => |aN n - ‖h₀‖ ^ 2 / 2|) atTop (𝓝 0) := by
        have := haNlim.sub (tendsto_const_nhds (x := ‖h₀‖ ^ 2 / 2))
        simpa using this.abs
      have hesev : ∀ᶠ n in atTop, |aN n - ‖h₀‖ ^ 2 / 2| < ε / 2 :=
        heslim.eventually (gt_mem_nhds (by linarith))
      refine squeeze_zero' (g := fun n => ((PN n).map (T n)).real
          {z : EuclideanSpace ℝ (Fin k) | ε / 2 ≤ ‖h₀ - u n‖ * ‖z‖})
        (Filter.Eventually.of_forall fun n => measureReal_nonneg) ?_ ?_
      · filter_upwards [hesev] with n hn
        have hsub : {d : Fin n → 𝓧 | ε ≤ dist (gmap (T n d)) (T n d, L n d)}
            ⊆ (T n) ⁻¹' {z : EuclideanSpace ℝ (Fin k) | ε / 2 ≤ ‖h₀ - u n‖ * ‖z‖} := by
          intro d hd
          simp only [Set.mem_setOf_eq, Set.mem_preimage] at hd ⊢
          have hdd : dist (gmap (T n d)) (T n d, L n d)
              = |⟪h₀, T n d⟫_ℝ - ‖h₀‖ ^ 2 / 2 - L n d| := by
            simp only [hgmap, Prod.dist_eq, dist_self, Real.dist_eq]
            exact max_eq_right (abs_nonneg _)
          rw [hdd] at hd
          have hsplit : ⟪h₀, T n d⟫_ℝ - ‖h₀‖ ^ 2 / 2 - L n d
              = ⟪h₀ - u n, T n d⟫_ℝ + (aN n - ‖h₀‖ ^ 2 / 2) := by
            simp only [hL, inner_sub_left]
            ring
          rw [hsplit] at hd
          have hb1 : |⟪h₀ - u n, T n d⟫_ℝ| ≤ ‖h₀ - u n‖ * ‖T n d‖ :=
            abs_real_inner_le_norm _ _
          have hb2 : |⟪h₀ - u n, T n d⟫_ℝ + (aN n - ‖h₀‖ ^ 2 / 2)|
              ≤ ‖h₀ - u n‖ * ‖T n d‖ + |aN n - ‖h₀‖ ^ 2 / 2| :=
            (abs_add_le _ _).trans (add_le_add hb1 le_rfl)
          have hfin := le_trans hd hb2
          linarith
        have hmeasset : MeasurableSet
            ((T n) ⁻¹' {z : EuclideanSpace ℝ (Fin k) | ε / 2 ≤ ‖h₀ - u n‖ * ‖z‖}) :=
          (hTmeas n) (measurableSet_le measurable_const (measurable_const.mul measurable_norm))
        calc (PN n).real {d : Fin n → 𝓧 | ε ≤ dist (gmap (T n d)) (T n d, L n d)}
            ≤ (PN n).real ((T n) ⁻¹' {z : EuclideanSpace ℝ (Fin k) |
                ε / 2 ≤ ‖h₀ - u n‖ * ‖z‖}) := measureReal_mono hsub (measure_ne_top _ _)
          _ = ((PN n).map (T n)).real {z : EuclideanSpace ℝ (Fin k) |
                ε / 2 ≤ ‖h₀ - u n‖ * ‖z‖} := by
              simp only [MeasureTheory.Measure.real]
              rw [Measure.map_apply (hTmeas n)
                (measurableSet_le measurable_const (measurable_const.fun_mul measurable_norm))]
      · exact htail
  -- ### The tilted limit is the Cameron–Martin shift
  haveI hCMprob : IsProbabilityMeasure ((stdGaussian (EuclideanSpace ℝ (Fin k))).withDensity
      (fun z => ENNReal.ofReal (Real.exp (⟪h₀, z⟫_ℝ - ‖h₀‖ ^ 2 / 2)))) := by
    rw [← stdGaussian_map_add_eq_withDensity h₀]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  obtain ⟨hCMint, hCMone⟩ := integrable_exp_of_withDensity_isProbability
    (μ := stdGaussian (EuclideanSpace ℝ (Fin k)))
    (f := fun z => ⟪h₀, z⟫_ℝ - ‖h₀‖ ^ 2 / 2)
    ((hinnermeas h₀).sub measurable_const) hCMprob
  have hae : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin k) × ℝ => Real.exp p.2)
      ((stdGaussian (EuclideanSpace ℝ (Fin k))).map gmap) := by fun_prop
  have hπint : Integrable (fun p : EuclideanSpace ℝ (Fin k) × ℝ => Real.exp p.2) π := by
    rw [hπ, integrable_map_measure hae hgmapcont.measurable.aemeasurable]
    simpa only [hgmap, Function.comp_def] using hCMint
  have hπone : ∫ p, Real.exp p.2 ∂π = 1 := by
    rw [hπ, integral_map hgmapcont.measurable.aemeasurable hae]
    simpa only [hgmap] using hCMone
  have htarget : (π.withDensity (fun p => ENNReal.ofReal (Real.exp p.2))).map Prod.fst
      = multivariateGaussian h₀ 1 := by
    have h1 : (Prod.fst ∘ gmap) = id := by funext z; simp only [hgmap, Function.comp_apply, id]
    have h2 : ((fun p : EuclideanSpace ℝ (Fin k) × ℝ => ENNReal.ofReal (Real.exp p.2)) ∘ gmap)
        = fun z => ENNReal.ofReal (Real.exp (⟪h₀, z⟫_ℝ - ‖h₀‖ ^ 2 / 2)) := by
      funext z; simp only [hgmap, Function.comp_apply]
    rw [hπ, AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
      (stdGaussian (EuclideanSpace ℝ (Fin k))) gmap hgmapcont.measurable
      (fun p => ENNReal.ofReal (Real.exp p.2)) (by fun_prop),
      Measure.map_map measurable_fst hgmapcont.measurable, h1, h2, Measure.map_id,
      mvGaussian_one_eq_map_add h₀, stdGaussian_map_add_eq_withDensity h₀]
  -- ### Le Cam's third lemma, and the transfer back to `Ω`
  have hlecam := AsymptoticStatistics.Contiguity.weak_limit_under_Q_of_lecam_third
    (Ω := fun n => (Fin n → 𝓧)) PN QN T L hTmeas hLmeas hdens π hjoint hUI hπint hπone
  rw [htarget] at hlecam
  have hlawid : ∀ n, (Q n (u n)).map (scoreVec ψ (X n)) = (QN n).map (T n) := by
    intro n
    simp only [hQN, hT, hθs]
    exact law_scoreVec_pi hψmeas (hX n) (hindep n (u n)) (hlaw n (u n))
  rw [funext hlawid]
  exact hlecam

/-- **The smooth test attains the maximin value on the local shell** (the deep half of
`smoothTest_asymptotically_maximin`). Under the local alternatives `θ = h n^{-1/2}` with
`b ≤ |h| ≤ B`, the minimum power of the smooth test `1{Sₙ > c}` converges to
`P{χ²_k(b²) > c_{k,1−α}}`.

CLOSED (wave 7), along the route re-derived in wave 6: no uniformity over the shell and no
Berry–Esseen estimate is needed, because the conclusion is about an *infimum*.

* `scoreVec_weakConverges_drift` supplies the DRIFTING-parameter local limit law: for any
  `hₙ → h₀`, the score vector under `Q n hₙ` converges in law to `N(h₀, Iₖ)`.  It is proved
  by Le Cam's third lemma with an *exact* affine log-likelihood ratio; see its docstring.
  Composing with the continuous map `z ↦ ‖z‖²` and the portmanteau theorem at the region
  `{c < ‖z‖²}` — whose frontier is Gaussian-null because `{‖z‖² ≤ c}` is convex — turns it
  into `power_n(hₙ) → ncχ²_k(‖h₀‖²)(c, ∞)`.
* `limsup ≤` is then immediate: evaluate at a *fixed* `h₁` on the inner boundary `‖h₁‖ = b`,
  which lies in the shell because `b < B`.
* `liminf ≥` chooses near-minimisers `hₙ ∈ Shell` with
  `power_n(hₙ) ≤ sInf_n + (n+1)⁻¹`, extracts a subsequence realising the liminf and, the
  shell being COMPACT (closed and contained in the ball of radius `B`) and fixed in `n`, a
  further convergent subsequence `hₙ → h₀` with `‖h₀‖ ≥ b`.  The drifting limit law along
  that subsequence — obtained from the full-sequence statement by extending the extracted
  parameters by `h₀` off the range of the extraction — plus
  `noncentralChiSquared_tail_mono` gives the required bound. -/
private lemma smoothTest_shell_minPower_tendsto {k : ℕ} {α b B c : ℝ} {P₀ : Measure 𝓧}
    [IsProbabilityMeasure P₀] {ψ : Fin k → 𝓧 → ℝ}
    {Q : ℕ → EuclideanSpace ℝ (Fin k) → Measure Ω} [∀ n h, IsProbabilityMeasure (Q n h)]
    {X : (n : ℕ) → Fin n → Ω → 𝓧}
    (hk : 0 < k) (hb : 0 < b) (hbB : b < B) (hα : 0 < α) (hα1 : α < 1)
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k)))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    (hint : (0 : EuclideanSpace ℝ (Fin k)) ∈ interior (smoothModel P₀ ψ hψ).natSet)
    (hX : ∀ n, ∀ i, Measurable (X n i))
    (hindep : ∀ n h, iIndepFun (X n) (Q n h))
    (hlaw : ∀ n h, ∀ i, (Q n h).map (X n i)
      = (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h)) :
    Tendsto (fun n => sInf ((fun h => power (Q n)
          (fun ω => if c < smoothStat ψ (X n) ω then (1 : ℝ) else 0) h)
        '' {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖ ∧ ‖h‖ ≤ B})) atTop
        (nhds (((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal)) := by
  classical
  have hψmeas : ∀ j, Measurable (ψ j) := fun j =>
    ((measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 (Fin k → ℝ))).comp hψ
  -- ### The statistic is the squared norm of the score vector
  have hSnorm : ∀ (n : ℕ) (ω : Ω), smoothStat ψ (X n) ω = ‖scoreVec ψ (X n) ω‖ ^ 2 := by
    intro n ω
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  set Reg : Set (EuclideanSpace ℝ (Fin k)) := {z | c < ‖z‖ ^ 2} with hRegdef
  have hRegmeas : MeasurableSet Reg :=
    measurableSet_lt measurable_const (measurable_norm.pow_const 2)
  have hpwmap : ∀ (n : ℕ) (h : EuclideanSpace ℝ (Fin k)),
      power (Q n) (fun ω => if c < smoothStat ψ (X n) ω then (1 : ℝ) else 0) h
        = (((Q n h).map (scoreVec ψ (X n))) Reg).toReal := by
    intro n h
    have hZmeas : Measurable (scoreVec ψ (X n)) := measurable_scoreVec hψmeas (hX n)
    have hpre : {ω | c < smoothStat ψ (X n) ω} = (scoreVec ψ (X n)) ⁻¹' Reg := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hRegdef, hSnorm n ω]
    have hind : (fun ω => if c < smoothStat ψ (X n) ω then (1 : ℝ) else 0)
        = Set.indicator ((scoreVec ψ (X n)) ⁻¹' Reg) 1 := by
      funext ω
      by_cases hc : c < smoothStat ψ (X n) ω
      · have hc' : ω ∈ (scoreVec ψ (X n)) ⁻¹' Reg := by
          simp only [Set.mem_preimage, hRegdef, Set.mem_setOf_eq, ← hSnorm n ω]
          exact hc
        rw [Set.indicator_of_mem hc', Pi.one_apply, if_pos hc]
      · have hc' : ω ∉ (scoreVec ψ (X n)) ⁻¹' Reg := by
          simp only [Set.mem_preimage, hRegdef, Set.mem_setOf_eq, ← hSnorm n ω]
          exact hc
        rw [Set.indicator_of_notMem hc', if_neg hc]
    simp only [power, hind]
    rw [integral_indicator_one (hZmeas hRegmeas), Measure.map_apply hZmeas hRegmeas]
    rfl
  -- ### The Gaussian mass of the rejection region, and its frontier
  have hRegmass : ∀ v : EuclideanSpace ℝ (Fin k),
      (multivariateGaussian v 1) Reg
        = noncentralChiSquared k (‖v‖ ^ 2).toNNReal (Set.Ioi c) := by
    intro v
    have hv : ‖v‖ = Real.sqrt (((‖v‖ ^ 2).toNNReal : ℝ)) := by
      rw [Real.coe_toNNReal _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg v)]
    rw [← map_normSq_multivariateGaussian_of_norm_eq k (‖v‖ ^ 2).toNNReal hv,
      Measure.map_apply (measurable_norm.pow_const 2) measurableSet_Ioi]
    rfl
  have hCconv : Convex ℝ {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ^ 2 ≤ c} := by
    rcases le_or_gt 0 c with hc0 | hc0
    · have hball : {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ^ 2 ≤ c}
          = Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (Real.sqrt c) := by
        ext z
        simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
        constructor
        · intro hzz
          rw [← Real.sqrt_sq (norm_nonneg z)]
          exact Real.sqrt_le_sqrt hzz
        · intro hzz
          have := pow_le_pow_left₀ (norm_nonneg z) hzz 2
          rwa [Real.sq_sqrt hc0] at this
      rw [hball]
      exact convex_closedBall _ _
    · have hempty : {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ^ 2 ≤ c} = (∅ : Set _) := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact lt_of_lt_of_le hc0 (sq_nonneg _)
      rw [hempty]
      exact convex_empty
  have hfrontier : ∀ v : EuclideanSpace ℝ (Fin k),
      multivariateGaussian v 1 (frontier Reg) = 0 := by
    intro v
    have hcompl : Reg = {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ^ 2 ≤ c}ᶜ := by
      ext z
      simp only [hRegdef, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    have hconv2 : Convex ℝ
        ((fun x => v + x) ⁻¹' {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ^ 2 ≤ c}) := by
      intro x hx y hy a₁ b₁ ha hb hab
      simp only [Set.mem_preimage] at hx hy ⊢
      have hv : a₁ • v + b₁ • v = v := by rw [← add_smul, hab, one_smul]
      have hkey : v + (a₁ • x + b₁ • y) = a₁ • (v + x) + b₁ • (v + y) := by
        rw [smul_add, smul_add,
          show a₁ • v + a₁ • x + (b₁ • v + b₁ • y)
            = (a₁ • v + b₁ • v) + (a₁ • x + b₁ • y) by abel, hv]
      rw [hkey]
      exact hCconv hx hy ha hb hab
    have htrans : (fun x : EuclideanSpace ℝ (Fin k) => v + x) ⁻¹'
        frontier {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ^ 2 ≤ c}
        = frontier ((fun x : EuclideanSpace ℝ (Fin k) => v + x) ⁻¹'
            {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ^ 2 ≤ c}) :=
      (Homeomorph.addLeft v).preimage_frontier _
    rw [hcompl, frontier_compl, mvGaussian_one_eq_map_add v,
      Measure.map_apply (by fun_prop) measurableSet_frontier, htrans,
      ← mvGaussian_zero_one_eq_stdGaussian]
    exact AsymptoticStatistics.multivariateGaussian_frontier_eq_zero_of_convex_posDef
      Matrix.PosDef.one hconv2
  -- ### The drifting local power limit
  set Shell : Set (EuclideanSpace ℝ (Fin k)) := {h | b ≤ ‖h‖ ∧ ‖h‖ ≤ B} with hShelldef
  set pwf : ℕ → EuclideanSpace ℝ (Fin k) → ℝ := fun n h =>
    power (Q n) (fun ω => if c < smoothStat ψ (X n) ω then (1 : ℝ) else 0) h with hpwf
  change Tendsto (fun n => sInf (pwf n '' Shell)) atTop (nhds _)
  have hdrift : ∀ (v : ℕ → EuclideanSpace ℝ (Fin k)) (h₀ : EuclideanSpace ℝ (Fin k)),
      Tendsto v atTop (nhds h₀) →
      Tendsto (fun n => pwf n (v n)) atTop
        (nhds ((noncentralChiSquared k (‖h₀‖ ^ 2).toNNReal (Set.Ioi c)).toReal)) := by
    intro v h₀ hv
    have hweak := scoreVec_weakConverges_drift hψ hortho hcentred hX hindep hlaw hv
    haveI hprob : ∀ n, IsProbabilityMeasure ((Q n (v n)).map (scoreVec ψ (X n))) := fun n =>
      Measure.isProbabilityMeasure_map (measurable_scoreVec hψmeas (hX n)).aemeasurable
    set μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) :=
      fun n => ⟨(Q n (v n)).map (scoreVec ψ (X n)), hprob n⟩ with hμs
    set νl : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) :=
      ⟨multivariateGaussian h₀ 1, inferInstance⟩ with hνl
    have hconv : Tendsto μs atTop (nhds νl) := by
      rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
      intro f
      simpa only [hμs, hνl, ProbabilityMeasure.coe_mk] using hweak f
    have hfront : (νl : Measure (EuclideanSpace ℝ (Fin k))) (frontier Reg) = 0 := by
      simp only [hνl, ProbabilityMeasure.coe_mk]
      exact hfrontier h₀
    have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv hfront
    have htoreal := (ENNReal.tendsto_toReal
      (measure_ne_top (νl : Measure (EuclideanSpace ℝ (Fin k))) Reg)).comp hport
    simp only [hμs, hνl, ProbabilityMeasure.coe_mk] at htoreal
    rw [hRegmass h₀] at htoreal
    exact htoreal.congr fun n => (hpwmap n (v n)).symm
  -- ### Elementary facts about the shell and the powers
  have hpwnn : ∀ n h, 0 ≤ pwf n h := by
    intro n h
    rw [hpwf]
    simp only [hpwmap n h]
    exact ENNReal.toReal_nonneg
  have hbdd : ∀ n, BddBelow (pwf n '' Shell) := by
    intro n
    exact ⟨0, fun x hx => by obtain ⟨h, _, rfl⟩ := hx; exact hpwnn n h⟩
  obtain ⟨h₁, hh₁⟩ : ∃ h : EuclideanSpace ℝ (Fin k), ‖h‖ = b := by
    refine ⟨b • EuclideanSpace.single (⟨0, hk⟩ : Fin k) (1 : ℝ), ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb, EuclideanSpace.norm_single, norm_one,
      mul_one]
  have hh₁mem : h₁ ∈ Shell := ⟨le_of_eq hh₁.symm, by rw [hh₁]; exact hbB.le⟩
  have hne : ∀ n, (pwf n '' Shell).Nonempty := fun n => ⟨pwf n h₁, ⟨h₁, hh₁mem, rfl⟩⟩
  have hShellcompact : IsCompact Shell := by
    have hclosed : IsClosed Shell := by
      have h1 : IsClosed {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖} :=
        isClosed_le continuous_const continuous_norm
      have h2 : IsClosed {h : EuclideanSpace ℝ (Fin k) | ‖h‖ ≤ B} :=
        isClosed_le continuous_norm continuous_const
      exact h1.inter h2
    refine (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin k)) B).of_isClosed_subset
      hclosed (fun h hh => ?_)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hh.2
  -- ### The two halves of the limit
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- `liminf ≥`: near-minimisers, compactness, and the drifting limit
    intro a' ha'
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    obtain ⟨φ, hφmono, hφ⟩ := Filter.extraction_of_frequently_atTop hcon
    have hchoice : ∀ n : ℕ, ∃ h, h ∈ Shell ∧
        pwf n h < sInf (pwf n '' Shell) + 1 / ((n : ℝ) + 1) := by
      intro n
      obtain ⟨x, hx, hlt⟩ := exists_lt_of_csInf_lt (hne n)
        (show sInf (pwf n '' Shell) < sInf (pwf n '' Shell) + 1 / ((n : ℝ) + 1) by
          have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith)
      obtain ⟨h, hh, rfl⟩ := hx
      exact ⟨h, hh, hlt⟩
    choose g hgS hglt using hchoice
    obtain ⟨h₀, hh₀S, ξ, hξmono, hξlim⟩ :=
      hShellcompact.tendsto_subseq (fun m : ℕ => hgS (φ m))
    set σ : ℕ → ℕ := fun m => φ (ξ m) with hσdef
    have hσmono : StrictMono σ := hφmono.comp hξmono
    set w : ℕ → EuclideanSpace ℝ (Fin k) :=
      fun n => if n ∈ Set.range σ then g n else h₀ with hwdef
    have hwσ : ∀ m, w (σ m) = g (σ m) := by
      intro m
      simp only [hwdef, if_pos (Set.mem_range.mpr ⟨m, rfl⟩)]
    have hwlim : Tendsto w atTop (nhds h₀) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      rw [Metric.tendsto_atTop] at hξlim
      obtain ⟨M, hM⟩ := hξlim ε hε
      refine ⟨σ M, fun n hn => ?_⟩
      by_cases hmem : n ∈ Set.range σ
      · obtain ⟨m, rfl⟩ := hmem
        have hmM : M ≤ m := by
          by_contra hc
          rw [not_le] at hc
          exact absurd hn (not_le.mpr (hσmono hc))
        rw [hwσ m]
        simpa only [Function.comp_apply, hσdef] using hM m hmM
      · rw [hwdef]
        simp only [if_neg hmem, dist_self]
        exact hε
    have hlimit := (hdrift w h₀ hwlim).comp hσmono.tendsto_atTop
    have hupper : Tendsto (fun m => a' + 1 / ((σ m : ℝ) + 1)) atTop (nhds a') := by
      have hσtop : Tendsto (fun m => ((σ m : ℝ) + 1)) atTop atTop :=
        Filter.tendsto_atTop_add_const_right _ 1
          (tendsto_natCast_atTop_atTop.comp hσmono.tendsto_atTop)
      have := Filter.Tendsto.div_atTop (f := fun _ : ℕ => (1 : ℝ)) tendsto_const_nhds hσtop
      simpa using tendsto_const_nhds.add this
    have hle : (noncentralChiSquared k (‖h₀‖ ^ 2).toNNReal (Set.Ioi c)).toReal ≤ a' := by
      refine le_of_tendsto_of_tendsto' hlimit hupper (fun m => ?_)
      have h1 := hglt (σ m)
      have h2 : sInf (pwf (σ m) '' Shell) ≤ a' := not_lt.mp (hφ (ξ m))
      simp only [Function.comp_apply, hwσ m]
      linarith
    have hmono : ((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal
        ≤ (noncentralChiSquared k (‖h₀‖ ^ 2).toNNReal (Set.Ioi c)).toReal := by
      exact ENNReal.toReal_mono (measure_ne_top _ _) (noncentralChiSquared_tail_mono k c
        (Real.toNNReal_mono (pow_le_pow_left₀ hb.le hh₀S.1 2)))
    linarith
  · -- `limsup ≤`: evaluate at a fixed inner-boundary point
    intro a' ha'
    have hlim := hdrift (fun _ => h₁) h₁ tendsto_const_nhds
    rw [hh₁] at hlim
    have hev := hlim.eventually (gt_mem_nhds ha')
    filter_upwards [hev] with n hn
    exact lt_of_le_of_lt (csInf_le (hbdd n) ⟨h₁, hh₁mem, rfl⟩) hn

/-- **The smooth test is asymptotically maximin.** For any radii `0 < b < B < ∞`, the
minimum power of the smooth test `1{Sₙ > c}` over the local alternatives `θ = h n^{-1/2}`
with `b ≤ |h| ≤ B` converges to `P{χ²_k(b²) > c_{k,1−α}}` (first conjunct); by
`smoothTest_maximin_upper_bound` it therefore maximizes the limiting minimum power among
all test sequences of asymptotic level `α` (second conjunct).

The worst case over the shell is asymptotically attained on its inner boundary `|h| = b`,
the noncentral chi-squared tail being increasing in the noncentrality parameter. -/
theorem smoothTest_asymptotically_maximin {k : ℕ} {α b B c : ℝ} {P₀ : Measure 𝓧}
    [IsProbabilityMeasure P₀] {ψ : Fin k → 𝓧 → ℝ}
    {Q : ℕ → EuclideanSpace ℝ (Fin k) → Measure Ω} [∀ n h, IsProbabilityMeasure (Q n h)]
    {X : (n : ℕ) → Fin n → Ω → 𝓧}
    -- USER-INPUT: at least one score direction
    (hk : 0 < k)
    -- USER-INPUT: the shell is nondegenerate and bounded (see the module docstring on
    -- removing the outer radius)
    (hb : 0 < b) (hbB : b < B)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c` is the `1 − α` quantile of `χ²_k`, i.e. the critical value
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    -- USER-INPUT: the vector of score functions is measurable; this is the certificate
    -- the exponential-family structure carries, and it implies measurability of each `ψⱼ`
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k)))
    -- USER-INPUT: the score functions are orthonormal in `L²(P₀)`; Neyman 1937
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    -- USER-INPUT: the score functions are orthogonal to the constants, i.e. `E₀ψⱼ = 0`
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    -- USER-INPUT: the null parameter is interior to the natural parameter set (full rank)
    (hint : (0 : EuclideanSpace ℝ (Fin k)) ∈ interior (smoothModel P₀ ψ hψ).natSet)
    -- USER-INPUT: at every stage and every local parameter each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: under every local parameter the observations are i.i.d.
    (hindep : ∀ n h, iIndepFun (X n) (Q n h))
    -- USER-INPUT: under the local parameter `h` the observations have law
    -- `p_{h n^{-1/2}}`, the smooth model at the local alternative
    (hlaw : ∀ n h, ∀ i, (Q n h).map (X n i)
      = (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h)) :
    Tendsto (fun n => sInf ((fun h => power (Q n)
          (fun ω => if c < smoothStat ψ (X n) ω then (1 : ℝ) else 0) h)
        '' {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖ ∧ ‖h‖ ≤ B})) atTop
        (nhds (((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal))
      ∧ ∀ ψtest : ℕ → Ω → ℝ, (∀ n, IsCriticalFn (ψtest n)) →
        -- REPAIRED: the competitors range over tests based on the sample; without this the
        -- second conjunct is FALSE, by the counterexample recorded at
        -- `smoothTest_maximin_upper_bound`
        (∀ n, ∃ ρ : (Fin n → 𝓧) → ℝ,
          Measurable ρ ∧ ∀ ω, ψtest n ω = ρ (fun i => X n i ω)) →
        Tendsto (fun n => power (Q n) (ψtest n) 0) atTop (nhds α) →
        limsup (fun n => sInf ((fun h => power (Q n) (ψtest n) h) ''
            {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖ ∧ ‖h‖ ≤ B})) atTop
          ≤ ((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal := by
  refine ⟨?_, ?_⟩
  · -- Attainment on the shell: the drifting-parameter local limit half.
    exact smoothTest_shell_minPower_tendsto hk hb hbB hα hα1 hc hψ hortho hcentred hint
      hX hindep hlaw
  · -- Optimality: for any level-`α` test this is exactly `smoothTest_maximin_upper_bound`.
    intro ψtest hψt hψX hlvl
    exact smoothTest_maximin_upper_bound hk hb hbB hα hα1 hc hψ hortho hcentred hint
      hX hindep hlaw hψt hψX hlvl

end StatLean.HypothesisTesting
