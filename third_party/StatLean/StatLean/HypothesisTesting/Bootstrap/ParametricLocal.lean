module
public import StatLean.HypothesisTesting.Bootstrap.Consistency
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# The parametric bootstrap: plug-in at an estimated parameter, and local power

In a parametric model indexed by `θ` in a finite-dimensional parameter space, the bootstrap
substitutes an estimator `thHat n` for the unknown `θ` inside the sampling distribution
`Jpar n θ` of a root. Consistency here is a statement **in probability**, not almost surely:
the estimated parameter sequence does not stay inside any fixed local class with probability
one, only along suitably chosen subsequences.

This file contains:

* `tendsto_supCDFDist_parametric_fixed` — uniform convergence of the sampling distribution at
  the true parameter to the limit law;
* `tendstoInMeasure_supCDFDist_parametric_plugIn` — the plug-in display: the sampling
  distribution at the estimated parameter is uniformly close, in probability, to the one at the
  true parameter;
* `tendstoInMeasure_supCDFDist_parametric_bootstrap` — the two displays combined;
* `tendsto_bootstrapTest_local_power` — the limiting power of the bootstrap test against
  contiguous alternatives `θ + n^{-1/2} hdir`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 18 (Bootstrap and
Subsampling Methods), §18.3 (Bootstrap Sampling Distributions), Theorem 18.3.2 (the uniform
consistency form, applied to a plug-in at an estimated parameter) and Corollary 18.3.1
(bootstrap test local power). (`TSH4 §18.3 Thm 18.3.2, Cor 18.3.1`.)

**Designed deviation (subsequence route replaces the almost sure representation).** The
reference argument passes to an almost sure representation: it constructs, on a new probability
space, a copy of the estimator that converges almost surely, concludes the almost sure version
of the display for the copy, and transfers the conclusion back because the two estimators have
the same law. Constructing that representation is a substantial piece of machinery. We instead
take the **local uniformity over compact sets of local parameters** as the explicit hypothesis
(`hlocunif` below: convergence of the sampling distribution is uniform over parameters
`θ + n^{-1/2} t` with `‖t‖ ≤ M`) and drive the conclusion by the subsequence characterisation of
convergence in probability. The two routes prove the same display; the hypothesis we assume is
exactly the local uniformity that the reference derives from its local asymptotic theory.

**Designed deviation (tightness rather than bare consistency).** Mere consistency
`thHat n → θ` in probability does **not** activate a compact-`t` local uniformity hypothesis:
the estimator may leave every `n^{-1/2}`-neighbourhood of `θ`. The reference setup supplies
`n^{1/2}`-consistency through the efficiency of the estimator it uses. We therefore state the
honest input — uniform tightness of `n^{1/2}(thHat n − θ)` — which implies consistency and is
what the argument consumes.

**Proof formalization notes.**
* Convergence in probability of the uniform distance is `TendstoInMeasure` against the constant
  function `0`; the underlying distance on `ℝ` is the usual one.
* The local-uniformity hypothesis is stated in eventually-`∀`-`ε` form rather than as a
  supremum over a compact set, which avoids the junk value of a supremum over an index type
  that is not known to be nonempty.
* In `tendsto_bootstrapTest_local_power` the two hypotheses `hlocalCLT` and `hcritval` are
  **not** free-choice inputs: they are the local limit theory of the estimator under contiguous
  alternatives, and the convergence of the estimated critical value under those alternatives.
  They are recorded here as explicit hypotheses only because the local-asymptotics layer of
  this area is developed in a separate module; when that layer lands they must be discharged
  from it rather than supplied by callers. They are flagged as such on their tags.

**Bibliographic comments.** The bootstrap is due to B. Efron ("Bootstrap methods: another look
at the jackknife," *Ann. Statist.* **7** (1979), 1–26). The class-of-sequences formulation of
consistency and the systematic study of bootstrap tests and their local power follow R. Beran
("Bootstrap methods in statistics," *Jahresber. Deutsch. Math.-Verein.* **86** (1984), 14–30)
and D. N. Politis, J. P. Romano and M. Wolf, *Subsampling*, Springer, 1999. Higher-order
properties of the parametric bootstrap are treated in P. Hall, *The Bootstrap and Edgeworth
Expansion*, Springer, 1992.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace StatLean.HypothesisTesting

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}

section ParametricBootstrap

variable {Pr : Measure Ω} [IsProbabilityMeasure Pr]
  {Jpar : ℕ → EuclideanSpace ℝ (Fin k) → ℝ → ℝ} {Jlim : EuclideanSpace ℝ (Fin k) → ℝ → ℝ}
  {θ : EuclideanSpace ℝ (Fin k)} {thHat : ℕ → Ω → EuclideanSpace ℝ (Fin k)}

/-- Reduce convergence in measure to `0` to the real-`ε` measure of the excess set
`{ω | ε ≤ |f n ω|}`. -/
private theorem tendstoInMeasure_absOf {f : ℕ → Ω → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => Pr {ω | ε ≤ |f n ω|}) atTop (𝓝 (0 : ℝ≥0∞))) :
    TendstoInMeasure Pr f atTop (fun _ => 0) := by
  refine tendstoInMeasure_of_ne_top (fun ε hε hε_top => ?_)
  lift ε to ℝ≥0 using hε_top
  rw [ENNReal.coe_pos, ← NNReal.coe_pos] at hε
  have hiff : ∀ a : ℝ, ((ε : ℝ≥0∞) ≤ edist a (0 : ℝ)) ↔ ((ε : ℝ) ≤ |a|) := by
    intro a
    rw [edist_dist, Real.dist_eq, sub_zero, ← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_le_ofReal_iff (abs_nonneg a)]
  simp only [hiff]
  exact h (ε : ℝ) hε

/-- **Sampling distribution at the true parameter converges uniformly to the limit law.**

Pointwise convergence of the sampling distribution functions at the fixed parameter `θ`,
together with continuity of the limit law, gives uniform convergence. -/
theorem tendsto_supCDFDist_parametric_fixed
    -- USER-INPUT: each sampling distribution is a distribution function
    (hcdf : ∀ n : ℕ, IsCDF (Jpar n θ))
    -- USER-INPUT: the limit law is a distribution function
    (hlim_cdf : IsCDF (Jlim θ))
    -- USER-INPUT: the limit law is continuous; the exact continuity requirement behind the
    -- upgrade from pointwise to uniform convergence
    (hlim_cont : Continuous (Jlim θ))
    -- USER-INPUT: pointwise convergence of the sampling distribution functions at `θ`
    (hptwise : ∀ x : ℝ, Tendsto (fun n => Jpar n θ x) atTop (𝓝 (Jlim θ x))) :
    Tendsto (fun n => supCDFDist (Jpar n θ) (Jlim θ)) atTop (𝓝 0) :=
  tendsto_supCDFDist_zero hcdf hlim_cont hlim_cdf hptwise

/-- **Plug-in display for the parametric bootstrap.**

If the sampling distribution converges to the limit law uniformly over parameters in
`n^{-1/2}`-neighbourhoods of `θ` of bounded rescaled radius, and if `n^{1/2}(thHat n − θ)` is
uniformly tight, then substituting the estimator for the true parameter perturbs the sampling
distribution by a uniformly negligible amount, in probability.

**Signature amendment (the limit law must be a distribution function).** As frozen — with
`hlim_cont` as the only hypothesis on `Jlim θ` — the statement is **false**, and the added
`hlim_cdf : IsCDF (Jlim θ)` is exactly what repairs it. The reason is the junk value of an
unbounded real supremum: `supCDFDist F G = ⨆ t, |F t − G t|` is `0` whenever that family is
unbounded (`Real.iSup_of_not_bddAbove`), so for an unbounded *continuous* `Jlim θ` every
`supCDFDist (·) (Jlim θ)` collapses to `0` and `hlocunif` becomes vacuous while the conclusion
still has content. Concretely, take `k = 1`, `θ = 0`, `Jlim θ = id` (continuous, unbounded),
`Jpar n t x = stdNormalCDF (x − n^{1/2} t)` (a genuine distribution function for every `n, t`)
and the deterministic estimator `thHat n ω = n^{-1/2}`. Then `n^{1/2}(thHat n − θ) ≡ 1` is
tight, `hlocunif` holds vacuously, and yet
`supCDFDist (Jpar n (thHat n ω)) (Jpar n θ)` is the (positive, `n`-independent) Kolmogorov
distance between the `N(1,1)` and `N(0,1)` distribution functions, so it does not tend to `0`.
The hypothesis is already carried by the downstream sibling
`tendstoInMeasure_supCDFDist_parametric_bootstrap`, so no application is weakened. -/
theorem tendstoInMeasure_supCDFDist_parametric_plugIn
    -- USER-INPUT: local uniformity over compact sets of local parameters — convergence of the
    -- sampling distribution to the limit law, uniform over `θ + n^{-1/2} t` with `‖t‖ ≤ M`
    (hlocunif : ∀ M : ℝ, 0 < M → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t : EuclideanSpace ℝ (Fin k), ‖t‖ ≤ M →
        supCDFDist (Jpar n (θ + (Real.sqrt n)⁻¹ • t)) (Jlim θ) ≤ ε)
    -- USER-INPUT: uniform tightness of the rescaled estimation error; strictly stronger than
    -- consistency and exactly what the local uniformity above consumes
    (htight : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧
      ∀ n : ℕ, (Pr {ω | M < ‖Real.sqrt n • (thHat n ω - θ)‖}).toReal ≤ ε)
    -- USER-INPUT: every sampling distribution is a distribution function
    (hcdf : ∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin k)), IsCDF (Jpar n t))
    -- USER-INPUT (signature amendment): the limit law is a distribution function; without it
    -- `hlocunif` is vacuous and the statement is false — see the docstring
    (hlim_cdf : IsCDF (Jlim θ))
    -- USER-INPUT: the limit law is continuous
    (hlim_cont : Continuous (Jlim θ))
    -- LEAN-ONLY: the estimator is measurable; needed for the tightness sets and the conclusion
    -- to carry their measures
    (hmeas : ∀ n, Measurable (thHat n)) :
    TendstoInMeasure Pr (fun n ω => supCDFDist (Jpar n (thHat n ω)) (Jpar n θ)) atTop
      (fun _ => 0) := by
  -- The bridge is the limit law: on the high-probability event `‖√n(θ̂ − θ)‖ ≤ M` both `Jpar n θ̂`
  -- and `Jpar n θ` (the local parameter `t = 0`) are within `ε/2` of `Jlim θ`.
  refine tendstoInMeasure_absOf (fun ε hε => ?_)
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨δ₀, hδ₀pos, hδ₀δ⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ENNReal.ofReal δ₀ ≤ δ := by
    rcases eq_or_ne δ ∞ with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨δ.toReal, ENNReal.toReal_pos hδ.ne' h, by rw [ENNReal.ofReal_toReal h]⟩
  obtain ⟨M, hMpos, htightM⟩ := htight δ₀ hδ₀pos
  filter_upwards [hlocunif M hMpos (ε / 4) (by positivity), eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have hn0 : 0 < n := by omega
    exact_mod_cast hn0
  have hsqrtne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
  -- the sampling distribution at the true parameter is the local parameter `t = 0`
  have hb0 : supCDFDist (Jpar n θ) (Jlim θ) ≤ ε / 4 := by
    have h0 := hn 0 (by simpa using hMpos.le)
    simpa using h0
  refine le_trans (measure_mono (?_ : _ ⊆
    {ω | M < ‖Real.sqrt (n : ℝ) • (thHat n ω - θ)‖})) ?_
  · intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_contra hcon
    push_neg at hcon
    set v := Real.sqrt (n : ℝ) • (thHat n ω - θ) with hv
    have hthHat : θ + (Real.sqrt (n : ℝ))⁻¹ • v = thHat n ω := by
      rw [hv, smul_smul, inv_mul_cancel₀ hsqrtne, one_smul, add_sub_cancel]
    have hb1 : supCDFDist (Jpar n (thHat n ω)) (Jlim θ) ≤ ε / 4 := by
      rw [← hthHat]; exact hn v hcon
    have htri : supCDFDist (Jpar n (thHat n ω)) (Jpar n θ)
        ≤ supCDFDist (Jpar n (thHat n ω)) (Jlim θ) + supCDFDist (Jlim θ) (Jpar n θ) :=
      supCDFDist_triangle_of_isCDF (hcdf n (thHat n ω)) hlim_cdf (hcdf n θ)
    rw [supCDFDist_comm] at hb0
    rw [abs_of_nonneg (supCDFDist_nonneg (hcdf n (thHat n ω)) (hcdf n θ))] at hω
    linarith
  · rw [← ENNReal.ofReal_toReal (measure_ne_top Pr _)]
    exact le_trans (ENNReal.ofReal_le_ofReal (htightM n)) hδ₀δ

/-- **Parametric bootstrap consistency**, the two displays combined: the sampling distribution
at the estimated parameter is uniformly close, in probability, to the limit law. -/
theorem tendstoInMeasure_supCDFDist_parametric_bootstrap
    -- USER-INPUT: local uniformity over compact sets of local parameters
    (hlocunif : ∀ M : ℝ, 0 < M → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t : EuclideanSpace ℝ (Fin k), ‖t‖ ≤ M →
        supCDFDist (Jpar n (θ + (Real.sqrt n)⁻¹ • t)) (Jlim θ) ≤ ε)
    -- USER-INPUT: uniform tightness of the rescaled estimation error
    (htight : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧
      ∀ n : ℕ, (Pr {ω | M < ‖Real.sqrt n • (thHat n ω - θ)‖}).toReal ≤ ε)
    -- USER-INPUT: every sampling distribution is a distribution function
    (hcdf : ∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin k)), IsCDF (Jpar n t))
    -- USER-INPUT: the limit law is a distribution function and is continuous
    (hlim_cdf : IsCDF (Jlim θ)) (hlim_cont : Continuous (Jlim θ))
    -- LEAN-ONLY: measurability of the estimator
    (hmeas : ∀ n, Measurable (thHat n)) :
    TendstoInMeasure Pr (fun n ω => supCDFDist (Jpar n (thHat n ω)) (Jlim θ)) atTop
      (fun _ => 0) := by
  -- Direct: on the high-probability event `‖√n(θ̂ − θ)‖ ≤ M`, the estimator is a local parameter,
  -- so `hlocunif` bounds the sampling distribution's distance to the limit law directly.
  refine tendstoInMeasure_absOf (fun ε hε => ?_)
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨δ₀, hδ₀pos, hδ₀δ⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ENNReal.ofReal δ₀ ≤ δ := by
    rcases eq_or_ne δ ∞ with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨δ.toReal, ENNReal.toReal_pos hδ.ne' h, by rw [ENNReal.ofReal_toReal h]⟩
  obtain ⟨M, hMpos, htightM⟩ := htight δ₀ hδ₀pos
  filter_upwards [hlocunif M hMpos (ε / 2) (by positivity), eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have hn0 : 0 < n := by omega
    exact_mod_cast hn0
  have hsqrtne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
  refine le_trans (measure_mono (?_ : _ ⊆
    {ω | M < ‖Real.sqrt (n : ℝ) • (thHat n ω - θ)‖})) ?_
  · intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_contra hcon
    push_neg at hcon
    set v := Real.sqrt (n : ℝ) • (thHat n ω - θ) with hv
    have hthHat : θ + (Real.sqrt (n : ℝ))⁻¹ • v = thHat n ω := by
      rw [hv, smul_smul, inv_mul_cancel₀ hsqrtne, one_smul, add_sub_cancel]
    have hb1 : supCDFDist (Jpar n (thHat n ω)) (Jlim θ) ≤ ε / 2 := by
      rw [← hthHat]; exact hn v hcon
    rw [abs_of_nonneg (supCDFDist_nonneg (hcdf n (thHat n ω)) hlim_cdf)] at hω
    linarith
  · rw [← ENNReal.ofReal_toReal (measure_ne_top Pr _)]
    exact le_trans (ENNReal.ofReal_le_ofReal (htightM n)) hδ₀δ

/-- **Limiting local power of the bootstrap test.**

Test `g(θ) = 0` against `g(θ) > 0` by rejecting when `n^{1/2} g(thHat n)` exceeds the estimated
`1 − α` quantile. Against the contiguous alternatives `θ + n^{-1/2} hdir` the rejection
probability converges to `1 − Φ(z_{1−α} − σ⁻¹ ⟪∇g(θ), hdir⟫)`, where `σ²` is the variance of
the limiting law of the root at `θ`.

**Signature amendment (two `LEAN-ONLY` measurability hypotheses).** The rejection event is the
*complement* of `{n^{1/2} g(thHat n) ≤ ĉₙ}`, and the hypotheses `hlocalCLT`/`hcritval` control
only events of the form `{· ≤ x}` and `{ε ≤ |·|}`. Passing to the complement needs
`measure_compl`, hence measurability of the rejection region: for a non-measurable set `A` the
Mathlib `Measure` is the outer-measure extension and `μ A + μ Aᶜ > μ univ` is possible, so the
complement step is not available without it. The two hypotheses added are the ones the siblings
of this cluster (`tendsto_bootstrapCoverage`, `tendsto_bootstrapTest_level`) already carry, and
they are pure regularity: no probabilistic content is imported. -/
theorem tendsto_bootstrapTest_local_power
    {Pn : ℕ → EuclideanSpace ℝ (Fin k) → Measure Ω} {g : EuclideanSpace ℝ (Fin k) → ℝ}
    {gradg hdir : EuclideanSpace ℝ (Fin k)} {sigma α : ℝ}
    -- USER-INPUT: the laws of the data of each sample size and each parameter value
    (hPn : ∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure (Pn n t))
    -- USER-INPUT: nominal level strictly between `0` and `1`
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    -- USER-INPUT: the tested parameter lies on the boundary of the null hypothesis
    (hg0 : g θ = 0)
    -- USER-INPUT: `g` is differentiable at `θ` with gradient `gradg`
    (hgrad : HasGradientAt g gradg θ)
    -- USER-INPUT: the gradient does not vanish, so the limiting law of the root is nondegenerate
    (hgrad_ne : gradg ≠ 0)
    -- USER-INPUT: positive limiting standard deviation of the root at `θ`
    (hsigma : 0 < sigma)
    -- USER-INPUT: the limit law of the root at `θ` is centred normal with variance `sigma ^ 2`
    (hJlim_eq : ∀ x : ℝ, Jlim θ x = normalCDF 0 (Real.toNNReal (sigma ^ 2)) x)
    -- USER-INPUT: under the contiguous alternatives the rescaled test statistic is
    -- asymptotically normal, centred at the directional derivative. NOT a free choice —
    -- supplied by the local-asymptotics layer; see the file's proof formalization notes
    (hlocalCLT : ∀ x : ℝ, Tendsto (fun n : ℕ =>
        ((Pn n (θ + (Real.sqrt n)⁻¹ • hdir))
          {ω | Real.sqrt n * g (thHat n ω) - ⟪gradg, hdir⟫ ≤ x}).toReal) atTop
        (𝓝 (normalCDF 0 (Real.toNNReal (sigma ^ 2)) x)))
    -- USER-INPUT: under the contiguous alternatives the estimated critical value converges in
    -- probability to the critical value of the limit law. NOT a free choice — supplied by the
    -- plug-in theorem above with contiguity; see the file's proof formalization notes
    (hcritval : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
        ((Pn n (θ + (Real.sqrt n)⁻¹ • hdir))
          {ω | ε ≤ |cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α)
                - sigma * stdNormalQuantile (1 - α)|}).toReal) atTop (𝓝 0))
    -- LEAN-ONLY (signature amendment): the test statistic is measurable in the sample
    (hstatmeas : ∀ n : ℕ, Measurable fun ω => Real.sqrt n * g (thHat n ω))
    -- LEAN-ONLY (signature amendment): the estimated critical value is measurable in the sample
    (hcritmeas : ∀ n : ℕ, Measurable fun ω =>
      cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α)) :
    Tendsto (fun n : ℕ =>
        ((Pn n (θ + (Real.sqrt n)⁻¹ • hdir))
          {ω | cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α) < Real.sqrt n * g (thHat n ω)}).toReal)
      atTop
      (𝓝 (1 - stdNormalCDF (stdNormalQuantile (1 - α) - sigma⁻¹ * ⟪gradg, hdir⟫))) := by
  haveI hprob : ∀ n : ℕ, IsProbabilityMeasure (Pn n (θ + (Real.sqrt n)⁻¹ • hdir)) :=
    fun n => hPn n _
  have hvne : Real.toNNReal (sigma ^ 2) ≠ 0 :=
    (Real.toNNReal_pos.mpr (by positivity)).ne'
  -- The limiting threshold: the critical value of the limit law, recentred by the drift.
  have hFcont : ContinuousAt (normalCDF 0 (Real.toNNReal (sigma ^ 2)))
      (sigma * stdNormalQuantile (1 - α) - ⟪gradg, hdir⟫) :=
    (continuous_normalCDF 0 hvne).continuousAt
  -- Convergence in probability of the recentred critical values is `hcritval` verbatim: the two
  -- drifts cancel.
  have hcconv : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
      ((Pn n (θ + (Real.sqrt n)⁻¹ • hdir))
        {ω | ε ≤ |(cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α) - ⟪gradg, hdir⟫)
          - (sigma * stdNormalQuantile (1 - α) - ⟪gradg, hdir⟫)|}).toReal) atTop (𝓝 0) := by
    intro ε hε
    have hsets : ∀ n : ℕ,
        {ω | ε ≤ |(cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α) - ⟪gradg, hdir⟫)
            - (sigma * stdNormalQuantile (1 - α) - ⟪gradg, hdir⟫)|}
          = {ω | ε ≤ |cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α)
            - sigma * stdNormalQuantile (1 - α)|} := by
      intro n
      ext ω
      simp only [Set.mem_setOf_eq, sub_sub_sub_cancel_right]
    simp only [hsets]
    exact hcritval ε hε
  -- The Slutsky coupling: the statistic against the estimated critical value.
  have hmain := tendsto_measure_le_of_tendsto_cdf
    (μ := fun n : ℕ => Pn n (θ + (Real.sqrt n)⁻¹ • hdir))
    (S := fun (n : ℕ) ω => Real.sqrt n * g (thHat n ω) - ⟪gradg, hdir⟫)
    (c := fun (n : ℕ) ω =>
      cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α) - ⟪gradg, hdir⟫)
    hFcont hlocalCLT hcconv
  -- The rejection event is the complement of the acceptance event.
  have hrej : ∀ n : ℕ,
      {ω | cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α) < Real.sqrt n * g (thHat n ω)}
        = {ω | Real.sqrt n * g (thHat n ω) - ⟪gradg, hdir⟫
            ≤ cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α) - ⟪gradg, hdir⟫}ᶜ := by
    intro n
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le, sub_lt_sub_iff_right]
  have hmeasA : ∀ n : ℕ, MeasurableSet
      {ω | Real.sqrt n * g (thHat n ω) - ⟪gradg, hdir⟫
        ≤ cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α) - ⟪gradg, hdir⟫} :=
    fun n => measurableSet_le ((hstatmeas n).sub measurable_const)
      ((hcritmeas n).sub measurable_const)
  have hcompl : ∀ n : ℕ,
      ((Pn n (θ + (Real.sqrt n)⁻¹ • hdir))
        {ω | cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α)
          < Real.sqrt n * g (thHat n ω)}).toReal
        = 1 - ((Pn n (θ + (Real.sqrt n)⁻¹ • hdir))
          {ω | Real.sqrt n * g (thHat n ω) - ⟪gradg, hdir⟫
            ≤ cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α) - ⟪gradg, hdir⟫}).toReal := by
    intro n
    rw [hrej n, measure_compl (hmeasA n) (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top _ _),
      measure_univ, ENNReal.toReal_one]
  -- Identify the limit through the standardisation of the normal distribution function.
  have hval : normalCDF 0 (Real.toNNReal (sigma ^ 2))
      (sigma * stdNormalQuantile (1 - α) - ⟪gradg, hdir⟫)
      = stdNormalCDF (stdNormalQuantile (1 - α) - sigma⁻¹ * ⟪gradg, hdir⟫) := by
    rw [normalCDF_sq_eq_stdNormalCDF hsigma]
    congr 1
    field_simp
  have hlim := Tendsto.const_sub 1 hmain
  rw [hval] at hlim
  exact Tendsto.congr (fun n => (hcompl n).symm) hlim

end ParametricBootstrap

end StatLean.HypothesisTesting
