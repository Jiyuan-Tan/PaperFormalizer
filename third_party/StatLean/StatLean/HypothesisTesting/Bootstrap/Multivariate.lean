module
public import StatLean.HypothesisTesting.Bootstrap.NonparametricMean
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# The multivariate bootstrap: mean vectors and smooth functions of means

The mean of a law on the line is replaced by the mean **vector** of a law on `ℝᵏ`. Two
consequences follow. First, the root can be built from the vector by any norm, and the bootstrap
handles every norm at once — the analytic approximation would have to be redone for each.
Second, once mean vectors are available, so is every parameter obtained by applying a smooth map
to a vector of expectations, through the delta method.

This file contains:

* `covMatrix`, `meanVecSeqClass`, `meanVecRootLaw`, `normLimitCDF`, `normMeanRootCDF` — the
  multivariate carriers;
* `meanVec_root_tendsto` — the multivariate limit law along the class;
* `norm_root_cdf_tendsto`, `continuous_normLimitCDF` — the limit law of the norm of the root;
* `bootstrap_meanVec_consistent` — almost sure consistency of the bootstrap for the mean vector;
* `meanStatistic`, `bootstrapLaw` — the plug-in statistic and the resampling law;
* `smooth_function_of_means_tendsto` — the delta-method limit for smooth functions of means;
* `bootstrap_smooth_function_consistent` — almost sure bootstrap consistency for those
  functions, in the two forms stated for them: closeness of the resampled law to the sampling
  law, and uniform closeness of the distribution functions of the norm.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 18 (Bootstrap and
Subsampling Methods), §18.3 (Bootstrap Sampling Distributions), Theorem 18.3.5 (the
multivariate bootstrap) and Theorem 18.3.6 (smooth functions of means), §18.3.3 (Further
Examples). (`TSH4 §18.3 Thm 18.3.5, Thm 18.3.6`.)

**Designed deviation (metric-free formulation).** Closeness of two laws on `ℝᵏ` is classically
expressed through a metric metrizing weak convergence (bounded-Lipschitz, Lévy–Prokhorov, …).
We keep the metric out of the statements: weak convergence is written as convergence of
integrals of bounded continuous functions, and the displays that the reference states in a
metric are rendered either in that form or — where the reference itself supplies a supremum over
a real argument — in the frozen `supCDFDist`. No metric on the space of measures is introduced.

**Deviation from the reference class (mean-vector convergence).** The reference defines the
multivariate class by weak convergence together with entrywise convergence of the covariance
matrices, and proves the limit law by reduction to the univariate mean case. That reduction
consumes convergence of the **mean vectors** as well: along a direction, the univariate class
requires the means to converge. We therefore include mean-vector convergence in
`meanVecSeqClass`. The empirical sequence satisfies it by the strong law, so no application is
weakened.

**Proof formalization notes.**
* Part (i) is the Cramér–Wold reduction of the multivariate limit to the univariate one: the
  image of `meanVecRootLaw` under `⟪t, ·⟫` is the univariate root law of the image sequence
  (`meanVecRootLaw_map_inner`), so the triangular-array central limit theorem with a drifting
  row law (`NonparametricMean.tendsto_meanRootLaw`) applies in each direction; the directions
  are recombined by Lévy's continuity theorem
  (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`) after identifying the limits through
  `charFun_gaussianReal` and `charFun_multivariateGaussian`. Degenerate directions
  (`tᵀ Σ t = 0`) are covered: the univariate theorem allows a vanishing limiting variance.
* Part (ii) is the continuous mapping theorem for the norm: a norm is continuous everywhere, and
  the spheres of a norm are null for the limit law — `measure_multivariateGaussian_norm_level`,
  proved by writing the Gaussian as the image of the standard Gaussian under `√Σ`, which turns
  the norm into a (possibly degenerate) seminorm whose level sets are frontiers of convex sets
  and hence Lebesgue-null, and transporting through `stdGaussian ≪ volume`. Continuity of the
  limiting distribution function is recorded separately as `continuous_normLimitCDF`, since the
  almost sure part needs it to run the uniform (Pólya) step.
* Part (iii) is the general sequence-class criterion applied to the empirical sequence. Its
  membership (`empirical_mem_meanVecSeqClass`) needs no separate Glivenko–Cantelli theorem: the
  characteristic functions of the empirical measures are sample averages of bounded functions,
  so the strong law gives their convergence along a countable dense set of directions, the
  strong law for `‖·‖` makes the family equi-Lipschitz in the direction, and Lévy's theorem
  upgrades this to weak convergence.
* The norm is passed as data with the three defining hypotheses (subadditive, absolutely
  homogeneous, positive definite) rather than as a `NormedAddCommGroup` instance, because the
  statement quantifies over norms on a space that already carries its Euclidean one.
* Coordinates of `EuclideanSpace` are read through `WithLp.ofLp` and built through
  `WithLp.toLp`; the space is a structure over the underlying function type in this pin, so
  bare lambdas do not typecheck.

**Bibliographic comments.** The bootstrap is due to B. Efron ("Bootstrap methods: another look
at the jackknife," *Ann. Statist.* **7** (1979), 1–26); the multivariate theory to P. J. Bickel
and D. A. Freedman ("Some asymptotic theory for the bootstrap," *Ann. Statist.* **9** (1981),
1196–1217) and K. Singh ("On the asymptotic accuracy of Efron's bootstrap," *Ann. Statist.* **9**
(1981), 1187–1195). Confidence sets for a multivariate distribution built from the bootstrap,
and the balancing of simultaneous intervals, are due to R. Beran ("Bootstrap methods in
statistics," *Jahresber. Deutsch. Math.-Verein.* **86** (1984), 14–30) and R. Beran and
P. W. Millar ("Confidence sets for a multivariate distribution," *Ann. Statist.* **14** (1986),
431–443); see also D. N. Politis, J. P. Romano and M. Wolf, *Subsampling*, Springer, 1999, and
P. Hall, *The Bootstrap and Edgeworth Expansion*, Springer, 1992.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StatLean.HypothesisTesting

variable {Ω 𝓢 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓢] {k p q : ℕ}

/-! ## Carriers for the mean vector -/

/-- The **covariance matrix** of a law on `ℝᵏ`, entry by entry. -/
noncomputable def covMatrix (F : Measure (EuclideanSpace ℝ (Fin k))) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    cov[fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y i,
        fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y j; F]

/-- The **sequence class for the mean-vector problem**: sequences of laws on `ℝᵏ` converging
weakly to `Q` — tested against bounded continuous functions — with mean vectors and covariance
matrices converging entrywise to those of `Q`. The `n = 0` entry is left unconstrained, as in
the univariate class. -/
def meanVecSeqClass (Q : Measure (EuclideanSpace ℝ (Fin k))) :
    Set (ℕ → Measure (EuclideanSpace ℝ (Fin k))) :=
  {F | (∀ n : ℕ, 0 < n → IsProbabilityMeasure (F n)) ∧
    (∀ n : ℕ, MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 (F n)) ∧
    (∀ f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ,
      Tendsto (fun n => ∫ y, f y ∂(F n)) atTop (𝓝 (∫ y, f y ∂Q))) ∧
    (∀ i : Fin k, Tendsto (fun n => ∫ y, WithLp.ofLp y i ∂(F n)) atTop
      (𝓝 (∫ y, WithLp.ofLp y i ∂Q))) ∧
    (∀ i j : Fin k, Tendsto (fun n => covMatrix (F n) i j) atTop (𝓝 (covMatrix Q i j)))}

/-- The **law of the centred and scaled sample mean vector** under `n` independent draws
from `F`. -/
noncomputable def meanVecRootLaw (F : Measure (EuclideanSpace ℝ (Fin k))) (n : ℕ) :
    Measure (EuclideanSpace ℝ (Fin k)) :=
  (Measure.pi fun _ : Fin n => F).map
    fun y => Real.sqrt n • ((n : ℝ)⁻¹ • (∑ i, y i) - ∫ z, z ∂F)

/-- The **limiting distribution function of the norm** of a centred Gaussian vector with
covariance `S`, for the norm `nrm`. -/
noncomputable def normLimitCDF (S : Matrix (Fin k) (Fin k) ℝ)
    (nrm : EuclideanSpace ℝ (Fin k) → ℝ) (x : ℝ) : ℝ :=
  ((multivariateGaussian 0 S) {z | nrm z ≤ x}).toReal

/-- The **sampling distribution function of the norm** of the centred and scaled sample mean
vector under `n` independent draws from `F`. -/
noncomputable def normMeanRootCDF (F : Measure (EuclideanSpace ℝ (Fin k)))
    (nrm : EuclideanSpace ℝ (Fin k) → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((meanVecRootLaw F n) {z | nrm z ≤ x}).toReal

/-! ## Analytic infrastructure for the norm of a Gaussian vector

The limiting distribution function of a norm of the Gaussian limit is continuous because the
spheres of the norm are null for the limit law. The chain of facts below establishes that,
degeneracy of the covariance included: the Gaussian is the image of the standard Gaussian under
the square root of the covariance, that image turns the norm into a **seminorm** `g`, the level
sets of a nonzero seminorm are frontiers of convex sets and hence Lebesgue-null, and the standard
Gaussian is absolutely continuous with respect to the volume. -/

section NormOfGaussian

/-- Absolute continuity is inherited by finite powers of a measure on the line. Mathlib
v4.29.1 has `Measure.AbsolutelyContinuous.prod` for binary products but no `Measure.pi`
counterpart; this is the induction that turns one into the other. -/
private lemma pi_absolutelyContinuous_pi {μ ν : Measure ℝ} [SigmaFinite μ] [SigmaFinite ν]
    (h : μ ≪ ν) (n : ℕ) :
    (Measure.pi fun _ : Fin n => μ) ≪ (Measure.pi fun _ : Fin n => ν) := by
  induction n with
  | zero =>
      rw [Measure.pi_of_empty (fun _ : Fin 0 => μ), Measure.pi_of_empty (fun _ : Fin 0 => ν)]
  | succ n ih =>
      have hμ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      have hν := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).symm
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      rw [← hμ.map_eq, ← hν.map_eq]
      exact (h.prod ih).map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.measurable

/-- The standard Gaussian measure on a Euclidean space is absolutely continuous with respect to
the volume: it is the image under `WithLp.toLp` of a product of one-dimensional Gaussians, and
`WithLp.toLp` also transports the volume to the volume. -/
private lemma stdGaussian_absolutelyContinuous_volume (k : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))) ≪ (volume : Measure (EuclideanSpace ℝ (Fin k))) := by
  have h1 : (stdGaussian (EuclideanSpace ℝ (Fin k)))
      = (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (WithLp.toLp 2) :=
    map_pi_eq_stdGaussian.symm
  have h2 : (volume : Measure (EuclideanSpace ℝ (Fin k)))
      = (Measure.pi fun _ : Fin k => (volume : Measure ℝ)).map (WithLp.toLp 2) := by
    rw [← volume_pi]
    exact (PiLp.volume_preserving_toLp (Fin k)).map_eq.symm
  rw [h1, h2]
  exact (pi_absolutelyContinuous_pi (gaussianReal_absolutelyContinuous 0 one_ne_zero) k).map
    (PiLp.volume_preserving_toLp (Fin k)).measurable

section Seminorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An absolutely homogeneous functional vanishes at the origin. -/
private lemma seminorm_zero {g : E → ℝ} (hsmul : ∀ (c : ℝ) (y : E), g (c • y) = |c| * g y) :
    g 0 = 0 := by simpa using hsmul 0 0

/-- A subadditive absolutely homogeneous functional is nonnegative. -/
private lemma seminorm_nonneg {g : E → ℝ} (hadd : ∀ y z, g (y + z) ≤ g y + g z)
    (hsmul : ∀ (c : ℝ) (y : E), g (c • y) = |c| * g y) (y : E) : 0 ≤ g y := by
  have h0 : g 0 = 0 := seminorm_zero hsmul
  have hneg : g ((-1 : ℝ) • y) = g y := by rw [hsmul]; simp
  have hy : y + (-1 : ℝ) • y = 0 := by module
  have h := hadd y ((-1 : ℝ) • y)
  rw [hneg, hy, h0] at h
  linarith

/-- A subadditive absolutely homogeneous functional is even. -/
private lemma seminorm_neg {g : E → ℝ} (hsmul : ∀ (c : ℝ) (y : E), g (c • y) = |c| * g y) (y : E) :
    g (-y) = g y := by
  have h := hsmul (-1) y
  simpa using h

/-- A subadditive absolutely homogeneous functional is convex. -/
private lemma convexOn_of_seminorm {g : E → ℝ} (hadd : ∀ y z, g (y + z) ≤ g y + g z)
    (hsmul : ∀ (c : ℝ) (y : E), g (c • y) = |c| * g y) : ConvexOn ℝ Set.univ g := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  calc g (a • x + b • y) ≤ g (a • x) + g (b • y) := hadd _ _
    _ = a * g x + b * g y := by rw [hsmul, hsmul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- A subadditive absolutely homogeneous functional on a finite-dimensional space is continuous:
it is convex and finite everywhere, hence locally Lipschitz. -/
private lemma continuous_of_seminorm [FiniteDimensional ℝ E] {g : E → ℝ}
    (hadd : ∀ y z, g (y + z) ≤ g y + g z)
    (hsmul : ∀ (c : ℝ) (y : E), g (c • y) = |c| * g y) : Continuous g :=
  (convexOn_of_seminorm hadd hsmul).locallyLipschitz.continuous

end Seminorm

/-- **The level sets of a nonvanishing seminorm are Lebesgue-null.**

For `x < 0` the level set is empty. For `x ≥ 0` it is contained in the frontier of the convex
sublevel set `{g ≤ x}`, which is Haar-null. The two ingredients that keep the point `y` off the
interior are: for `x > 0`, that `(1 + t) • y` leaves the sublevel set; and for `x = 0`, that a
proper subspace has empty interior. -/
private lemma volume_seminorm_level_eq_zero {k : ℕ} {g : EuclideanSpace ℝ (Fin k) → ℝ}
    (hadd : ∀ y z, g (y + z) ≤ g y + g z)
    (hsmul : ∀ (c : ℝ) (y : EuclideanSpace ℝ (Fin k)), g (c • y) = |c| * g y)
    (hne : ∃ u, g u ≠ 0) (x : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin k))) {y | g y = x} = 0 := by
  have hnn := seminorm_nonneg hadd hsmul
  have h0 : g 0 = 0 := seminorm_zero hsmul
  obtain ⟨u, hu⟩ := hne
  have hupos : 0 < g u := lt_of_le_of_ne (hnn u) (Ne.symm hu)
  have hune : u ≠ 0 := fun h => by rw [h, h0] at hupos; exact lt_irrefl _ hupos
  have hunorm : 0 < ‖u‖ := norm_pos_iff.2 hune
  rcases lt_or_ge x 0 with hx | hx
  · have hempty : {y : EuclideanSpace ℝ (Fin k) | g y = x} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact absurd (h ▸ hnn y) (not_le.mpr hx)
    rw [hempty, measure_empty]
  · have hconv : Convex ℝ {y : EuclideanSpace ℝ (Fin k) | g y ≤ x} := by
      have h := (convexOn_of_seminorm hadd hsmul).convex_le x
      simpa using h
    refine measure_mono_null ?_ (Convex.addHaar_frontier _ hconv)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    refine ⟨subset_closure (by simp only [Set.mem_setOf_eq, hy]; exact le_rfl), ?_⟩
    intro hmem
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hmem)
    have hune' : ‖u‖ ≠ 0 := hunorm.ne'
    rcases eq_or_lt_of_le hx with hx0 | hxpos
    · -- the level `x = 0` is the kernel of `g`, a proper subspace, so it has empty interior
      obtain ⟨s, hs, hnormsu⟩ : ∃ s : ℝ, 0 < s ∧ s * ‖u‖ = ε / 2 :=
        ⟨ε / (2 * ‖u‖), by positivity, by field_simp⟩
      have hzmem : y + s • u ∈ Metric.ball y ε := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hs, hnormsu]
        linarith
      have hz : g (y + s • u) ≤ x := hball hzmem
      have hsplit : g (s • u) ≤ g (y + s • u) + g (-y) := by
        have := hadd (y + s • u) (-y)
        simpa using this
      rw [seminorm_neg hsmul, hsmul, abs_of_pos hs, hy, ← hx0] at hsplit
      nlinarith [hsplit, hz, hupos, hs]
    · -- a positive level: scaling `y` slightly leaves the sublevel set
      have hyne : y ≠ 0 := fun h => by rw [h, h0] at hy; exact hxpos.ne hy
      have hynorm : 0 < ‖y‖ := norm_pos_iff.2 hyne
      have hyne' : ‖y‖ ≠ 0 := hynorm.ne'
      obtain ⟨t, ht, hnormty⟩ : ∃ t : ℝ, 0 < t ∧ t * ‖y‖ = ε / 2 :=
        ⟨ε / (2 * ‖y‖), by positivity, by field_simp⟩
      have hzmem : (1 + t) • y ∈ Metric.ball y ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hrw : (1 + t) • y - y = t • y := by module
        rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hnormty]
        linarith
      have hz : g ((1 + t) • y) ≤ x := hball hzmem
      rw [hsmul, abs_of_pos (by linarith : (0 : ℝ) < 1 + t), hy] at hz
      nlinarith [hz, ht, hxpos]

open scoped MatrixOrder

/-- The coordinates of a square-integrable law on a Euclidean space are square-integrable. -/
private lemma memLp_coord {k : ℕ} {Q : Measure (EuclideanSpace ℝ (Fin k))}
    (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q) (i : Fin k) :
    MemLp (fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y i) 2 Q := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin k) i).comp_memLp' hQ2
  simpa [Function.comp_def] using h

/-- The covariance bilinear form of a square-integrable law on a Euclidean space is the
quadratic form of its covariance matrix. -/
private lemma covarianceBilin_eq_covMatrix {k : ℕ} {Q : Measure (EuclideanSpace ℝ (Fin k))}
    [IsFiniteMeasure Q] (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q)
    (x y : EuclideanSpace ℝ (Fin k)) :
    covarianceBilin Q x y = ∑ i, ∑ j, WithLp.ofLp x i * WithLp.ofLp y j * covMatrix Q i j := by
  have hmap : Q.map (fun y : EuclideanSpace ℝ (Fin k) =>
      WithLp.toLp 2 fun i => WithLp.ofLp y i) = Q := by
    simp
  have h := covarianceBilin_apply_pi (μ := Q)
    (X := fun (i : Fin k) (y : EuclideanSpace ℝ (Fin k)) => WithLp.ofLp y i) (memLp_coord hQ2) x y
  rwa [hmap] at h

/-- The variance of a linear functional is the quadratic form of the covariance matrix. -/
private lemma variance_inner_eq_covMatrix {k : ℕ} {Q : Measure (EuclideanSpace ℝ (Fin k))}
    [IsFiniteMeasure Q] (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q)
    (t : EuclideanSpace ℝ (Fin k)) :
    Var[fun z : EuclideanSpace ℝ (Fin k) => inner ℝ t z; Q]
      = ∑ i, ∑ j, WithLp.ofLp t i * WithLp.ofLp t j * covMatrix Q i j := by
  rw [← covarianceBilin_self hQ2 t, covarianceBilin_eq_covMatrix hQ2]

/-- **The covariance matrix of a square-integrable law is positive semidefinite.**

Square-integrability is what makes this true: the Mathlib `covariance` returns its junk value `0`
on entries whose integrand is not integrable, and a matrix built from a mixture of genuine and
junk entries need not be positive semidefinite. -/
private lemma posSemidef_covMatrix {k : ℕ} {Q : Measure (EuclideanSpace ℝ (Fin k))}
    [IsFiniteMeasure Q] (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q) :
    (covMatrix Q).PosSemidef := by
  classical
  have hbil := covarianceBilin_eq_covMatrix hQ2
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, covMatrix, Matrix.of_apply]
    exact covariance_comm _ _
  · intro x
    have h := covarianceBilin_self_nonneg (μ := Q) (WithLp.toLp 2 x)
    rw [hbil] at h
    have hrw : dotProduct (star x) ((covMatrix Q).mulVec x)
        = ∑ i, ∑ j, x i * x j * covMatrix Q i j := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hrw]
    exact h

/-- **The spheres of a norm are null for a nondegenerate Gaussian limit.**

The analytic core: `multivariateGaussian 0 S` is the image of the standard Gaussian under the
square root of `S`, and that image turns `nrm` into a seminorm `g = nrm ∘ √S` which does not
vanish identically as soon as `S ≠ 0`. Degeneracy of `S` is allowed. -/
private lemma measure_multivariateGaussian_norm_level {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ}
    {nrm : EuclideanSpace ℝ (Fin k) → ℝ}
    (hpsd : S.PosSemidef) (hSne : S ≠ 0)
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    (hnrm_def : ∀ y, nrm y = 0 → y = 0) (x : ℝ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S {z | nrm z = x} = 0 := by
  classical
  set A := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) with hAdef
  set g : EuclideanSpace ℝ (Fin k) → ℝ := fun y => nrm (A y) with hgdef
  have hgadd : ∀ y z, g (y + z) ≤ g y + g z := by
    intro y z; simp only [hgdef, map_add]; exact hnrm_add _ _
  have hgsmul : ∀ (c : ℝ) (y), g (c • y) = |c| * g y := by
    intro c y; simp only [hgdef, map_smul]; exact hnrm_smul _ _
  -- the square root of a nonzero positive semidefinite matrix is nonzero
  have hsqrt_ne : CFC.sqrt S ≠ 0 := fun h => hSne ((CFC.sqrt_eq_zero_iff S hpsd.nonneg).1 h)
  have hAne : A ≠ 0 := by
    intro h
    exact hsqrt_ne ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)).injective
      (a₁ := CFC.sqrt S) (a₂ := 0) (by simpa [hAdef, map_zero] using h))
  -- hence `g` is a seminorm that does not vanish identically
  have hgne : ∃ u, g u ≠ 0 := by
    obtain ⟨u, hu⟩ := DFunLike.ne_iff.1 hAne
    refine ⟨u, fun h => hu ?_⟩
    simpa using hnrm_def _ h
  have hnrm_cont : Continuous nrm := continuous_of_seminorm hnrm_add hnrm_smul
  have hset : MeasurableSet {z : EuclideanSpace ℝ (Fin k) | nrm z = x} :=
    measurableSet_eq_fun hnrm_cont.measurable measurable_const
  have hpre : (fun y : EuclideanSpace ℝ (Fin k) => (0 : EuclideanSpace ℝ (Fin k)) + A y) ⁻¹'
      {z | nrm z = x} = {y | g y = x} := by
    ext y; simp [hgdef]
  rw [multivariateGaussian,
    Measure.map_apply (by fun_prop : Measurable fun y : EuclideanSpace ℝ (Fin k) =>
      (0 : EuclideanSpace ℝ (Fin k)) + A y) hset, hpre]
  exact stdGaussian_absolutelyContinuous_volume k
    (volume_seminorm_level_eq_zero hgadd hgsmul hgne x)

/-- **Continuity of the limiting norm distribution function, for a general covariance.**

The general engine behind `continuous_normLimitCDF`: for any nonzero positive semidefinite `S`
the distribution function of `nrm` under `multivariateGaussian 0 S` is continuous. Degeneracy of
`S` is allowed — only `S ≠ 0` is used. -/
private lemma continuous_normLimitCDF_of_posSemidef {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ}
    {nrm : EuclideanSpace ℝ (Fin k) → ℝ}
    (hpsd : S.PosSemidef) (hSne : S ≠ 0)
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    (hnrm_def : ∀ y, nrm y = 0 → y = 0) :
    Continuous (normLimitCDF S nrm) := by
  have hnrm_cont : Continuous nrm := continuous_of_seminorm hnrm_add hnrm_smul
  set ρ := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S).map nrm with hρdef
  haveI : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map hnrm_cont.measurable.aemeasurable
  haveI : NullSingletonClass ρ := by
    refine ⟨fun x => ?_⟩
    rw [hρdef, Measure.map_apply hnrm_cont.measurable (measurableSet_singleton x)]
    exact measure_multivariateGaussian_norm_level hpsd hSne hnrm_add hnrm_smul hnrm_def x
  have heq : normLimitCDF S nrm = fun x => (ρ (Set.Iic x)).toReal := by
    funext x
    rw [normLimitCDF, hρdef, Measure.map_apply hnrm_cont.measurable measurableSet_Iic]
    rfl
  rw [heq]
  exact continuous_toReal_measure_Iic ρ

end NormOfGaussian

/-! ## Empirical measures on a Euclidean space -/

section EmpiricalBasics

/-- Every strongly measurable function is integrable against an empirical measure. -/
private lemma integrable_empiricalMeasure {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x : Fin n → EuclideanSpace ℝ (Fin k))
    (f : EuclideanSpace ℝ (Fin k) → E) : Integrable f (empiricalMeasure x) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [empiricalMeasure]
  · unfold empiricalMeasure
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (by exact_mod_cast hn.ne'))
    exact integrable_finset_sum_measure.2 (fun i _ => integrable_dirac (by simp))

/-- The integral against an empirical measure is the sample average. -/
private lemma integral_empiricalMeasure {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (x : Fin n → EuclideanSpace ℝ (Fin k))
    (f : EuclideanSpace ℝ (Fin k) → E) :
    ∫ y, f y ∂(empiricalMeasure x) = (n : ℝ)⁻¹ • ∑ i, f (x i) := by
  unfold empiricalMeasure
  rw [integral_smul_measure,
    integral_finset_sum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- The empirical measure of a nonempty sample is a probability measure. -/
private lemma isProbabilityMeasure_empiricalMeasure {n : ℕ} (hn : 0 < n)
    (x : Fin n → EuclideanSpace ℝ (Fin k)) : IsProbabilityMeasure (empiricalMeasure x) := by
  refine ⟨?_⟩
  unfold empiricalMeasure
  simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)]

/-- The identity is square-integrable against an empirical measure. -/
private lemma memLp_id_empiricalMeasure {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin k)) :
    MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 (empiricalMeasure x) := by
  rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
  exact integrable_empiricalMeasure x (fun y => ‖y‖ ^ 2)

/-- **Strong law of large numbers, in the form the empirical class needs.** -/
private lemma tendsto_sample_average {Pr : Measure Ω}
    [IsProbabilityMeasure Pr] {Q : Measure (EuclideanSpace ℝ (Fin k))}
    {X : ℕ → Ω → EuclideanSpace ℝ (Fin k)}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) Q Pr)
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    (g : EuclideanSpace ℝ (Fin k) → E) (hg : Measurable g) (hint : Integrable g Q) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (X i ω)) atTop
      (𝓝 (∫ y, g y ∂Q)) := by
  have hintmap : Integrable g (Pr.map (X 0)) := by rw [hlaw.map_eq]; exact hint
  have hint' : Integrable (fun ω => g (X 0 ω)) Pr :=
    (integrable_map_measure hintmap.aestronglyMeasurable (hmeas 0).aemeasurable).1 hintmap
  have hmean : Pr[fun ω => g (X 0 ω)] = ∫ y, g y ∂Q :=
    hlaw.integral_comp hg.aestronglyMeasurable
  rw [← hmean]
  exact strong_law_ae (fun i ω => g (X i ω)) hint'
    (fun i j hij => (hindep.comp (fun _ => g) (fun _ => hg)).indepFun hij)
    (fun i => (hident i).comp hg)

/-- A complex exponential of a linear functional is integrable against any finite measure. -/
private lemma integrable_charFun_integrand (μ : Measure (EuclideanSpace ℝ (Fin k)))
    [IsFiniteMeasure μ] (t : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin k) =>
      Complex.exp ((inner ℝ y t : ℝ) * Complex.I)) μ := by
  refine (memLp_top_of_bound (by fun_prop) 1 ?_).integrable le_top
  filter_upwards with y
  simp [Complex.norm_exp_ofReal_mul_I]

/-- **The characteristic function is Lipschitz with the first absolute moment as constant.**

This is the equicontinuity that turns characteristic-function convergence on a countable dense
set of directions into convergence in every direction. -/
private lemma norm_charFun_sub_charFun_le (μ : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure μ] (hint : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) μ)
    (t s : EuclideanSpace ℝ (Fin k)) :
    ‖charFun μ t - charFun μ s‖ ≤ ‖t - s‖ * ∫ y, ‖y‖ ∂μ := by
  have hb : ∀ y : EuclideanSpace ℝ (Fin k),
      ‖Complex.exp ((inner ℝ y t : ℝ) * Complex.I)
        - Complex.exp ((inner ℝ y s : ℝ) * Complex.I)‖ ≤ ‖t - s‖ * ‖y‖ := by
    intro y
    have hfac : Complex.exp ((inner ℝ y t : ℝ) * Complex.I)
        - Complex.exp ((inner ℝ y s : ℝ) * Complex.I)
        = Complex.exp ((inner ℝ y s : ℝ) * Complex.I)
          * (Complex.exp (Complex.I * (((inner ℝ y t : ℝ) - (inner ℝ y s : ℝ) : ℝ) : ℂ))
            - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      push_cast
      ring_nf
    rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    refine le_trans Real.norm_exp_I_mul_ofReal_sub_one_le ?_
    have hinner : (inner ℝ y t : ℝ) - (inner ℝ y s : ℝ) = inner ℝ y (t - s) := by
      rw [inner_sub_right]
    rw [Real.norm_eq_abs, hinner]
    calc |(inner ℝ y (t - s) : ℝ)| ≤ ‖y‖ * ‖t - s‖ := abs_real_inner_le_norm y (t - s)
      _ = ‖t - s‖ * ‖y‖ := by ring
  rw [charFun_apply, charFun_apply,
    ← integral_sub (integrable_charFun_integrand μ t) (integrable_charFun_integrand μ s)]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ y, ‖Complex.exp ((inner ℝ y t : ℝ) * Complex.I)
        - Complex.exp ((inner ℝ y s : ℝ) * Complex.I)‖ ∂μ
      ≤ ∫ y, ‖t - s‖ * ‖y‖ ∂μ := by
        refine integral_mono ?_ (hint.const_mul _) hb
        exact ((integrable_charFun_integrand μ t).sub (integrable_charFun_integrand μ s)).norm
    _ = ‖t - s‖ * ∫ y, ‖y‖ ∂μ := integral_const_mul _ _

set_option maxHeartbeats 1600000 in
/-- **The empirical sequence belongs to the mean-vector class, almost surely.**

The weak-convergence clause — the multivariate Glivenko–Cantelli / Varadarajan input — is
obtained from the strong law alone: the characteristic functions of the empirical measures are
sample averages of bounded functions, so they converge almost surely along a *countable* dense
set of directions; the first absolute moment (also a strong law) makes the family equi-Lipschitz
in the direction, which upgrades the countable statement to every direction, and Lévy's
continuity theorem concludes. -/
private theorem empirical_mem_meanVecSeqClass {Q : Measure (EuclideanSpace ℝ (Fin k))}
    {Pr : Measure Ω} [IsProbabilityMeasure Pr] [IsProbabilityMeasure Q]
    {X : ℕ → Ω → EuclideanSpace ℝ (Fin k)}
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) Q Pr)
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q) :
    ∀ᵐ ω ∂Pr, (fun n => empiricalMeasure fun i : Fin n => X i ω) ∈ meanVecSeqClass Q := by
  classical
  have hcoordLp := memLp_coord hQ2
  have hcoordint : ∀ i : Fin k,
      Integrable (fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y i) Q :=
    fun i => (hcoordLp i).integrable one_le_two
  have hprodint : ∀ i j : Fin k,
      Integrable (fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y i * WithLp.ofLp y j) Q :=
    fun i j => (hcoordLp i).integrable_mul (hcoordLp j)
  have hnormint : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) Q :=
    (hQ2.integrable one_le_two).norm
  set T : ℕ → EuclideanSpace ℝ (Fin k) :=
    TopologicalSpace.denseSeq (EuclideanSpace ℝ (Fin k)) with hT
  have hTdense : DenseRange T := TopologicalSpace.denseRange_denseSeq _
  -- four families of strong laws, all indexed countably
  have hA : ∀ᵐ ω ∂Pr, ∀ i : Fin k,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, WithLp.ofLp (X j ω) i) atTop
        (𝓝 (∫ y, WithLp.ofLp y i ∂Q)) :=
    ae_all_iff.2 fun i =>
      tendsto_sample_average hmeas hindep hlaw hident _ (by fun_prop) (hcoordint i)
  have hB : ∀ᵐ ω ∂Pr, ∀ i j : Fin k,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ jj ∈ Finset.range n,
          WithLp.ofLp (X jj ω) i * WithLp.ofLp (X jj ω) j) atTop
        (𝓝 (∫ y, WithLp.ofLp y i * WithLp.ofLp y j ∂Q)) :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
      tendsto_sample_average hmeas hindep hlaw hident _ (by fun_prop) (hprodint i j)
  have hC : ∀ᵐ ω ∂Pr, ∀ m : ℕ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n,
          Complex.exp ((inner ℝ (X j ω) (T m) : ℝ) * Complex.I)) atTop
        (𝓝 (∫ y, Complex.exp ((inner ℝ y (T m) : ℝ) * Complex.I) ∂Q)) :=
    ae_all_iff.2 fun m =>
      tendsto_sample_average hmeas hindep hlaw hident _ (by fun_prop)
        (integrable_charFun_integrand Q (T m))
  have hD : ∀ᵐ ω ∂Pr,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, ‖X j ω‖) atTop
        (𝓝 (∫ y, ‖y‖ ∂Q)) :=
    tendsto_sample_average hmeas hindep hlaw hident _ (by fun_prop) hnormint
  filter_upwards [hA, hB, hC, hD] with ω hAω hBω hCω hDω
  have hprob : ∀ n : ℕ, 0 < n →
      IsProbabilityMeasure (empiricalMeasure fun j : Fin n => X j ω) :=
    fun n hn => isProbabilityMeasure_empiricalMeasure hn _
  refine ⟨hprob, fun n => memLp_id_empiricalMeasure _, ?_, ?_, ?_⟩
  · -- weak convergence, via Lévy's continuity theorem
    intro f
    set R : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) := fun n =>
      ⟨empiricalMeasure fun j : Fin (n + 1) => X j ω, hprob (n + 1) n.succ_pos⟩ with hR
    set νQ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) := ⟨Q, inferInstance⟩ with hνQ
    have hRcoe : ∀ n : ℕ, ((R n : Measure (EuclideanSpace ℝ (Fin k))))
        = empiricalMeasure fun j : Fin (n + 1) => X j ω := fun n => rfl
    have hmom : Tendsto (fun n : ℕ => ∫ y, ‖y‖ ∂(R n : Measure (EuclideanSpace ℝ (Fin k))))
        atTop (𝓝 (∫ y, ‖y‖ ∂Q)) := by
      have hrw : ∀ n : ℕ, ∫ y, ‖y‖ ∂(R n : Measure (EuclideanSpace ℝ (Fin k)))
          = ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ j ∈ Finset.range (n + 1), ‖X j ω‖ := by
        intro n
        rw [hRcoe, integral_empiricalMeasure]
        congr 1
        exact Fin.sum_univ_eq_sum_range (fun j => ‖X j ω‖) (n + 1)
      simp only [hrw]
      exact (Filter.tendsto_add_atTop_iff_nat 1).2 hDω
    have hmomint : ∀ n : ℕ,
        Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖)
          (R n : Measure (EuclideanSpace ℝ (Fin k))) := by
      intro n
      rw [hRcoe]
      exact integrable_empiricalMeasure _ _
    have hcfT : ∀ m : ℕ, Tendsto
        (fun n : ℕ => charFun ((R n : Measure (EuclideanSpace ℝ (Fin k)))) (T m)) atTop
        (𝓝 (charFun Q (T m))) := by
      intro m
      have hrw : ∀ n : ℕ, charFun ((R n : Measure (EuclideanSpace ℝ (Fin k)))) (T m)
          = ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ j ∈ Finset.range (n + 1),
              Complex.exp ((inner ℝ (X j ω) (T m) : ℝ) * Complex.I) := by
        intro n
        rw [charFun_apply, hRcoe, integral_empiricalMeasure]
        congr 1
        exact Fin.sum_univ_eq_sum_range
          (fun j => Complex.exp ((inner ℝ (X j ω) (T m) : ℝ) * Complex.I)) (n + 1)
      simp only [hrw]
      exact (Filter.tendsto_add_atTop_iff_nat 1).2 (hCω m)
    have hcf : ∀ t : EuclideanSpace ℝ (Fin k), Tendsto
        (fun n : ℕ => charFun ((R n : Measure (EuclideanSpace ℝ (Fin k)))) t) atTop
        (𝓝 (charFun Q t)) := by
      intro t
      set C : ℝ := ∫ y, ‖y‖ ∂Q with hCdef
      have hCnn : 0 ≤ C := integral_nonneg fun y => norm_nonneg y
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨m, hm⟩ : ∃ m : ℕ, ‖t - T m‖ < ε / (3 * (C + 2)) := by
        have hpos : 0 < ε / (3 * (C + 2)) := by positivity
        obtain ⟨-, ⟨m, rfl⟩, hlt⟩ := Metric.mem_closure_iff.1 (hTdense t) _ hpos
        exact ⟨m, by rwa [← dist_eq_norm]⟩
      obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hmom 1 one_pos
      obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (hcfT m) (ε / 3) (by positivity)
      refine ⟨max N₁ N₂, fun n hn => ?_⟩
      have hn₁ := hN₁ n (le_of_max_le_left hn)
      have hn₂ := hN₂ n (le_of_max_le_right hn)
      have hbound : ∫ y, ‖y‖ ∂(R n : Measure (EuclideanSpace ℝ (Fin k))) ≤ C + 1 := by
        have hx := abs_lt.1 (by rwa [Real.dist_eq] at hn₁)
        linarith [hx.2]
      have hnn : (0 : ℝ) ≤ ∫ y, ‖y‖ ∂(R n : Measure (EuclideanSpace ℝ (Fin k))) :=
        integral_nonneg fun y => norm_nonneg y
      have hfrac : (ε / (3 * (C + 2))) * (C + 1) ≤ ε / 3 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hε.le, hCnn]
      have h1 : ‖charFun ((R n : Measure (EuclideanSpace ℝ (Fin k)))) t
          - charFun ((R n : Measure (EuclideanSpace ℝ (Fin k)))) (T m)‖ ≤ ε / 3 := by
        refine (norm_charFun_sub_charFun_le _ (hmomint n) t (T m)).trans ?_
        refine le_trans (mul_le_mul hm.le hbound hnn (by positivity)) hfrac
      have h3 : ‖charFun Q (T m) - charFun Q t‖ ≤ ε / 3 := by
        refine (norm_charFun_sub_charFun_le Q hnormint (T m) t).trans ?_
        rw [← neg_sub t (T m), norm_neg]
        exact le_trans (mul_le_mul hm.le (by linarith) hCnn (by positivity)) hfrac
      have h2 : ‖charFun ((R n : Measure (EuclideanSpace ℝ (Fin k)))) (T m)
          - charFun Q (T m)‖ < ε / 3 := by rwa [dist_eq_norm] at hn₂
      rw [dist_eq_norm]
      have hsplit : charFun ((R n : Measure (EuclideanSpace ℝ (Fin k)))) t - charFun Q t
          = (charFun ((R n : Measure (EuclideanSpace ℝ (Fin k)))) t
              - charFun ((R n : Measure (EuclideanSpace ℝ (Fin k)))) (T m))
            + (charFun ((R n : Measure (EuclideanSpace ℝ (Fin k)))) (T m) - charFun Q (T m))
            + (charFun Q (T m) - charFun Q t) := by ring
      rw [hsplit]
      calc ‖_ + _ + _‖ ≤ _ := norm_add₃_le
        _ < ε := by linarith
    have hlevy : Tendsto R atTop (𝓝 νQ) := ProbabilityMeasure.tendsto_of_tendsto_charFun hcf
    have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlevy f
    simp only [hRcoe, hνQ] at hint
    exact (Filter.tendsto_add_atTop_iff_nat 1).1 hint
  · -- convergence of the mean vectors
    intro i
    have heq : ∀ n : ℕ, ∫ y, WithLp.ofLp y i ∂(empiricalMeasure fun j : Fin n => X j ω)
        = (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, WithLp.ofLp (X j ω) i := by
      intro n
      rw [integral_empiricalMeasure]
      congr 1
      exact Fin.sum_univ_eq_sum_range (fun j => WithLp.ofLp (X j ω) i) n
    simp only [heq]
    exact hAω i
  · -- convergence of the covariance matrices
    intro i j
    have hI : ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin k) → ℝ),
        ∫ y, g y ∂(empiricalMeasure fun jj : Fin n => X jj ω)
          = (n : ℝ)⁻¹ • ∑ jj ∈ Finset.range n, g (X jj ω) := by
      intro n g
      rw [integral_empiricalMeasure]
      congr 1
      exact Fin.sum_univ_eq_sum_range (fun jj => g (X jj ω)) n
    have hQsub : covMatrix Q i j
        = (∫ y, WithLp.ofLp y i * WithLp.ofLp y j ∂Q)
          - (∫ y, WithLp.ofLp y i ∂Q) * ∫ y, WithLp.ofLp y j ∂Q :=
      covariance_eq_sub (hcoordLp i) (hcoordLp j)
    have heq : ∀ᶠ n : ℕ in atTop,
        ((n : ℝ)⁻¹ • ∑ jj ∈ Finset.range n,
            WithLp.ofLp (X jj ω) i * WithLp.ofLp (X jj ω) j)
          - ((n : ℝ)⁻¹ • ∑ jj ∈ Finset.range n, WithLp.ofLp (X jj ω) i)
            * ((n : ℝ)⁻¹ • ∑ jj ∈ Finset.range n, WithLp.ofLp (X jj ω) j)
          = covMatrix (empiricalMeasure fun jj : Fin n => X jj ω) i j := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      haveI := hprob n hn
      rw [show covMatrix (empiricalMeasure fun jj : Fin n => X jj ω) i j
        = cov[fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y i,
              fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y j;
              empiricalMeasure fun jj : Fin n => X jj ω] from rfl,
        covariance_eq_sub (memLp_coord (memLp_id_empiricalMeasure _) i)
          (memLp_coord (memLp_id_empiricalMeasure _) j)]
      simp only [Pi.mul_apply]
      rw [hI n (fun y => WithLp.ofLp y i * WithLp.ofLp y j), hI n (fun y => WithLp.ofLp y i),
        hI n (fun y => WithLp.ofLp y j)]
    refine Tendsto.congr' heq ?_
    rw [hQsub]
    exact (hBω i j).sub ((hAω i).mul (hAω j))

end EmpiricalBasics

/-! ## Cramér–Wold: projecting the mean-vector root onto a direction -/

section CramerWold

/-- The image of the mean-vector root law under a linear functional is the univariate root law
of the image sequence. This is the Cramér–Wold reduction, at the level of the laws. -/
private lemma meanVecRootLaw_map_inner {k : ℕ} (F : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure F] (hF2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 F)
    (t : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    (meanVecRootLaw F n).map (fun z => inner ℝ t z)
      = meanRootLaw (F.map (fun z => inner ℝ t z)) n := by
  classical
  have hcoe : (fun z : EuclideanSpace ℝ (Fin k) => inner ℝ t z) = ⇑(innerSL ℝ t) := rfl
  simp only [hcoe]
  set L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ := innerSL ℝ t with hL
  have hLc : Continuous L := L.continuous
  have hFint : Integrable (fun z : EuclideanSpace ℝ (Fin k) => z) F := hF2.integrable one_le_two
  have hint2 : ∫ s, s ∂(F.map L) = L (∫ z, z ∂F) := by
    rw [integral_map hLc.aemeasurable (by fun_prop), L.integral_comp_comm hFint]
  have hpi : Measure.pi (fun _ : Fin n => F.map L)
      = (Measure.pi fun _ : Fin n => F).map (fun y i => L (y i)) :=
    (Measure.pi_map_pi (fun _ => hLc.aemeasurable)).symm
  rw [meanVecRootLaw, meanRootLaw, hpi,
    Measure.map_map hLc.measurable (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext y
  simp only [Function.comp_def, hint2, map_smul, map_sub, map_sum, smul_eq_mul]

end CramerWold

/-! ## The mean vector -/

section MeanVector

variable {Q : Measure (EuclideanSpace ℝ (Fin k))} {F : ℕ → Measure (EuclideanSpace ℝ (Fin k))}
  {nrm : EuclideanSpace ℝ (Fin k) → ℝ} {Pr : Measure Ω} {X : ℕ → Ω → EuclideanSpace ℝ (Fin k)}

/-- **Limit law of the mean vector along the class.**

Along every sequence of the mean-vector class, the law of the centred and scaled sample mean
vector converges weakly to the centred multivariate normal law with the limiting covariance
matrix. -/
theorem meanVec_root_tendsto [IsProbabilityMeasure Q]
    -- USER-INPUT: the limit law is square-integrable, so its mean vector and covariance exist
    (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q)
    -- USER-INPUT: the sequence of laws belongs to the mean-vector class
    (hF : F ∈ meanVecSeqClass Q)
    -- LEAN-ONLY: argument quantified by the conclusion, not a hypothesis
    (f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ) :
    Tendsto (fun n => ∫ z, f z ∂(meanVecRootLaw (F n) n)) atTop
      (𝓝 (∫ z, f z ∂(multivariateGaussian 0 (covMatrix Q)))) := by
  classical
  -- Replace the unconstrained `n = 0` entry of the sequence by `Q`, so that every entry is a
  -- probability measure; the conclusion only sees the tail.
  set F' : ℕ → Measure (EuclideanSpace ℝ (Fin k)) := fun n => if n = 0 then Q else F n with hF'def
  have hF'eq : ∀ n : ℕ, 0 < n → F' n = F n := by
    intro n hn; simp only [hF'def, if_neg hn.ne']
  haveI hF'prob : ∀ n, IsProbabilityMeasure (F' n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa only [hF'def, if_pos rfl] using ‹IsProbabilityMeasure Q›
    · rw [hF'eq n hn]; exact hF.1 n hn
  obtain ⟨-, hF2, hFweak, hFmean, hFcov⟩ := hF
  have hF'2 : ∀ n, MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 (F' n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa only [hF'def, if_pos rfl] using hQ2
    · rw [hF'eq n hn]; exact hF2 n
  have hF'weak : ∀ g : EuclideanSpace ℝ (Fin k) →ᵇ ℝ,
      Tendsto (fun n => ∫ y, g y ∂(F' n)) atTop (𝓝 (∫ y, g y ∂Q)) := by
    intro g
    refine (hFweak g).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hF'eq n hn]
  have hF'mean : ∀ i : Fin k, Tendsto (fun n => ∫ y, WithLp.ofLp y i ∂(F' n)) atTop
      (𝓝 (∫ y, WithLp.ofLp y i ∂Q)) := by
    intro i
    refine (hFmean i).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hF'eq n hn]
  have hF'cov : ∀ i j : Fin k,
      Tendsto (fun n => covMatrix (F' n) i j) atTop (𝓝 (covMatrix Q i j)) := by
    intro i j
    refine (hFcov i j).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hF'eq n hn]
  -- the root laws are probability measures
  haveI hpi : ∀ n : ℕ, IsProbabilityMeasure (Measure.pi fun _ : Fin n => F' n) := by
    intro n
    haveI : ∀ _ : Fin n, IsProbabilityMeasure (F' n) := fun _ => hF'prob n
    infer_instance
  haveI hroot : ∀ n : ℕ, IsProbabilityMeasure (meanVecRootLaw (F' n) n) := by
    intro n
    haveI := hpi n
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  -- Cramér–Wold, direction by direction, through the characteristic functions
  set μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) :=
    fun n => ⟨meanVecRootLaw (F' n) n, hroot n⟩ with hμs
  set ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) :=
    ⟨multivariateGaussian 0 (covMatrix Q), inferInstance⟩ with hν
  have hconv : Tendsto μs atTop (𝓝 ν) := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    -- the projected sequence
    have hLc : Continuous fun z : EuclideanSpace ℝ (Fin k) => (inner ℝ t z : ℝ) :=
      (innerSL ℝ t).continuous
    set G : ℕ → Measure ℝ := fun n => (F' n).map (fun z => inner ℝ t z) with hG
    set Q₁ : Measure ℝ := Q.map (fun z => inner ℝ t z) with hQ₁
    haveI hGprob : ∀ n, IsProbabilityMeasure (G n) := fun n =>
      Measure.isProbabilityMeasure_map hLc.aemeasurable
    haveI hQ₁prob : IsProbabilityMeasure Q₁ := Measure.isProbabilityMeasure_map hLc.aemeasurable
    haveI hGpi : ∀ n : ℕ, IsProbabilityMeasure (Measure.pi fun _ : Fin n => G n) := by
      intro n
      haveI : ∀ _ : Fin n, IsProbabilityMeasure (G n) := fun _ => hGprob n
      infer_instance
    haveI hGroot : ∀ n : ℕ, IsProbabilityMeasure (meanRootLaw (G n) n) := by
      intro n
      haveI := hGpi n
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    -- square-integrability of the projections
    have hproj2 : ∀ (μ : Measure (EuclideanSpace ℝ (Fin k))),
        MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 μ →
          MemLp (fun s : ℝ => s) 2 (μ.map (fun z => inner ℝ t z)) := by
      intro μ hμ
      refine (memLp_map_measure_iff (by fun_prop) hLc.aemeasurable).2 ?_
      have h : MemLp (fun z : EuclideanSpace ℝ (Fin k) => (inner ℝ t z : ℝ)) 2 μ := by
        simpa [Function.comp_def] using (innerSL ℝ t).comp_memLp' hμ
      simpa [Function.comp_def] using h
    have hG2 : ∀ n, MemLp (fun s : ℝ => s) 2 (G n) := fun n => hproj2 _ (hF'2 n)
    have hQ₁2 : MemLp (fun s : ℝ => s) 2 Q₁ := hproj2 _ hQ2
    -- weak convergence of the projections
    have hGweak : ∀ g : ℝ →ᵇ ℝ,
        Tendsto (fun n => ∫ s, g s ∂(G n)) atTop (𝓝 (∫ s, g s ∂Q₁)) := by
      intro g
      have hcomp : ∀ μ : Measure (EuclideanSpace ℝ (Fin k)),
          ∫ s, g s ∂(μ.map (fun z => inner ℝ t z))
            = ∫ y, (g.compContinuous ⟨fun z => inner ℝ t z, hLc⟩) y ∂μ := by
        intro μ
        rw [integral_map hLc.aemeasurable g.continuous.aestronglyMeasurable]
        rfl
      simp only [hG, hQ₁, hcomp]
      exact hF'weak _
    -- the means of the projections
    have hprojmean : ∀ (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure μ],
        MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 μ →
          ∫ s, s ∂(μ.map (fun z => inner ℝ t z))
            = ∑ i, WithLp.ofLp t i * ∫ y, WithLp.ofLp y i ∂μ := by
      intro μ _ hμ
      have hint : Integrable (fun z : EuclideanSpace ℝ (Fin k) => z) μ := hμ.integrable one_le_two
      have hcomm : ∫ z, (inner ℝ t z : ℝ) ∂μ = inner ℝ t (∫ z, z ∂μ) :=
        (innerSL ℝ t).integral_comp_comm hint
      have hcoordint : ∀ i : Fin k, ∫ y, WithLp.ofLp y i ∂μ = WithLp.ofLp (∫ z, z ∂μ) i :=
        fun i => (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin k) i).integral_comp_comm hint
      rw [integral_map hLc.aemeasurable (by fun_prop), hcomm]
      simp only [hcoordint]
      simp [PiLp.inner_apply, real_inner_eq_re_inner, mul_comm]
    have hGmean : Tendsto (fun n => ∫ s, s ∂(G n)) atTop (𝓝 (∫ s, s ∂Q₁)) := by
      simp only [hG, hQ₁, hprojmean _ (hF'2 _), hprojmean _ hQ2]
      exact tendsto_finset_sum _ fun i _ => (hF'mean i).const_mul _
    -- the variances of the projections
    have hprojvar : ∀ (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure μ],
        MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 μ →
          Var[fun s : ℝ => s; μ.map (fun z => inner ℝ t z)]
            = ∑ i, ∑ j, WithLp.ofLp t i * WithLp.ofLp t j * covMatrix μ i j := by
      intro μ _ hμ
      rw [variance_map (by fun_prop) hLc.aemeasurable]
      exact variance_inner_eq_covMatrix hμ t
    have hGvar : Tendsto (fun n => Var[fun s : ℝ => s; G n]) atTop
        (𝓝 Var[fun s : ℝ => s; Q₁]) := by
      simp only [hG, hQ₁, hprojvar _ (hF'2 _), hprojvar _ hQ2]
      exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
        (hF'cov i j).const_mul _
    -- the univariate triangular-array central limit theorem in this direction
    have huni := tendsto_meanRootLaw hG2 hQ₁2 hGweak hGmean hGvar
    set ρs : ℕ → ProbabilityMeasure ℝ := fun n => ⟨meanRootLaw (G n) n, hGroot n⟩ with hρs
    set ρ : ProbabilityMeasure ℝ :=
      ⟨gaussianReal 0 (Real.toNNReal Var[fun s : ℝ => s; Q₁]), inferInstance⟩ with hρ
    have hprobconv : Tendsto ρs atTop (𝓝 ρ) :=
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 huni
    have hcf := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hprobconv 1
    -- transport back to the characteristic function of the vector law
    have hproject : ∀ (μ : Measure (EuclideanSpace ℝ (Fin k))),
        charFun μ t = charFun (μ.map (fun z => inner ℝ t z)) 1 := by
      intro μ
      have h1 : ∀ a : ℝ, (inner ℝ a (1 : ℝ) : ℝ) = a := fun a => by
        simp [real_inner_eq_re_inner]
      rw [charFun_apply, charFun_apply, integral_map hLc.aemeasurable (by fun_prop)]
      simp only [h1]
      simp_rw [real_inner_comm t]
    have hcoeμ : ∀ n : ℕ, ((μs n : Measure (EuclideanSpace ℝ (Fin k))))
        = meanVecRootLaw (F' n) n := fun n => rfl
    have hcoeν : ((ν : Measure (EuclideanSpace ℝ (Fin k))))
        = multivariateGaussian 0 (covMatrix Q) := rfl
    have hcoeρs : ∀ n : ℕ, ((ρs n : Measure ℝ)) = meanRootLaw (G n) n := fun n => rfl
    have hcoeρ : ((ρ : Measure ℝ))
        = gaussianReal 0 (Real.toNNReal Var[fun s : ℝ => s; Q₁]) := rfl
    have hlhs : ∀ n : ℕ, charFun (meanVecRootLaw (F' n) n) t
        = charFun (meanRootLaw (G n) n) 1 := by
      intro n
      rw [hproject]
      congr 1
      exact meanVecRootLaw_map_inner (F' n) (hF'2 n) t n
    have hrhs : charFun (multivariateGaussian 0 (covMatrix Q)) t
        = charFun (gaussianReal 0 (Real.toNNReal Var[fun s : ℝ => s; Q₁])) 1 := by
      have hvarQ : Var[fun s : ℝ => s; Q₁]
          = ∑ i, ∑ j, WithLp.ofLp t i * WithLp.ofLp t j * covMatrix Q i j := hprojvar _ hQ2
      have hquad : WithLp.ofLp t ⬝ᵥ (covMatrix Q).mulVec (WithLp.ofLp t)
          = ∑ i, ∑ j, WithLp.ofLp t i * WithLp.ofLp t j * covMatrix Q i j := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      have hqnn : 0 ≤ WithLp.ofLp t ⬝ᵥ (covMatrix Q).mulVec (WithLp.ofLp t) := by
        simpa using (posSemidef_covMatrix hQ2).dotProduct_mulVec_nonneg (WithLp.ofLp t)
      rw [charFun_multivariateGaussian (posSemidef_covMatrix hQ2), charFun_gaussianReal,
        hvarQ, ← hquad]
      simp [max_eq_left hqnn]
    simp only [hcoeμ, hcoeν, hlhs, hrhs]
    simp only [hcoeρs, hcoeρ] at hcf
    exact hcf
  -- unpack the weak convergence and undo the `n = 0` patch
  have hgoal := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv f
  refine hgoal.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hμs]
  simp only [hF'eq n hn]
  rfl

/-- **The limiting distribution function of the norm is continuous.**

If the limiting covariance matrix has a nonzero entry, the norm of the Gaussian limit has no
atoms: the spheres of a norm are boundaries of convex sets and hence null for the limit law.

**Signature amendment (square-integrability of the limit law).** The reference's statement is
*false* as frozen, and the added hypotheses `[IsFiniteMeasure Q]` and `hQ2` are exactly what
repairs it. In Mathlib v4.29.1, `multivariateGaussian 0 S = Measure.dirac 0` as soon as `S` is
not positive semidefinite (`ProbabilityTheory.multivariateGaussian_of_not_posSemidef`); for that
law `normLimitCDF S nrm` is the indicator of `{0 ≤ x}`, which jumps at `0`, so no norm makes it
continuous. And `covMatrix Q` is positive semidefinite only under square-integrability: the
Mathlib `covariance` returns its junk value `0` whenever the integrand is not integrable, so a
law with one non-integrable coordinate can have a vanishing diagonal entry next to a genuine
nonzero off-diagonal one (on `ℝ²`, the law of `(Z, Z / (1 + Z²))` for a Cauchy `Z` has junk
`(1,1)` entry `0` — `Z` is not integrable and `Z²` is not either — while the `(1,2)` entry
`∫ Z² / (1 + Z²)` is finite and positive, giving a negative determinant). Both added hypotheses
are already carried by the two siblings `norm_root_cdf_tendsto` and
`bootstrap_meanVec_consistent`, so no application is weakened. -/
theorem continuous_normLimitCDF [IsFiniteMeasure Q]
    -- USER-INPUT (signature amendment): the limit law is square-integrable, so its covariance
    -- matrix is positive semidefinite and the Gaussian limit is a genuine Gaussian
    (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q)
    -- USER-INPUT: the norm is subadditive
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    -- USER-INPUT: the norm is absolutely homogeneous
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    -- USER-INPUT: the norm is positive definite
    (hnrm_def : ∀ y, nrm y = 0 → y = 0)
    -- USER-INPUT: the limiting covariance is not identically zero, so the limit is nondegenerate
    (hS : ∃ i j : Fin k, covMatrix Q i j ≠ 0) :
    Continuous (normLimitCDF (covMatrix Q) nrm) := by
  obtain ⟨i, j, hij⟩ := hS
  exact continuous_normLimitCDF_of_posSemidef (posSemidef_covMatrix hQ2)
    (fun h => hij (by rw [h]; simp)) hnrm_add hnrm_smul hnrm_def

/-- **Limit law of the norm of the root along the class.**

Along every sequence of the mean-vector class, the sampling distribution function of the norm of
the centred and scaled sample mean vector converges to the distribution function of the norm of
the Gaussian limit — for **every** norm on `ℝᵏ`. -/
theorem norm_root_cdf_tendsto [IsProbabilityMeasure Q]
    -- USER-INPUT: the limit law is square-integrable
    (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q)
    -- USER-INPUT: the sequence of laws belongs to the mean-vector class
    (hF : F ∈ meanVecSeqClass Q)
    -- USER-INPUT: the norm is subadditive
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    -- USER-INPUT: the norm is absolutely homogeneous
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    -- USER-INPUT: the norm is positive definite
    (hnrm_def : ∀ y, nrm y = 0 → y = 0)
    -- USER-INPUT: nondegeneracy of the limiting covariance
    (hS : ∃ i j : Fin k, covMatrix Q i j ≠ 0)
    -- LEAN-ONLY: argument quantified by the conclusion, not a hypothesis
    (x : ℝ) :
    Tendsto (fun n => normMeanRootCDF (F n) nrm n x) atTop
      (𝓝 (normLimitCDF (covMatrix Q) nrm x)) := by
  classical
  obtain ⟨i₀, j₀, hij⟩ := hS
  have hSne : covMatrix Q ≠ 0 := fun h => hij (by rw [h]; simp)
  have hpsd := posSemidef_covMatrix hQ2
  have hnrm_cont : Continuous nrm := continuous_of_seminorm hnrm_add hnrm_smul
  -- all the laws in sight are probability measures (`n = 0` gives the Dirac at the empty tuple)
  haveI hpi : ∀ n : ℕ, IsProbabilityMeasure (Measure.pi fun _ : Fin n => F n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [Measure.pi_of_empty]; infer_instance
    · haveI := hF.1 n hn
      haveI : ∀ _ : Fin n, IsProbabilityMeasure (F n) := fun _ => ‹_›
      infer_instance
  haveI hroot : ∀ n : ℕ, IsProbabilityMeasure (meanVecRootLaw (F n) n) := by
    intro n
    haveI := hpi n
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  -- weak convergence of the root laws, packaged as `ProbabilityMeasure` convergence
  set ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) :=
    ⟨multivariateGaussian 0 (covMatrix Q), inferInstance⟩ with hν
  set μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) :=
    fun n => ⟨meanVecRootLaw (F n) n, hroot n⟩ with hμs
  have hconv : Tendsto μs atTop (𝓝 ν) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f =>
      meanVec_root_tendsto hQ2 hF f
  -- the frontier of the sublevel set is contained in the sphere, which is Gaussian-null
  have hfrontier :
      (ν : Measure (EuclideanSpace ℝ (Fin k)))
        (frontier {z : EuclideanSpace ℝ (Fin k) | nrm z ≤ x}) = 0 := by
    refine measure_mono_null ?_
      (measure_multivariateGaussian_norm_level hpsd hSne hnrm_add hnrm_smul hnrm_def x)
    intro z hz
    have hclosed : IsClosed {z : EuclideanSpace ℝ (Fin k) | nrm z ≤ x} :=
      isClosed_le hnrm_cont continuous_const
    have hz1 : nrm z ≤ x := by
      have h := hz.1
      rwa [hclosed.closure_eq] at h
    exact le_antisymm hz1 (not_lt.1 fun hlt => hz.2
      (mem_interior_iff_mem_nhds.2
        (Filter.mem_of_superset ((isOpen_lt hnrm_cont continuous_const).mem_nhds hlt)
          (fun w hw => (le_of_lt hw : nrm w ≤ x)))))
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv hfrontier
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport

/-- **Consistency of the multivariate bootstrap.**

For an independent identically distributed sample from a square-integrable law on `ℝᵏ` with a
nondegenerate covariance, the bootstrap sampling distribution of the norm of the root is
uniformly close to the true one, almost surely, for every norm. -/
theorem bootstrap_meanVec_consistent [IsProbabilityMeasure Pr] [IsProbabilityMeasure Q]
    -- LEAN-ONLY: the observations are measurable
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent identically distributed observations with law `Q`
    (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) Q Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: square-integrable sampling law
    (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q)
    -- USER-INPUT: the norm is subadditive
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    -- USER-INPUT: the norm is absolutely homogeneous
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    -- USER-INPUT: the norm is positive definite
    (hnrm_def : ∀ y, nrm y = 0 → y = 0)
    -- USER-INPUT: nondegeneracy of the covariance
    (hS : ∃ i j : Fin k, covMatrix Q i j ≠ 0) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n => supCDFDist (normMeanRootCDF Q nrm n)
      (normMeanRootCDF (empiricalMeasure fun i : Fin n => X i ω) nrm n)) atTop (𝓝 0) := by
  classical
  have hnrm_cont : Continuous nrm := continuous_of_seminorm hnrm_add hnrm_smul
  -- the limiting distribution function of the norm
  set Jlim : ℝ → ℝ := normLimitCDF (covMatrix Q) nrm with hJlim
  have hcont : Continuous Jlim :=
    continuous_normLimitCDF hQ2 hnrm_add hnrm_smul hnrm_def hS
  have hJcdf : IsCDF Jlim := by
    haveI : IsProbabilityMeasure
        ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (covMatrix Q)).map nrm) :=
      Measure.isProbabilityMeasure_map hnrm_cont.measurable.aemeasurable
    have heq : Jlim = fun x =>
        (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (covMatrix Q)).map nrm)
          (Set.Iic x)).toReal := by
      funext x
      rw [hJlim, normLimitCDF, Measure.map_apply hnrm_cont.measurable measurableSet_Iic]
      rfl
    rw [heq]
    exact isCDF_toReal_measure_Iic _
  -- the sampling distribution functions of the norm are distribution functions
  have hFcdf : ∀ (F : Measure (EuclideanSpace ℝ (Fin k))) (n : ℕ),
      IsProbabilityMeasure (Measure.pi fun _ : Fin n => F) →
      IsCDF (normMeanRootCDF F nrm n) := by
    intro F n hpi
    haveI := hpi
    haveI : IsProbabilityMeasure (meanVecRootLaw F n) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    haveI : IsProbabilityMeasure ((meanVecRootLaw F n).map nrm) :=
      Measure.isProbabilityMeasure_map hnrm_cont.measurable.aemeasurable
    have heq : normMeanRootCDF F nrm n
        = fun x => (((meanVecRootLaw F n).map nrm) (Set.Iic x)).toReal := by
      funext x
      rw [normMeanRootCDF, Measure.map_apply hnrm_cont.measurable measurableSet_Iic]
      rfl
    rw [heq]
    exact isCDF_toReal_measure_Iic _
  have hpiQ : ∀ n : ℕ, IsProbabilityMeasure (Measure.pi fun _ : Fin n => Q) := by
    intro n
    haveI : ∀ _ : Fin n, IsProbabilityMeasure Q := fun _ => ‹_›
    infer_instance
  have hconstmem : (fun _ : ℕ => Q) ∈ meanVecSeqClass Q :=
    ⟨fun _ _ => inferInstance, fun _ => hQ2, fun _ => tendsto_const_nhds,
      fun _ => tendsto_const_nhds, fun _ _ => tendsto_const_nhds⟩
  have hQconv : ∀ x, Tendsto (fun n => normMeanRootCDF Q nrm n x) atTop (𝓝 (Jlim x)) :=
    fun x => norm_root_cdf_tendsto hQ2 hconstmem hnrm_add hnrm_smul hnrm_def hS x
  filter_upwards [empirical_mem_meanVecSeqClass hmeas hindep hlaw hident hQ2] with ω hω
  have hpiE : ∀ n : ℕ, IsProbabilityMeasure
      (Measure.pi fun _ : Fin n => empiricalMeasure fun i : Fin n => X i ω) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [Measure.pi_of_empty]; infer_instance
    · haveI := hω.1 n hn
      haveI : ∀ _ : Fin n, IsProbabilityMeasure (empiricalMeasure fun i : Fin n => X i ω) :=
        fun _ => ‹_›
      infer_instance
  have hEconv : ∀ x, Tendsto
      (fun n => normMeanRootCDF (empiricalMeasure fun i : Fin n => X i ω) nrm n x) atTop
      (𝓝 (Jlim x)) := fun x => norm_root_cdf_tendsto hQ2 hω hnrm_add hnrm_smul hnrm_def hS x
  have hQ' : ∀ n, IsCDF (normMeanRootCDF Q nrm n) := fun n => hFcdf Q n (hpiQ n)
  have hE' : ∀ n, IsCDF (normMeanRootCDF (empiricalMeasure fun i : Fin n => X i ω) nrm n) :=
    fun n => hFcdf _ n (hpiE n)
  have hA : Tendsto (fun n => supCDFDist (normMeanRootCDF Q nrm n) Jlim) atTop (𝓝 0) :=
    tendsto_supCDFDist_zero hQ' hcont hJcdf hQconv
  have hB : Tendsto (fun n => supCDFDist Jlim
      (normMeanRootCDF (empiricalMeasure fun i : Fin n => X i ω) nrm n)) atTop (𝓝 0) := by
    have h := tendsto_supCDFDist_zero hE' hcont hJcdf hEconv
    simpa only [supCDFDist_comm] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
    (h := fun n => supCDFDist (normMeanRootCDF Q nrm n) Jlim
      + supCDFDist Jlim (normMeanRootCDF (empiricalMeasure fun i : Fin n => X i ω) nrm n))
    tendsto_const_nhds (by simpa using hA.add hB) (fun n => ?_) (fun n => ?_)
  · exact supCDFDist_nonneg (hQ' n) (hE' n)
  · exact supCDFDist_triangle_of_isCDF (hQ' n) hJcdf (hE' n)

end MeanVector

/-! ## Smooth functions of means -/

/-- The **vector of sample means** of the coordinate functions `h`. -/
noncomputable def meanStatistic {n : ℕ} (h : Fin p → 𝓢 → ℝ) (z : Fin n → 𝓢) :
    EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun j => (n : ℝ)⁻¹ * (∑ i, h j (z i))

/-- The **bootstrap resampling law**: `n` independent draws from the empirical measure of the
observed sample. -/
noncomputable def bootstrapLaw {n : ℕ} (x : Fin n → 𝓢) : Measure (Fin n → 𝓢) :=
  Measure.pi fun _ : Fin n => empiricalMeasure x

section SmoothFunctions

variable {P : Measure 𝓢} {Pr : Measure Ω} {X : ℕ → Ω → 𝓢} {h : Fin p → 𝓢 → ℝ}
  {f : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q)}
  {Df : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin q)} {D : Matrix (Fin q) (Fin p) ℝ}
  {covH : Matrix (Fin p) (Fin p) ℝ} {nrm : EuclideanSpace ℝ (Fin q) → ℝ}

/-! ### The vector of coordinate functions as a mean-vector problem

The delta method is the mean-vector theory of this file, transported along `s ↦ (h₁ s, …, h_p s)`
and then pushed through a differentiable map. The lemmas of this block do the transport: they
identify the law of the vector of sample means with a `meanVecRootLaw`, its covariance matrix with
`covH`, and the image of the Gaussian limit under the differential with the Gaussian limit of the
image. -/

/-- Coordinate extensionality on a Euclidean space. -/
private lemma euclidean_ext {x y : EuclideanSpace ℝ (Fin p)}
    (hxy : ∀ j, WithLp.ofLp x j = WithLp.ofLp y j) : x = y := by
  have h : WithLp.ofLp x = WithLp.ofLp y := funext hxy
  simpa using congrArg (WithLp.toLp 2) h

/-- The **vector of coordinate functions** `s ↦ (h₁ s, …, h_p s)`, as a point of `ℝᵖ`. -/
private noncomputable def hVec (h : Fin p → 𝓢 → ℝ) (s : 𝓢) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun j => h j s

private lemma ofLp_hVec (s : 𝓢) (j : Fin p) : WithLp.ofLp (hVec h s) j = h j s := rfl

private lemma measurable_hVec (hhmeas : ∀ j, Measurable (h j)) : Measurable (hVec h) := by
  unfold hVec
  fun_prop

private lemma measurable_ofLp_apply (a : Fin p) :
    Measurable fun y : EuclideanSpace ℝ (Fin p) => WithLp.ofLp y a := by fun_prop

/-- The vector of coordinate functions is square-integrable as soon as each coordinate is. -/
private lemma memLp_hVec (hhmeas : ∀ j, Measurable (h j)) (hh2 : ∀ j, MemLp (h j) 2 P) :
    MemLp (hVec h) 2 P := by
  have hmeas : Measurable (hVec h) := measurable_hVec hhmeas
  rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable]
  have hnorm : ∀ s : 𝓢, ‖hVec h s‖ ^ 2 = ∑ j, (h j s) ^ 2 := by
    intro s
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => by positivity))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ofLp_hVec, Real.norm_eq_abs, sq_abs]
  simp only [hnorm]
  exact integrable_finset_sum _ (fun j _ => (hh2 j).integrable_sq)

/-- The law of the vector of coordinate functions is a probability measure. -/
private lemma isProbabilityMeasure_hVec [IsProbabilityMeasure P] (hhmeas : ∀ j, Measurable (h j)) :
    IsProbabilityMeasure (P.map (hVec h)) :=
  Measure.isProbabilityMeasure_map (measurable_hVec hhmeas).aemeasurable

/-- The law of the vector of coordinate functions is square-integrable. -/
private lemma memLp_id_map_hVec (hhmeas : ∀ j, Measurable (h j)) (hh2 : ∀ j, MemLp (h j) 2 P) :
    MemLp (fun y : EuclideanSpace ℝ (Fin p) => y) 2 (P.map (hVec h)) := by
  rw [memLp_map_measure_iff (by fun_prop) (measurable_hVec hhmeas).aemeasurable]
  simpa [Function.comp_def] using memLp_hVec hhmeas hh2

/-- The covariance matrix of the law of the vector of coordinate functions is the covariance
matrix of the coordinate functions. -/
private lemma covMatrix_map_hVec [IsProbabilityMeasure P] (hhmeas : ∀ j, Measurable (h j))
    (i j : Fin p) :
    covMatrix (P.map (hVec h)) i j = cov[h i, h j; P] := by
  rw [covMatrix, Matrix.of_apply, covariance_map (measurable_ofLp_apply i).aestronglyMeasurable
    (measurable_ofLp_apply j).aestronglyMeasurable (measurable_hVec hhmeas).aemeasurable]
  rfl

/-- The mean vector of the law of the vector of coordinate functions is the parameter. -/
private lemma integral_map_hVec [IsProbabilityMeasure P] (hhmeas : ∀ j, Measurable (h j))
    (hh2 : ∀ j, MemLp (h j) 2 P) :
    ∫ z, z ∂(P.map (hVec h)) = WithLp.toLp 2 fun j => ∫ s, h j s ∂P := by
  have hmeas : Measurable (hVec h) := measurable_hVec hhmeas
  have hint : Integrable (hVec h) P := (memLp_hVec hhmeas hh2).integrable (by norm_num)
  rw [integral_map hmeas.aemeasurable (by fun_prop)]
  refine euclidean_ext (fun j => ?_)
  have hproj : ∫ s, WithLp.ofLp (hVec h s) j ∂P = WithLp.ofLp (∫ s, hVec h s ∂P) j :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin p) j).integral_comp_comm hint
  rw [← hproj]
  simp only [ofLp_hVec]

/-- **The vector of sample means is a mean-vector root.**

The law of `n^{1/2}(θ̂ₙ − θ)`, where `θ̂ₙ` is the vector of sample means of the coordinate
functions under `n` independent draws from `P`, is the mean-vector root law of the image of `P`
under `s ↦ (h₁ s, …, h_p s)`. This is the identification that makes the whole multivariate
chain of this file available for smooth functions of means. -/
private lemma map_meanStatistic_eq_meanVecRootLaw [IsProbabilityMeasure P]
    (hhmeas : ∀ j, Measurable (h j)) (hh2 : ∀ j, MemLp (h j) 2 P) (n : ℕ) :
    (Measure.pi fun _ : Fin n => P).map
        (fun w => Real.sqrt n • (meanStatistic h w - WithLp.toLp 2 fun j => ∫ s, h j s ∂P))
      = meanVecRootLaw (P.map (hVec h)) n := by
  have hmeas : Measurable (hVec h) := measurable_hVec hhmeas
  have hpi : (Measure.pi fun _ : Fin n => P).map (fun w (i : Fin n) => hVec h (w i))
      = Measure.pi fun _ : Fin n => P.map (hVec h) :=
    Measure.pi_map_pi (fun _ => hmeas.aemeasurable)
  have hstat : ∀ w : Fin n → 𝓢,
      meanStatistic h w = (n : ℝ)⁻¹ • ∑ i, hVec h (w i) := by
    intro w
    refine euclidean_ext (fun j => ?_)
    have hsum : WithLp.ofLp (∑ i, hVec h (w i)) j = ∑ i, WithLp.ofLp (hVec h (w i)) j :=
      map_sum (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin p) j) _ _
    simp only [meanStatistic, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul, hsum, ofLp_hVec]
  have hcomp : ((Measure.pi fun _ : Fin n => P).map (fun w (i : Fin n) => hVec h (w i))).map
        (fun y : Fin n → EuclideanSpace ℝ (Fin p) =>
          Real.sqrt n • ((n : ℝ)⁻¹ • (∑ i, y i) - ∫ z, z ∂(P.map (hVec h))))
      = (Measure.pi fun _ : Fin n => P).map
        (fun w => Real.sqrt n • ((n : ℝ)⁻¹ • (∑ i, hVec h (w i))
          - ∫ z, z ∂(P.map (hVec h)))) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def]
  rw [meanVecRootLaw, ← hpi, hcomp, integral_map_hVec hhmeas hh2]
  congr 1
  funext w
  rw [hstat w]

/-! ### The same transport at an empirical measure

The bootstrap runs the transport above at the empirical measure of the observed sample. Three
facts are needed: the image of an empirical measure under the vector of coordinate functions is
the empirical measure of the transformed sample; the mean of the coordinate functions under it is
the sample mean vector; and every measurable function is square-integrable against it. -/

private lemma isProbabilityMeasure_empiricalMeasure' {n : ℕ} (hn : 0 < n) (x : Fin n → 𝓢) :
    IsProbabilityMeasure (empiricalMeasure x) := by
  refine ⟨?_⟩
  unfold empiricalMeasure
  simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)]

private lemma map_empiricalMeasure {n : ℕ} {𝓨 : Type*} [MeasurableSpace 𝓨] {g : 𝓢 → 𝓨}
    (hg : Measurable g) (x : Fin n → 𝓢) :
    (empiricalMeasure x).map g = empiricalMeasure fun i => g (x i) := by
  have hsum : ∀ s : Finset (Fin n),
      (∑ i ∈ s, Measure.dirac (x i)).map g = ∑ i ∈ s, Measure.dirac (g (x i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hg, ih,
          Measure.map_dirac' hg]
  unfold empiricalMeasure
  rw [Measure.map_smul, hsum]

private lemma integrable_empiricalMeasure' {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (x : Fin n → 𝓢) {g : 𝓢 → E} (hg : StronglyMeasurable g) :
    Integrable g (empiricalMeasure x) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [empiricalMeasure]
  · unfold empiricalMeasure
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (by exact_mod_cast hn.ne'))
    exact integrable_finset_sum_measure.2 fun i _ => integrable_dirac' hg (by simp)

private lemma integral_empiricalMeasure' {n : ℕ} (x : Fin n → 𝓢) {g : 𝓢 → ℝ}
    (hg : Measurable g) :
    ∫ s, g s ∂(empiricalMeasure x) = (n : ℝ)⁻¹ * ∑ i, g (x i) := by
  unfold empiricalMeasure
  rw [integral_smul_measure, integral_finset_sum_measure
    (fun i _ => integrable_dirac' hg.stronglyMeasurable (by simp))]
  simp only [integral_dirac' _ _ hg.stronglyMeasurable]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

private lemma memLp_empiricalMeasure' {n : ℕ} (x : Fin n → 𝓢) {g : 𝓢 → ℝ} (hg : Measurable g) :
    MemLp g 2 (empiricalMeasure x) := by
  rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable]
  exact integrable_empiricalMeasure' x (by fun_prop)

/-- The sample mean vector is the mean of the coordinate functions under the empirical measure. -/
private lemma toLp_integral_empiricalMeasure {n : ℕ} (hhmeas : ∀ j, Measurable (h j))
    (x : Fin n → 𝓢) :
    (WithLp.toLp 2 fun j => ∫ s, h j s ∂(empiricalMeasure x)) = meanStatistic h x := by
  refine euclidean_ext fun j => ?_
  simp only [WithLp.ofLp_toLp, meanStatistic, integral_empiricalMeasure' x (hhmeas j)]

/-- The sample mean vector as a scaled sum of the transformed observations. -/
private lemma meanStatistic_eq_smul_sum {n : ℕ} (x : Fin n → 𝓢) :
    meanStatistic h x = (n : ℝ)⁻¹ • ∑ i, hVec h (x i) := by
  refine euclidean_ext fun j => ?_
  have hsum : WithLp.ofLp (∑ i, hVec h (x i)) j = ∑ i, WithLp.ofLp (hVec h (x i)) j :=
    map_sum (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin p) j) _ _
  simp only [meanStatistic, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul, hsum, ofLp_hVec]

/-- The real inner product of a Euclidean space, as a sum of products of coordinates. -/
private lemma real_inner_euclidean {m : ℕ} (u v : EuclideanSpace ℝ (Fin m)) :
    (inner ℝ u v : ℝ) = ∑ i, WithLp.ofLp u i * WithLp.ofLp v i := by
  have hdef : (inner ℝ u v : ℝ) = ∑ i, WithLp.ofLp v i * star (WithLp.ofLp u i) := rfl
  rw [hdef]
  exact Finset.sum_congr rfl (fun i _ => by simp [mul_comm])

/-- **The Gaussian limit transforms by the differential.**

The image of the centred Gaussian law with covariance `covH` under the differential is the centred
Gaussian law with covariance `D covH Dᵀ`: both characteristic functions are Gaussian, and the
quadratic forms agree because `t ⬝ᵥ (D S Dᵀ) *ᵥ t = (Dᵀ t) ⬝ᵥ S *ᵥ (Dᵀ t)`. -/
private lemma map_multivariateGaussian_deriv (hpsd : covH.PosSemidef)
    (hD : ∀ v, Df v = WithLp.toLp 2 (D.mulVec (WithLp.ofLp v))) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) covH).map Df
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) (D * covH * D.transpose) := by
  classical
  have hpsd' : (D * covH * D.transpose).PosSemidef := by
    have hc := hpsd.conjTranspose_mul_mul_same (B := D.transpose)
    simpa [Matrix.conjTranspose_transpose] using hc
  haveI : IsProbabilityMeasure ((multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin p)) covH).map Df) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun (funext fun t => ?_)
  -- pairing with `Df y` is pairing with the transposed direction
  set tD : EuclideanSpace ℝ (Fin p) := WithLp.toLp 2 (D.transpose.mulVec (WithLp.ofLp t)) with htD
  have hinner : ∀ y : EuclideanSpace ℝ (Fin p),
      (inner ℝ (Df y) t : ℝ) = inner ℝ y tD := by
    intro y
    rw [real_inner_euclidean, real_inner_euclidean, hD y]
    simp only [htD, WithLp.ofLp_toLp, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => by ring))
  -- both characteristic functions are the Gaussian one
  have hcf : charFun ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) covH).map Df) t
      = charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) covH) tD := by
    rw [charFun_apply, charFun_apply,
      integral_map (by fun_prop) (by fun_prop : AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin q) => Complex.exp ((inner ℝ z t : ℝ) * Complex.I)) _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hinner y]
  rw [hcf, charFun_multivariateGaussian hpsd, charFun_multivariateGaussian hpsd']
  have hquad : WithLp.ofLp tD ⬝ᵥ covH.mulVec (WithLp.ofLp tD)
      = WithLp.ofLp t ⬝ᵥ (D * covH * D.transpose).mulVec (WithLp.ofLp t) := by
    have hu : WithLp.ofLp tD = D.transpose.mulVec (WithLp.ofLp t) := by
      simp only [htD, WithLp.ofLp_toLp]
    rw [hu, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.transpose_transpose,
      Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      Matrix.vecMul_transpose, dotProduct_comm,
      dotProduct_comm (D.mulVec _) (WithLp.ofLp t), Matrix.dotProduct_mulVec]
  rw [hquad]
  simp

/-! ### The Taylor step

The delta method compares the root of the smooth function with the linear image of the
mean-vector root. The comparison is run on bounded **Lipschitz** test functions — enough for weak
convergence by `MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto` — and needs two
carriers: the rescaling `z ↦ √n (f(θ + z/√n) − f(θ))`, whose composition with the mean-vector
root *is* the root of the smooth function, and a bounded continuous tail cutoff that converts the
tightness supplied by the mean-vector limit into a uniform bound outside a ball. -/

/-- The **delta-method rescaling** `z ↦ √n (f(θ + z/√n) − f(θ))`. -/
private noncomputable def deltaMap (f : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q))
    (θ : EuclideanSpace ℝ (Fin p)) (n : ℕ) (z : EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin q) :=
  Real.sqrt n • (f (θ + (Real.sqrt n)⁻¹ • z) - f θ)

private lemma measurable_deltaMap (hfmeas : Measurable f) (θ : EuclideanSpace ℝ (Fin p)) (n : ℕ) :
    Measurable (deltaMap f θ n) := by
  unfold deltaMap
  fun_prop

private lemma measurable_meanStatistic {n : ℕ} (hhmeas : ∀ j, Measurable (h j)) :
    Measurable (meanStatistic h (n := n)) := by
  unfold meanStatistic
  fun_prop

/-- The **tail cutoff** `z ↦ min 1 (max 0 (‖z‖ − M + 1))`: a bounded continuous function that
vanishes on the ball of radius `M − 1` and equals `1` outside the ball of radius `M`. -/
private noncomputable def tailCutoff (M : ℝ) : EuclideanSpace ℝ (Fin p) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => min 1 (max 0 (‖z‖ - M + 1))) (by fun_prop) 1 (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (le_max_left _ _))]
      exact min_le_left _ _)

private lemma tailCutoff_apply (M : ℝ) (z : EuclideanSpace ℝ (Fin p)) :
    tailCutoff M z = min 1 (max 0 (‖z‖ - M + 1)) := rfl

private lemma tailCutoff_nonneg (M : ℝ) (z : EuclideanSpace ℝ (Fin p)) :
    0 ≤ tailCutoff M z := le_min zero_le_one (le_max_left _ _)

private lemma tailCutoff_eq_one {M : ℝ} {z : EuclideanSpace ℝ (Fin p)} (hz : M < ‖z‖) :
    tailCutoff M z = 1 := by
  rw [tailCutoff_apply, max_eq_right (by linarith), min_eq_left (by linarith)]

/-- The mass the tail cutoff sees vanishes as the radius grows: for a finite measure, dominated
convergence applies because each point is eventually outside every cutoff. -/
private lemma tendsto_integral_tailCutoff (μ : Measure (EuclideanSpace ℝ (Fin p)))
    [IsFiniteMeasure μ] :
    Tendsto (fun j : ℕ => ∫ z, tailCutoff (j : ℝ) z ∂μ) atTop (𝓝 0) := by
  have hzero : (0 : ℝ) = ∫ _z : EuclideanSpace ℝ (Fin p), (0 : ℝ) ∂μ := by simp
  rw [hzero]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun j => (tailCutoff (j : ℝ)).continuous.aestronglyMeasurable) (integrable_const _)
    (fun j => Filter.Eventually.of_forall fun z => ?_) (Filter.Eventually.of_forall fun z => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (tailCutoff_nonneg _ z), tailCutoff_apply]
    exact min_le_left _ _
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈‖z‖ + 1⌉₊] with j hj
    have hjr : ‖z‖ + 1 ≤ (j : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.2 hj)
    rw [tailCutoff_apply, max_eq_left (by linarith), min_eq_right zero_le_one]

/-- **The delta-method engine.**

If the mean-vector roots `νₙ` converge weakly to a limit `Gp`, and the centres `cₙ` converge to a
point `θ` at which `f` is differentiable with a differential that is continuous there, then the
rescaled images `√n (f(cₙ + ·/√n) − f(cₙ))` of the roots converge weakly to the image of `Gp`
under the differential.

The comparison is run on bounded **Lipschitz** test functions, which suffice for weak convergence
by `MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto`; the tail cutoff turns the
tightness carried by the weak limit into a uniform bound outside a ball, and inside the ball the
mean-value inequality `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` gives the Taylor
estimate **uniformly in the centre**, which is what the drifting `cₙ` needs. -/
private theorem tendsto_integral_map_deltaMap {θ : EuclideanSpace ℝ (Fin p)}
    (hfmeas : Measurable f) (hf : HasFDerivAt f Df θ)
    (hf_nhds : ∀ᶠ y in 𝓝 θ, DifferentiableAt ℝ f y)
    (hf_cont : ContinuousAt (fderiv ℝ f) θ)
    {ν : ℕ → Measure (EuclideanSpace ℝ (Fin p))} (hνprob : ∀ n, IsProbabilityMeasure (ν n))
    {Gp : Measure (EuclideanSpace ℝ (Fin p))} (hGp : IsProbabilityMeasure Gp)
    (hν : ∀ ψ : EuclideanSpace ℝ (Fin p) →ᵇ ℝ,
      Tendsto (fun n => ∫ z, ψ z ∂(ν n)) atTop (𝓝 (∫ z, ψ z ∂Gp)))
    {c : ℕ → EuclideanSpace ℝ (Fin p)} (hc : Tendsto c atTop (𝓝 θ))
    (φ : EuclideanSpace ℝ (Fin q) →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ y, φ y ∂((ν n).map (deltaMap f (c n) n))) atTop
      (𝓝 (∫ y, φ y ∂(Gp.map Df))) := by
  classical
  haveI := hGp
  haveI hνi : ∀ n, IsProbabilityMeasure (ν n) := hνprob
  haveI hmapprob : ∀ n : ℕ, IsProbabilityMeasure ((ν n).map (deltaMap f (c n) n)) := fun n =>
    Measure.isProbabilityMeasure_map (measurable_deltaMap hfmeas _ n).aemeasurable
  haveI hDprob : IsProbabilityMeasure (Gp.map Df) :=
    Measure.isProbabilityMeasure_map Df.continuous.measurable.aemeasurable
  set Ps : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin q)) :=
    fun n => ⟨(ν n).map (deltaMap f (c n) n), hmapprob n⟩ with hPs
  set Pl : ProbabilityMeasure (EuclideanSpace ℝ (Fin q)) := ⟨Gp.map Df, hDprob⟩ with hPl
  have hweak : Tendsto Ps atTop (𝓝 Pl) := by
    refine tendsto_iff_forall_lipschitz_integral_tendsto.2 ?_
    rintro ψ ⟨C, hCb⟩ ⟨L, hL⟩
    have hψcont : Continuous ψ := hL.continuous
    have hCnn : (0 : ℝ) ≤ C := by simpa using hCb 0 0
    have hψabs : ∀ a b, |ψ a - ψ b| ≤ C := fun a b => by
      simpa [Real.dist_eq] using hCb a b
    have hψbdd : ∀ a, ‖ψ a‖ ≤ ‖ψ 0‖ + C := by
      intro a
      have hid : ψ a = ψ 0 + (ψ a - ψ 0) := by ring
      have h2 : ‖ψ a - ψ 0‖ ≤ C := by rw [Real.norm_eq_abs]; exact hψabs a 0
      calc ‖ψ a‖ = ‖ψ 0 + (ψ a - ψ 0)‖ := by rw [← hid]
        _ ≤ ‖ψ 0‖ + ‖ψ a - ψ 0‖ := norm_add_le _ _
        _ ≤ ‖ψ 0‖ + C := by linarith
    set ψb : EuclideanSpace ℝ (Fin q) →ᵇ ℝ :=
      BoundedContinuousFunction.ofNormedAddCommGroup ψ hψcont (‖ψ 0‖ + C) hψbdd with hψbdef
    set ψD : EuclideanSpace ℝ (Fin p) →ᵇ ℝ := ψb.compContinuous ⟨Df, Df.continuous⟩ with hψDdef
    have hψDapp : ∀ z, ψD z = ψ (Df z) := fun _ => rfl
    -- the linear comparison term converges by the mean-vector limit
    have hrhs : ∫ y, ψ y ∂(Gp.map Df) = ∫ z, ψD z ∂Gp := by
      rw [integral_map Df.continuous.measurable.aemeasurable hψcont.aestronglyMeasurable]
      rfl
    have hB : Tendsto (fun n => ∫ z, ψD z ∂(ν n)) atTop (𝓝 (∫ y, ψ y ∂(Gp.map Df))) := by
      rw [hrhs]; exact hν ψD
    have hlhs : ∀ n : ℕ, ∫ y, ψ y ∂((ν n).map (deltaMap f (c n) n))
        = ∫ z, ψ (deltaMap f (c n) n z) ∂(ν n) := fun n =>
      integral_map (measurable_deltaMap hfmeas _ n).aemeasurable hψcont.aestronglyMeasurable
    -- the Taylor difference is uniformly negligible
    have hA : Tendsto (fun n : ℕ => ∫ y, ψ y ∂((ν n).map (deltaMap f (c n) n))
        - ∫ z, ψD z ∂(ν n)) atTop (𝓝 0) := by
      rw [NormedAddGroup.tendsto_nhds_zero]
      intro ε hε
      -- a radius outside which the limit has little mass
      obtain ⟨M, hM0, hMtail⟩ : ∃ M : ℝ, 0 ≤ M ∧ (C + 1) * ∫ z, tailCutoff M z ∂Gp < ε / 3 := by
        have hlim : Tendsto (fun j : ℕ => (C + 1) * ∫ z, tailCutoff (j : ℝ) z ∂Gp) atTop (𝓝 0) := by
          simpa using (tendsto_integral_tailCutoff Gp).const_mul (C + 1)
        obtain ⟨j, hj⟩ := (hlim.eventually_lt_const (by positivity : (0 : ℝ) < ε / 3)).exists
        exact ⟨(j : ℝ), Nat.cast_nonneg j, hj⟩
      -- the matching Taylor tolerance
      have hden : (0 : ℝ) < (L : ℝ) * M + 1 := by positivity
      obtain ⟨η, hη, hηM⟩ : ∃ η : ℝ, 0 < η ∧ (L : ℝ) * η * M ≤ ε / 3 := by
        refine ⟨(ε / 3) / ((L : ℝ) * M + 1), by positivity, ?_⟩
        have key : (L : ℝ) * ((ε / 3) / ((L : ℝ) * M + 1)) * M
            = ((L : ℝ) * M) * (ε / 3) / ((L : ℝ) * M + 1) := by ring
        rw [key, div_le_iff₀ hden]
        nlinarith [hε.le, mul_nonneg (NNReal.coe_nonneg L) hM0]
      -- uniform differentiability on a ball around the limiting centre
      have hcontev : ∀ᶠ y in 𝓝 θ, ‖fderiv ℝ f y - Df‖ ≤ η := by
        filter_upwards [Metric.tendsto_nhds.1 hf_cont η hη] with y hy
        rw [← hf.fderiv, ← dist_eq_norm]
        exact hy.le
      obtain ⟨r, hr, hrball⟩ := Metric.eventually_nhds_iff.1 (hf_nhds.and hcontev)
      have hMVT : ∀ x ∈ Metric.ball θ r, ∀ y ∈ Metric.ball θ r,
          ‖f y - f x - Df (y - x)‖ ≤ η * ‖y - x‖ := by
        intro x hx y hy
        exact (convex_ball θ r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
          (fun u hu => (hrball (Metric.mem_ball.1 hu)).1.hasFDerivAt.hasFDerivWithinAt)
          (fun u hu => (hrball (Metric.mem_ball.1 hu)).2) hx hy
      -- the three eventual constraints
      have hcutev : ∀ᶠ n : ℕ in atTop,
          (C + 1) * ∫ z, tailCutoff M z ∂(ν n) < 2 * ε / 3 :=
        ((hν (tailCutoff M)).const_mul (C + 1)).eventually_lt_const (by linarith)
      have hsqrt : Tendsto (fun n : ℕ => M * (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
        simpa using h1.const_mul M
      have hcev : ∀ᶠ n : ℕ in atTop, dist (c n) θ < r / 2 :=
        Metric.tendsto_nhds.1 hc (r / 2) (by linarith)
      have hMev : ∀ᶠ n : ℕ in atTop, M * (Real.sqrt n)⁻¹ < r / 2 :=
        hsqrt.eventually_lt_const (by linarith)
      filter_upwards [hcutev, hcev, hMev, eventually_gt_atTop 0] with n hcutn hcn hMn hn
      have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
      have hsni : (0 : ℝ) ≤ (Real.sqrt n)⁻¹ := by positivity
      -- the pointwise estimate: Taylor inside the ball, oscillation outside
      have hpt : ∀ z : EuclideanSpace ℝ (Fin p),
          ‖ψ (deltaMap f (c n) n z) - ψD z‖ ≤ (L : ℝ) * η * M + C * tailCutoff M z := by
        intro z
        rcases le_or_gt ‖z‖ M with hz | hz
        · have hvn : ‖(Real.sqrt n)⁻¹ • z‖ < r / 2 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsni]
            calc (Real.sqrt n)⁻¹ * ‖z‖ ≤ (Real.sqrt n)⁻¹ * M := by gcongr
              _ = M * (Real.sqrt n)⁻¹ := mul_comm _ _
              _ < r / 2 := hMn
          have hx : c n ∈ Metric.ball θ r := Metric.mem_ball.2 (by linarith)
          have hd1 : dist (c n + (Real.sqrt n)⁻¹ • z) (c n) < r / 2 := by
            rw [dist_eq_norm, add_sub_cancel_left]
            exact hvn
          have hy : c n + (Real.sqrt n)⁻¹ • z ∈ Metric.ball θ r := by
            refine Metric.mem_ball.2 ?_
            calc dist (c n + (Real.sqrt n)⁻¹ • z) θ
                ≤ dist (c n + (Real.sqrt n)⁻¹ • z) (c n) + dist (c n) θ := dist_triangle _ _ _
              _ < r / 2 + r / 2 := add_lt_add hd1 hcn
              _ = r := by ring
          have hmv := hMVT _ hx _ hy
          rw [add_sub_cancel_left] at hmv
          have hdel : ‖deltaMap f (c n) n z - Df z‖ ≤ η * ‖z‖ := by
            have hid : deltaMap f (c n) n z - Df z
                = Real.sqrt n • (f (c n + (Real.sqrt n)⁻¹ • z) - f (c n)
                    - Df ((Real.sqrt n)⁻¹ • z)) := by
              rw [deltaMap, map_smul, smul_sub, smul_sub, smul_smul,
                mul_inv_cancel₀ hsn.ne', one_smul, smul_sub]
            rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsn.le]
            calc Real.sqrt n * ‖f (c n + (Real.sqrt n)⁻¹ • z) - f (c n)
                    - Df ((Real.sqrt n)⁻¹ • z)‖
                ≤ Real.sqrt n * (η * ‖(Real.sqrt n)⁻¹ • z‖) := by gcongr
              _ = η * ‖z‖ := by
                  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsni]
                  field_simp
          have hlip : ‖ψ (deltaMap f (c n) n z) - ψD z‖
              ≤ (L : ℝ) * ‖deltaMap f (c n) n z - Df z‖ := by
            rw [hψDapp, Real.norm_eq_abs, ← Real.dist_eq, ← dist_eq_norm]
            exact hL.dist_le_mul _ _
          have h1 : (L : ℝ) * ‖deltaMap f (c n) n z - Df z‖ ≤ (L : ℝ) * (η * M) := by
            refine mul_le_mul_of_nonneg_left (hdel.trans ?_) (NNReal.coe_nonneg L)
            exact mul_le_mul_of_nonneg_left hz hη.le
          have h2 : (0 : ℝ) ≤ C * tailCutoff M z := mul_nonneg hCnn (tailCutoff_nonneg M z)
          calc ‖ψ (deltaMap f (c n) n z) - ψD z‖ ≤ (L : ℝ) * (η * M) := hlip.trans h1
            _ ≤ (L : ℝ) * η * M + C * tailCutoff M z := by rw [mul_assoc]; linarith
        · have h1 : ‖ψ (deltaMap f (c n) n z) - ψD z‖ ≤ C := by
            rw [hψDapp, Real.norm_eq_abs]; exact hψabs _ _
          have h3 : (0 : ℝ) ≤ (L : ℝ) * η * M := by positivity
          rw [tailCutoff_eq_one hz]
          linarith
      -- integrate the pointwise estimate
      have hI1 : Integrable (fun z => ψ (deltaMap f (c n) n z)) (ν n) :=
        Integrable.mono' (integrable_const (‖ψ 0‖ + C))
          (hψcont.measurable.comp (measurable_deltaMap hfmeas _ n)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => hψbdd _)
      have hI2 : Integrable (fun z => ψD z) (ν n) := BoundedContinuousFunction.integrable _ ψD
      have hI3 : Integrable (fun z => C * tailCutoff M z) (ν n) :=
        (BoundedContinuousFunction.integrable _ (tailCutoff M)).const_mul C
      have hbound : ‖∫ y, ψ y ∂((ν n).map (deltaMap f (c n) n)) - ∫ z, ψD z ∂(ν n)‖
          ≤ (L : ℝ) * η * M + C * ∫ z, tailCutoff M z ∂(ν n) := by
        have hcm : ∫ z, (C * tailCutoff M z) ∂(ν n) = C * ∫ z, tailCutoff M z ∂(ν n) :=
          integral_const_mul C _
        have heq : ∫ z, ((L : ℝ) * η * M + C * tailCutoff M z) ∂(ν n)
            = (L : ℝ) * η * M + C * ∫ z, tailCutoff M z ∂(ν n) := by
          rw [integral_add (integrable_const _) hI3, hcm, integral_const]
          simp
        rw [hlhs n, ← integral_sub hI1 hI2]
        refine (norm_integral_le_integral_norm _).trans ?_
        calc ∫ z, ‖ψ (deltaMap f (c n) n z) - ψD z‖ ∂(ν n)
            ≤ ∫ z, ((L : ℝ) * η * M + C * tailCutoff M z) ∂(ν n) :=
              integral_mono ((hI1.sub hI2).norm) ((integrable_const _).add hI3) hpt
          _ = (L : ℝ) * η * M + C * ∫ z, tailCutoff M z ∂(ν n) := heq
      have hnn : (0 : ℝ) ≤ ∫ z, tailCutoff M z ∂(ν n) :=
        integral_nonneg fun z => tailCutoff_nonneg M z
      have hCle : C * ∫ z, tailCutoff M z ∂(ν n) ≤ (C + 1) * ∫ z, tailCutoff M z ∂(ν n) := by
        nlinarith
      calc ‖∫ y, ψ y ∂((ν n).map (deltaMap f (c n) n)) - ∫ z, ψD z ∂(ν n)‖
          ≤ (L : ℝ) * η * M + C * ∫ z, tailCutoff M z ∂(ν n) := hbound
        _ < ε := by linarith
    simpa using! hA.add hB
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hweak φ

/-- **The smooth-function root along a sequence of source laws.**

If the images of the source laws `E n` under the vector of coordinate functions form a sequence of
the mean-vector class with limit `H`, and the corresponding mean vectors `c n` converge to a point
`θ` at which `f` is continuously differentiable, then the root `√n (f(θ̂ₙ) − f(c n))` converges
weakly to the image of the Gaussian limit under the differential.

Both halves of the bootstrap delta method are instances: the sampling-law half at the constant
sequence `E n = P`, and the resampled half at the empirical measures of the observed sample. -/
private lemma tendsto_smooth_root_of_class {θ : EuclideanSpace ℝ (Fin p)}
    {H : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure H]
    (hH2 : MemLp (fun y : EuclideanSpace ℝ (Fin p) => y) 2 H)
    (hhmeas : ∀ j, Measurable (h j)) (hfmeas : Measurable f) (hf : HasFDerivAt f Df θ)
    (hf_nhds : ∀ᶠ y in 𝓝 θ, DifferentiableAt ℝ f y)
    (hf_cont : ContinuousAt (fderiv ℝ f) θ)
    {E : ℕ → Measure 𝓢} (hEprob : ∀ n : ℕ, 0 < n → IsProbabilityMeasure (E n))
    (hE2 : ∀ (n : ℕ) (j : Fin p), MemLp (h j) 2 (E n))
    (hEclass : (fun n => (E n).map (hVec h)) ∈ meanVecSeqClass H)
    {c : ℕ → EuclideanSpace ℝ (Fin p)}
    (hcE : ∀ n : ℕ, 0 < n → c n = WithLp.toLp 2 fun j => ∫ s, h j s ∂(E n))
    (hc : Tendsto c atTop (𝓝 θ))
    (φ : EuclideanSpace ℝ (Fin q) →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ z, φ z ∂((Measure.pi fun _ : Fin n => E n).map
        fun w => Real.sqrt n • (f (meanStatistic h w) - f (c n)))) atTop
      (𝓝 (∫ y, φ y ∂((multivariateGaussian 0 (covMatrix H)).map Df))) := by
  classical
  have hνprob : ∀ n : ℕ, IsProbabilityMeasure (meanVecRootLaw ((E n).map (hVec h)) n) := by
    intro n
    haveI hpi : IsProbabilityMeasure (Measure.pi fun _ : Fin n => (E n).map (hVec h)) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; rw [Measure.pi_of_empty]; infer_instance
      · haveI := hEclass.1 n hn
        haveI : ∀ _ : Fin n, IsProbabilityMeasure ((E n).map (hVec h)) := fun _ => ‹_›
        infer_instance
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hν : ∀ ψ : EuclideanSpace ℝ (Fin p) →ᵇ ℝ,
      Tendsto (fun n => ∫ z, ψ z ∂(meanVecRootLaw ((E n).map (hVec h)) n)) atTop
        (𝓝 (∫ z, ψ z ∂(multivariateGaussian 0 (covMatrix H)))) :=
    fun ψ => meanVec_root_tendsto hH2 hEclass ψ
  have hmain := tendsto_integral_map_deltaMap (f := f) (Df := Df) (θ := θ)
    (ν := fun n => meanVecRootLaw ((E n).map (hVec h)) n)
    (Gp := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (covMatrix H)) (c := c)
    hfmeas hf hf_nhds hf_cont hνprob inferInstance hν hc φ
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  haveI := hEprob n hn
  have hsq : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hn)
  have hmroot : Measurable fun w : Fin n → 𝓢 => Real.sqrt n • (meanStatistic h w - c n) := by
    have hms : Measurable (meanStatistic h (n := n)) := measurable_meanStatistic hhmeas
    fun_prop
  have hid : (Measure.pi fun _ : Fin n => E n).map
      (fun w => Real.sqrt n • (meanStatistic h w - c n))
      = meanVecRootLaw ((E n).map (hVec h)) n := by
    rw [hcE n hn]
    exact map_meanStatistic_eq_meanVecRootLaw hhmeas (fun j => hE2 n j) n
  congr 1
  rw [← hid, Measure.map_map (measurable_deltaMap hfmeas (c n) n) hmroot]
  congr 1
  funext w
  have hcancel : c n + (Real.sqrt n)⁻¹ • (Real.sqrt n • (meanStatistic h w - c n))
      = meanStatistic h w := by
    rw [smul_smul, inv_mul_cancel₀ hsq, one_smul]
    abel
  simp only [Function.comp_apply, deltaMap, hcancel]

/-- **Delta-method limit for a smooth function of means.**

Let each coordinate of the parameter be an expectation `∫ h j dP` estimated by the corresponding
sample mean, and let `f` be differentiable at the parameter with a nonzero differential that is
continuous there. Then the centred and scaled image `n^{1/2}(f(θ̂ₙ) − f(θ))` converges weakly to
the centred multivariate normal law with covariance `D Σ Dᵀ`, where `Σ` is the covariance matrix
of the vector of coordinate functions and `D` is the matrix of the differential. -/
theorem smooth_function_of_means_tendsto [IsProbabilityMeasure P]
    -- USER-INPUT: the coordinate functions are measurable and square-integrable
    (hhmeas : ∀ j, Measurable (h j)) (hh2 : ∀ j, MemLp (h j) 2 P)
    -- LEAN-ONLY (signature amendment, FORCED): the smooth function is measurable. The conclusion
    -- is about `Measure.map (fun w => √n • (f (meanStatistic h w) − f θ))`, and in Mathlib
    -- `Measure.map` returns the junk value `0` when its argument is not `AEMeasurable`. The
    -- remaining hypotheses constrain `f` only near `θ` (`hf`, `hf_nhds`, `hf_cont`), so without
    -- this clause `f` may be non-measurable away from `θ`, where the law of `θ̂ₙ` still puts mass:
    -- take `p = q = 1`, `f y = y` for `y < 1/2` and `f y = 1_V(y)` for `y ≥ 1/2` with
    -- `V ⊆ [1/2, ∞)` non-Lebesgue-measurable. Then every other hypothesis holds, the left-hand
    -- side is `∫ φ d0 = 0`, and the right-hand side is nonzero for suitable `φ`.
    (hfmeas : Measurable f)
    -- USER-INPUT: `f` is differentiable at the parameter with differential `Df`
    (hf : HasFDerivAt f Df (WithLp.toLp 2 fun j => ∫ s, h j s ∂P))
    -- USER-INPUT: the differential does not vanish
    (hDf_ne : Df ≠ 0)
    -- USER-INPUT: `f` is differentiable near the parameter; half of the reference's
    -- "nonzero continuous differential" condition
    (hf_nhds : ∀ᶠ y in 𝓝 (WithLp.toLp (2 : ℝ≥0∞) fun j => ∫ s, h j s ∂P),
      DifferentiableAt ℝ f y)
    -- USER-INPUT: the differential is continuous at the parameter; the other half
    (hf_cont : ContinuousAt (fderiv ℝ f) (WithLp.toLp 2 fun j => ∫ s, h j s ∂P))
    -- USER-INPUT: `D` is the matrix of the differential
    (hD : ∀ v, Df v = WithLp.toLp 2 (D.mulVec (WithLp.ofLp v)))
    -- USER-INPUT: `covH` is the covariance matrix of the vector of coordinate functions
    (hcovH : ∀ i j, covH i j = cov[h i, h j; P])
    -- LEAN-ONLY: argument quantified by the conclusion, not a hypothesis
    (φ : EuclideanSpace ℝ (Fin q) →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ z, φ z ∂((Measure.pi fun _ : Fin n => P).map
        fun w => Real.sqrt n • (f (meanStatistic h w) -
          f (WithLp.toLp 2 fun j => ∫ s, h j s ∂P)))) atTop
      (𝓝 (∫ z, φ z ∂(multivariateGaussian 0 (D * covH * D.transpose)))) := by
  classical
  -- (1) transport the problem to the mean-vector theory of this file
  set θ : EuclideanSpace ℝ (Fin p) := WithLp.toLp 2 fun j => ∫ s, h j s ∂P with hθdef
  haveI hHprob : IsProbabilityMeasure (P.map (hVec h)) := isProbabilityMeasure_hVec hhmeas
  have hH2 : MemLp (fun y : EuclideanSpace ℝ (Fin p) => y) 2 (P.map (hVec h)) :=
    memLp_id_map_hVec hhmeas hh2
  have hcovEq : covMatrix (P.map (hVec h)) = covH := by
    ext i j
    rw [covMatrix_map_hVec hhmeas i j, hcovH i j]
  have hpsd : covH.PosSemidef := hcovEq ▸ posSemidef_covMatrix hH2
  have hclass : (fun _ : ℕ => P.map (hVec h)) ∈ meanVecSeqClass (P.map (hVec h)) :=
    ⟨fun _ _ => inferInstance, fun _ => hH2, fun _ => tendsto_const_nhds,
      fun _ => tendsto_const_nhds, fun _ _ => tendsto_const_nhds⟩
  have hνprob : ∀ n : ℕ, IsProbabilityMeasure (meanVecRootLaw (P.map (hVec h)) n) := by
    intro n
    haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin n => P.map (hVec h)) := inferInstance
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hν : ∀ ψ : EuclideanSpace ℝ (Fin p) →ᵇ ℝ,
      Tendsto (fun n => ∫ z, ψ z ∂(meanVecRootLaw (P.map (hVec h)) n)) atTop
        (𝓝 (∫ z, ψ z ∂(multivariateGaussian 0 covH))) := by
    intro ψ
    have hres := meanVec_root_tendsto hH2 hclass ψ
    rwa [hcovEq] at hres
  -- (4) the Gaussian limit transforms by the differential
  have hGq : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) covH).map Df
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) (D * covH * D.transpose) :=
    map_multivariateGaussian_deriv hpsd hD
  -- (2)-(3) the delta-method engine at the constant centre `θ`
  have hmain := tendsto_integral_map_deltaMap (f := f) (Df := Df) (θ := θ)
    (ν := fun n => meanVecRootLaw (P.map (hVec h)) n)
    (Gp := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) covH) (c := fun _ : ℕ => θ)
    hfmeas hf hf_nhds hf_cont hνprob inferInstance hν tendsto_const_nhds φ
  rw [hGq] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hsq : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hn)
  have hmroot : Measurable fun w : Fin n → 𝓢 => Real.sqrt n • (meanStatistic h w - θ) := by
    have hms : Measurable (meanStatistic h (n := n)) := measurable_meanStatistic hhmeas
    fun_prop
  congr 1
  rw [← map_meanStatistic_eq_meanVecRootLaw hhmeas hh2 n,
    Measure.map_map (measurable_deltaMap hfmeas θ n) hmroot]
  congr 1
  funext w
  have hcancel : θ + (Real.sqrt n)⁻¹ • (Real.sqrt n • (meanStatistic h w - θ))
      = meanStatistic h w := by
    rw [smul_smul, inv_mul_cancel₀ hsq, one_smul]
    abel
  simp only [Function.comp_apply, deltaMap, hcancel]


/-- **Bootstrap consistency for a smooth function of means, resampled-law form.**

Almost surely, the law of the resampled and recentred image is asymptotically indistinguishable
from the sampling law of the centred and scaled image, tested against bounded continuous
functions. -/
theorem bootstrap_smooth_function_law_consistent [IsProbabilityMeasure P] [IsProbabilityMeasure Pr]
    -- LEAN-ONLY: the observations are measurable
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent identically distributed observations with law `P`
    (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) P Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: the coordinate functions are measurable and square-integrable
    (hhmeas : ∀ j, Measurable (h j)) (hh2 : ∀ j, MemLp (h j) 2 P)
    -- LEAN-ONLY (signature amendment, FORCED): the smooth function is measurable; the two
    -- `Measure.map`s of the conclusion return the junk value `0` otherwise. See the same clause
    -- on `smooth_function_of_means_tendsto` for the counterexample.
    (hfmeas : Measurable f)
    -- USER-INPUT: `f` is differentiable at the parameter with nonzero continuous differential
    (hf : HasFDerivAt f Df (WithLp.toLp 2 fun j => ∫ s, h j s ∂P)) (hDf_ne : Df ≠ 0)
    -- USER-INPUT (signature amendment): `f` is differentiable *near* the parameter. This is the
    -- other half of the reference's "nonzero continuous differential" hypothesis, and it is
    -- already carried by the sibling `smooth_function_of_means_tendsto`; the frozen signature of
    -- this theorem kept only `hf_cont`, which alone carries no information, because Mathlib's
    -- `fderiv ℝ f y` is the junk value `0` at every `y` where `f` is not differentiable (so
    -- `fderiv ℝ f` can be continuous at `θ` while `f` is differentiable at `θ` only). The clause
    -- is genuinely needed here and not in the sampling-law half: the resampled root is expanded
    -- at the RANDOM centre `θ̂ₙ`, and differentiability at `θ` alone bounds the Taylor remainder
    -- only by `η (2√n‖θ̂ₙ − θ‖ + ‖z‖)`, which is useless because `√n‖θ̂ₙ − θ‖` is almost surely
    -- unbounded by the law of the iterated logarithm.
    (hf_nhds : ∀ᶠ y in 𝓝 (WithLp.toLp (2 : ℝ≥0∞) fun j => ∫ s, h j s ∂P),
      DifferentiableAt ℝ f y)
    -- USER-INPUT: the differential is continuous at the parameter
    (hf_cont : ContinuousAt (fderiv ℝ f) (WithLp.toLp 2 fun j => ∫ s, h j s ∂P))
    -- LEAN-ONLY: argument quantified by the conclusion, not a hypothesis
    (φ : EuclideanSpace ℝ (Fin q) →ᵇ ℝ) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n : ℕ =>
        ∫ z, φ z ∂((Measure.pi fun _ : Fin n => P).map
          fun w => Real.sqrt n • (f (meanStatistic h w) -
            f (WithLp.toLp 2 fun j => ∫ s, h j s ∂P))) -
        ∫ z, φ z ∂((bootstrapLaw fun i : Fin n => X i ω).map
          fun w => Real.sqrt n • (f (meanStatistic h w) -
            f (meanStatistic h fun i : Fin n => X i ω)))) atTop (𝓝 0) := by
  classical
  set θ : EuclideanSpace ℝ (Fin p) := WithLp.toLp 2 fun j => ∫ s, h j s ∂P with hθdef
  haveI hHprob : IsProbabilityMeasure (P.map (hVec h)) := isProbabilityMeasure_hVec hhmeas
  have hH2 : MemLp (fun y : EuclideanSpace ℝ (Fin p) => y) 2 (P.map (hVec h)) :=
    memLp_id_map_hVec hhmeas hh2
  have hhVmeas : Measurable (hVec h) := measurable_hVec hhmeas
  have hθint : ∫ z, z ∂(P.map (hVec h)) = θ := integral_map_hVec hhmeas hh2
  -- the transformed observations are i.i.d. with law `P.map (hVec h)`
  have hYmeas : ∀ i, Measurable fun ω => hVec h (X i ω) := fun i => hhVmeas.comp (hXmeas i)
  have hYindep : iIndepFun (fun i ω => hVec h (X i ω)) Pr := by
    simpa [Function.comp_def] using hindep.comp (fun _ => hVec h) (fun _ => hhVmeas)
  have hVecLaw : HasLaw (hVec h) (P.map (hVec h)) P :=
    { aemeasurable := hhVmeas.aemeasurable, map_eq := rfl }
  have hYlaw : HasLaw (fun ω => hVec h (X 0 ω)) (P.map (hVec h)) Pr := hVecLaw.fun_comp hlaw
  have hYident : ∀ i, IdentDistrib (fun ω => hVec h (X i ω)) (fun ω => hVec h (X 0 ω)) Pr Pr :=
    fun i => (hident i).comp hhVmeas
  -- the sampling-law half
  have hA : Tendsto (fun n : ℕ => ∫ z, φ z ∂((Measure.pi fun _ : Fin n => P).map
      fun w => Real.sqrt n • (f (meanStatistic h w) - f θ))) atTop
      (𝓝 (∫ y, φ y ∂((multivariateGaussian 0 (covMatrix (P.map (hVec h)))).map Df))) :=
    tendsto_smooth_root_of_class hH2 hhmeas hfmeas hf hf_nhds hf_cont
      (E := fun _ => P) (fun _ _ => inferInstance) (fun _ j => hh2 j)
      ⟨fun _ _ => inferInstance, fun _ => hH2, fun _ => tendsto_const_nhds,
        fun _ => tendsto_const_nhds, fun _ _ => tendsto_const_nhds⟩
      (c := fun _ => θ) (fun _ _ => rfl) tendsto_const_nhds φ
  filter_upwards [empirical_mem_meanVecSeqClass hYmeas hYindep hYlaw hYident hH2,
    tendsto_sample_average hYmeas hYindep hYlaw hYident (fun y => y) measurable_id
      (hH2.integrable one_le_two)] with ω hω hsl
  -- the resampled half, at the empirical measures of the observed sample
  have hEclass : (fun n => (empiricalMeasure fun i : Fin n => X i ω).map (hVec h))
      ∈ meanVecSeqClass (P.map (hVec h)) := by
    have hmapeq : ∀ n : ℕ, (empiricalMeasure fun i : Fin n => X i ω).map (hVec h)
        = empiricalMeasure fun i : Fin n => hVec h (X i ω) :=
      fun n => map_empiricalMeasure hhVmeas _
    simpa only [hmapeq] using hω
  have hcω : Tendsto (fun n : ℕ => meanStatistic h fun i : Fin n => X i ω) atTop (𝓝 θ) := by
    rw [hθint] at hsl
    refine hsl.congr fun n => ?_
    rw [meanStatistic_eq_smul_sum, Fin.sum_univ_eq_sum_range (fun i => hVec h (X i ω)) n]
  have hB : Tendsto (fun n : ℕ =>
      ∫ z, φ z ∂((Measure.pi fun _ : Fin n => empiricalMeasure fun i : Fin n => X i ω).map
        fun w => Real.sqrt n • (f (meanStatistic h w) -
          f (meanStatistic h fun i : Fin n => X i ω)))) atTop
      (𝓝 (∫ y, φ y ∂((multivariateGaussian 0 (covMatrix (P.map (hVec h)))).map Df))) :=
    tendsto_smooth_root_of_class hH2 hhmeas hfmeas hf hf_nhds hf_cont
      (E := fun n => empiricalMeasure fun i : Fin n => X i ω)
      (fun n hn => isProbabilityMeasure_empiricalMeasure' hn _)
      (fun n j => memLp_empiricalMeasure' _ (hhmeas j)) hEclass
      (c := fun n => meanStatistic h fun i : Fin n => X i ω)
      (fun n _ => (toLp_integral_empiricalMeasure hhmeas _).symm) hcω φ
  have hgoal := hA.sub hB
  rw [sub_self] at hgoal
  exact hgoal

/-- **Portmanteau at the sublevel sets of a norm.**

If probability measures converge weakly to a nondegenerate centred Gaussian, the measures of the
sublevel sets of a norm converge, because the spheres of the norm are null for the limit. This is
the second half of `norm_root_cdf_tendsto`, isolated so that it applies to the image laws of the
smooth-function root as well as to the mean-vector root. -/
private lemma tendsto_measure_norm_le_of_weak {S : Matrix (Fin q) (Fin q) ℝ}
    (hpsdS : S.PosSemidef) (hSne : S ≠ 0)
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    (hnrm_def : ∀ y, nrm y = 0 → y = 0)
    {μ : ℕ → Measure (EuclideanSpace ℝ (Fin q))} (hμprob : ∀ n, IsProbabilityMeasure (μ n))
    (hweak : ∀ ψ : EuclideanSpace ℝ (Fin q) →ᵇ ℝ,
      Tendsto (fun n => ∫ z, ψ z ∂(μ n)) atTop (𝓝 (∫ z, ψ z ∂(multivariateGaussian 0 S))))
    (x : ℝ) :
    Tendsto (fun n => ((μ n) {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ x}).toReal) atTop
      (𝓝 (normLimitCDF S nrm x)) := by
  classical
  have hnrm_cont : Continuous nrm := continuous_of_seminorm hnrm_add hnrm_smul
  set ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin q)) :=
    ⟨multivariateGaussian 0 S, inferInstance⟩ with hνdef
  set μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin q)) :=
    fun n => ⟨μ n, hμprob n⟩ with hμsdef
  have hconv : Tendsto μs atTop (𝓝 ν) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 hweak
  have hfrontier : (ν : Measure (EuclideanSpace ℝ (Fin q)))
      (frontier {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ x}) = 0 := by
    refine measure_mono_null ?_
      (measure_multivariateGaussian_norm_level hpsdS hSne hnrm_add hnrm_smul hnrm_def x)
    intro z hz
    have hclosed : IsClosed {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ x} :=
      isClosed_le hnrm_cont continuous_const
    have hz1 : nrm z ≤ x := by
      have hh := hz.1
      rwa [hclosed.closure_eq] at hh
    exact le_antisymm hz1 (not_lt.1 fun hlt => hz.2
      (mem_interior_iff_mem_nhds.2
        (Filter.mem_of_superset ((isOpen_lt hnrm_cont continuous_const).mem_nhds hlt)
          (fun w hw => (le_of_lt hw : nrm w ≤ x)))))
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv hfrontier
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport

/-- The distribution function of a norm under a probability law is a distribution function. -/
private lemma isCDF_measure_norm_le {μ : Measure (EuclideanSpace ℝ (Fin q))}
    (hμ : IsProbabilityMeasure μ) (hnrm_cont : Continuous nrm) :
    IsCDF fun t => (μ {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ t}).toReal := by
  haveI := hμ
  haveI : IsProbabilityMeasure (μ.map nrm) :=
    Measure.isProbabilityMeasure_map hnrm_cont.measurable.aemeasurable
  have heq : (fun t => (μ {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ t}).toReal)
      = fun t => ((μ.map nrm) (Set.Iic t)).toReal := by
    funext t
    rw [Measure.map_apply hnrm_cont.measurable measurableSet_Iic]
    rfl
  rw [heq]
  exact isCDF_toReal_measure_Iic _

/-- Rescaling the argument by a nonzero factor does not change the Kolmogorov distance. -/
private lemma supCDFDist_comp_mul_left {a : ℝ} (ha : a ≠ 0) (F G : ℝ → ℝ) :
    supCDFDist (fun s => F (a * s)) (fun s => G (a * s)) = supCDFDist F G := by
  unfold supCDFDist
  exact Equiv.iSup_comp (g := fun t : ℝ => |F t - G t|) (Equiv.mulLeft₀ a ha)

/-- **Bootstrap consistency for a smooth function of means, uniform distribution-function form.**

Almost surely, the sampling distribution function of the norm of the estimation error is
uniformly approximated by its resampled counterpart. Taking the maximum norm on the image space,
this is the statement behind simultaneous confidence rectangles for the coordinates of
`f(θ)`; the reference develops that construction as an illustration rather than as part of the
result, so it is not stated separately here. -/
theorem bootstrap_smooth_function_consistent [IsProbabilityMeasure P] [IsProbabilityMeasure Pr]
    -- LEAN-ONLY: the observations are measurable
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent identically distributed observations with law `P`
    (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) P Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: the coordinate functions are measurable and square-integrable
    (hhmeas : ∀ j, Measurable (h j)) (hh2 : ∀ j, MemLp (h j) 2 P)
    -- LEAN-ONLY (signature amendment, FORCED): the smooth function is measurable; the statement
    -- measures the sets `{ω' | nrm (f (meanStatistic h …) − f θ) ≤ s}`. See the same clause on
    -- `smooth_function_of_means_tendsto`.
    (hfmeas : Measurable f)
    -- USER-INPUT: `f` is differentiable at the parameter with nonzero continuous differential
    (hf : HasFDerivAt f Df (WithLp.toLp 2 fun j => ∫ s, h j s ∂P)) (hDf_ne : Df ≠ 0)
    -- USER-INPUT (signature amendment): `f` is differentiable *near* the parameter — the other
    -- half of the reference's "continuous differential" hypothesis, needed for the Taylor step at
    -- the random centre. See the same clause on `bootstrap_smooth_function_law_consistent`.
    (hf_nhds : ∀ᶠ y in 𝓝 (WithLp.toLp (2 : ℝ≥0∞) fun j => ∫ s, h j s ∂P),
      DifferentiableAt ℝ f y)
    -- USER-INPUT: the differential is continuous at the parameter
    (hf_cont : ContinuousAt (fderiv ℝ f) (WithLp.toLp 2 fun j => ∫ s, h j s ∂P))
    -- USER-INPUT (signature amendment): `D` is the matrix of the differential and `covH` the
    -- covariance matrix of the vector of coordinate functions, exactly as in the sibling
    -- `smooth_function_of_means_tendsto`; they are needed only to name the limiting covariance
    -- `D covH Dᵀ` in the nondegeneracy clause `hS` below.
    (hD : ∀ v, Df v = WithLp.toLp 2 (D.mulVec (WithLp.ofLp v)))
    (hcovH : ∀ i j, covH i j = cov[h i, h j; P])
    -- USER-INPUT (signature amendment, REQUIRED — the statement is FALSE without it): the
    -- limiting covariance `D covH Dᵀ` of the smooth-function root is not identically zero. This
    -- is the exact analogue of the clause `hS` already carried by the mean-vector sibling
    -- `bootstrap_meanVec_consistent`, and `Df ≠ 0` does **not** imply it, because the differential
    -- may annihilate the range of `covH`.
    --
    -- COUNTEREXAMPLE to the frozen statement (no `hS`). Take `𝓢 = ℝ`, `P = ` standard normal,
    -- `p = 2`, `h 0 = id`, `h 1 = 0`, `q = 1`, `nrm = |·|`, and `f (u, v) = v + u²`. Then
    -- `θ = (0,0)`, `f` is smooth, `Df = (0,1) ≠ 0`, `covH = diag(1,0)`, and `D covH Dᵀ = 0`. The
    -- sample mean vector is `(ūₙ, 0)`, so the sampling distribution function of the error is
    -- `s ↦ P(ūₙ² ≤ s)`, which at `s = c/n` equals `P(χ²₁ ≤ c)` for every `n`. The resampled error
    -- is `(w̄)² − (ūₙ)² = (w̄ − ūₙ)(w̄ + ūₙ)`, of order `n^{-1}` with a *different* shape: at
    -- `s = c/n` its distribution function converges to `P(|W(2Zₙ + W)| ≤ c)` with `Zₙ = √n ūₙ`,
    -- and the law of the iterated logarithm makes `|Zₙ(ω)| ≥ 1` infinitely often for almost every
    -- `ω`. For small `c` the two values are `≈ √(2c/π)` and `≈ c√(2/π)/|Zₙ|`, whose difference is
    -- bounded away from `0` along that subsequence, so the Kolmogorov distance does not tend
    -- to `0`. (The degenerate case is genuinely excluded rather than repaired: with a degenerate
    -- limit the sublevel sets of the norm have a non-null frontier and Pólya's argument — which
    -- is the content of the theorem — does not apply.)
    (hS : ∃ i j : Fin q, (D * covH * D.transpose) i j ≠ 0)
    -- USER-INPUT: the norm is subadditive
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    -- USER-INPUT: the norm is absolutely homogeneous
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    -- USER-INPUT: the norm is positive definite
    (hnrm_def : ∀ y, nrm y = 0 → y = 0) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n : ℕ => supCDFDist
        (fun s => (Pr {ω' | nrm (f (meanStatistic h fun i : Fin n => X i ω') -
          f (WithLp.toLp 2 fun j => ∫ t, h j t ∂P)) ≤ s}).toReal)
        (fun s => ((bootstrapLaw fun i : Fin n => X i ω)
          {w | nrm (f (meanStatistic h w) -
            f (meanStatistic h fun i : Fin n => X i ω)) ≤ s}).toReal))
      atTop (𝓝 0) := by
  classical
  set θ : EuclideanSpace ℝ (Fin p) := WithLp.toLp 2 fun j => ∫ s, h j s ∂P with hθdef
  haveI hHprob : IsProbabilityMeasure (P.map (hVec h)) := isProbabilityMeasure_hVec hhmeas
  have hH2 : MemLp (fun y : EuclideanSpace ℝ (Fin p) => y) 2 (P.map (hVec h)) :=
    memLp_id_map_hVec hhmeas hh2
  have hhVmeas : Measurable (hVec h) := measurable_hVec hhmeas
  have hθint : ∫ z, z ∂(P.map (hVec h)) = θ := integral_map_hVec hhmeas hh2
  have hcovEq : covMatrix (P.map (hVec h)) = covH := by
    ext i j
    rw [covMatrix_map_hVec hhmeas i j, hcovH i j]
  have hpsd : covH.PosSemidef := hcovEq ▸ posSemidef_covMatrix hH2
  have hpsdS : (D * covH * D.transpose).PosSemidef := by
    have hc := hpsd.conjTranspose_mul_mul_same (B := D.transpose)
    simpa [Matrix.conjTranspose_transpose] using hc
  obtain ⟨i₀, j₀, hij⟩ := hS
  have hSne : D * covH * D.transpose ≠ 0 := fun hz => hij (by rw [hz]; simp)
  have hnrm_cont : Continuous nrm := continuous_of_seminorm hnrm_add hnrm_smul
  have hGq : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) covH).map Df
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) (D * covH * D.transpose) :=
    map_multivariateGaussian_deriv hpsd hD
  -- the limiting distribution function of the norm is a continuous distribution function
  have hcontJ : Continuous (normLimitCDF (D * covH * D.transpose) nrm) :=
    continuous_normLimitCDF_of_posSemidef hpsdS hSne hnrm_add hnrm_smul hnrm_def
  have hJcdf : IsCDF (normLimitCDF (D * covH * D.transpose) nrm) := by
    haveI : IsProbabilityMeasure ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin q))
        (D * covH * D.transpose)).map nrm) :=
      Measure.isProbabilityMeasure_map hnrm_cont.measurable.aemeasurable
    have heq : normLimitCDF (D * covH * D.transpose) nrm = fun x =>
        (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin q))
          (D * covH * D.transpose)).map nrm) (Set.Iic x)).toReal := by
      funext x
      rw [normLimitCDF, Measure.map_apply hnrm_cont.measurable measurableSet_Iic]
      rfl
    rw [heq]
    exact isCDF_toReal_measure_Iic _
  -- the transformed observations are i.i.d. with law `P.map (hVec h)`
  have hYmeas : ∀ i, Measurable fun ω => hVec h (X i ω) := fun i => hhVmeas.comp (hXmeas i)
  have hYindep : iIndepFun (fun i ω => hVec h (X i ω)) Pr := by
    simpa [Function.comp_def] using hindep.comp (fun _ => hVec h) (fun _ => hhVmeas)
  have hVecLaw : HasLaw (hVec h) (P.map (hVec h)) P :=
    { aemeasurable := hhVmeas.aemeasurable, map_eq := rfl }
  have hYlaw : HasLaw (fun ω => hVec h (X 0 ω)) (P.map (hVec h)) Pr := hVecLaw.fun_comp hlaw
  have hYident : ∀ i, IdentDistrib (fun ω => hVec h (X i ω)) (fun ω => hVec h (X 0 ω)) Pr Pr :=
    fun i => (hident i).comp hhVmeas
  -- the i.i.d. representation of the sampling law
  have hφmeas : ∀ n : ℕ, Measurable fun ω (i : Fin n) => X i ω :=
    fun n => measurable_pi_lambda _ fun i => hXmeas i
  have hmap : ∀ n : ℕ, Pr.map (fun ω (i : Fin n) => X i ω) = Measure.pi fun _ : Fin n => P := by
    intro n
    have hh := (iIndepFun_iff_map_fun_eq_pi_map (μ := Pr) (f := fun i : Fin n => X (i : ℕ))
      (fun i => (hXmeas (i : ℕ)).aemeasurable)).1 (hindep.precomp Fin.val_injective)
    rw [hh]
    congr 1
    funext i
    exact ((hident (i : ℕ)).map_eq).trans hlaw.map_eq
  -- the sampling-law half of the weak convergence
  have hAweak : ∀ ψ : EuclideanSpace ℝ (Fin q) →ᵇ ℝ,
      Tendsto (fun n : ℕ => ∫ z, ψ z ∂((Measure.pi fun _ : Fin n => P).map
        fun w => Real.sqrt n • (f (meanStatistic h w) - f θ))) atTop
        (𝓝 (∫ z, ψ z ∂(multivariateGaussian 0 (D * covH * D.transpose)))) := by
    intro ψ
    have hres := tendsto_smooth_root_of_class hH2 hhmeas hfmeas hf hf_nhds hf_cont
      (E := fun _ => P) (fun _ _ => inferInstance) (fun _ j => hh2 j)
      ⟨fun _ _ => inferInstance, fun _ => hH2, fun _ => tendsto_const_nhds,
        fun _ => tendsto_const_nhds, fun _ _ => tendsto_const_nhds⟩
      (c := fun _ => θ) (fun _ _ => rfl) tendsto_const_nhds ψ
    rwa [hcovEq, hGq] at hres
  have hmeasRootP : ∀ n : ℕ, Measurable fun w : Fin n → 𝓢 =>
      Real.sqrt n • (f (meanStatistic h w) - f θ) := by
    intro n
    have hms : Measurable (meanStatistic h (n := n)) := measurable_meanStatistic hhmeas
    fun_prop
  have hκprob : ∀ n : ℕ, IsProbabilityMeasure ((Measure.pi fun _ : Fin n => P).map
      fun w => Real.sqrt n • (f (meanStatistic h w) - f θ)) := fun n =>
    Measure.isProbabilityMeasure_map (hmeasRootP n).aemeasurable
  have hFconv : ∀ t : ℝ, Tendsto (fun n : ℕ =>
      (((Measure.pi fun _ : Fin n => P).map
        fun w => Real.sqrt n • (f (meanStatistic h w) - f θ))
          {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ t}).toReal) atTop
      (𝓝 (normLimitCDF (D * covH * D.transpose) nrm t)) := fun t =>
    tendsto_measure_norm_le_of_weak hpsdS hSne hnrm_add hnrm_smul hnrm_def hκprob hAweak t
  have hA : Tendsto (fun n : ℕ => supCDFDist
      (fun t => (((Measure.pi fun _ : Fin n => P).map
        fun w => Real.sqrt n • (f (meanStatistic h w) - f θ))
          {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ t}).toReal)
      (normLimitCDF (D * covH * D.transpose) nrm)) atTop (𝓝 0) :=
    tendsto_supCDFDist_zero (fun n => isCDF_measure_norm_le (hκprob n) hnrm_cont) hcontJ hJcdf
      hFconv
  filter_upwards [empirical_mem_meanVecSeqClass hYmeas hYindep hYlaw hYident hH2,
    tendsto_sample_average hYmeas hYindep hYlaw hYident (fun y => y) measurable_id
      (hH2.integrable one_le_two)] with ω hω hsl
  -- the resampled half
  have hEclass : (fun n => (empiricalMeasure fun i : Fin n => X i ω).map (hVec h))
      ∈ meanVecSeqClass (P.map (hVec h)) := by
    have hmapeq : ∀ n : ℕ, (empiricalMeasure fun i : Fin n => X i ω).map (hVec h)
        = empiricalMeasure fun i : Fin n => hVec h (X i ω) :=
      fun n => map_empiricalMeasure hhVmeas _
    simpa only [hmapeq] using hω
  have hcω : Tendsto (fun n : ℕ => meanStatistic h fun i : Fin n => X i ω) atTop (𝓝 θ) := by
    rw [hθint] at hsl
    refine hsl.congr fun n => ?_
    rw [meanStatistic_eq_smul_sum, Fin.sum_univ_eq_sum_range (fun i => hVec h (X i ω)) n]
  have hBweak : ∀ ψ : EuclideanSpace ℝ (Fin q) →ᵇ ℝ,
      Tendsto (fun n : ℕ => ∫ z, ψ z ∂((Measure.pi fun _ : Fin n =>
          empiricalMeasure fun i : Fin n => X i ω).map
        fun w => Real.sqrt n • (f (meanStatistic h w) -
          f (meanStatistic h fun i : Fin n => X i ω)))) atTop
        (𝓝 (∫ z, ψ z ∂(multivariateGaussian 0 (D * covH * D.transpose)))) := by
    intro ψ
    have hres := tendsto_smooth_root_of_class hH2 hhmeas hfmeas hf hf_nhds hf_cont
      (E := fun n => empiricalMeasure fun i : Fin n => X i ω)
      (fun n hn => isProbabilityMeasure_empiricalMeasure' hn _)
      (fun n j => memLp_empiricalMeasure' _ (hhmeas j)) hEclass
      (c := fun n => meanStatistic h fun i : Fin n => X i ω)
      (fun n _ => (toLp_integral_empiricalMeasure hhmeas _).symm) hcω ψ
    rwa [hcovEq, hGq] at hres
  have hmeasRootE : ∀ n : ℕ, Measurable fun w : Fin n → 𝓢 =>
      Real.sqrt n • (f (meanStatistic h w) - f (meanStatistic h fun i : Fin n => X i ω)) := by
    intro n
    have hms : Measurable (meanStatistic h (n := n)) := measurable_meanStatistic hhmeas
    fun_prop
  have hpiE : ∀ n : ℕ, IsProbabilityMeasure
      (Measure.pi fun _ : Fin n => empiricalMeasure fun i : Fin n => X i ω) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [Measure.pi_of_empty]; infer_instance
    · haveI := isProbabilityMeasure_empiricalMeasure' hn fun i : Fin n => X i ω
      haveI : ∀ _ : Fin n,
          IsProbabilityMeasure (empiricalMeasure fun i : Fin n => X i ω) := fun _ => ‹_›
      infer_instance
  have hlamprob : ∀ n : ℕ, IsProbabilityMeasure ((Measure.pi fun _ : Fin n =>
      empiricalMeasure fun i : Fin n => X i ω).map
      fun w => Real.sqrt n • (f (meanStatistic h w) -
        f (meanStatistic h fun i : Fin n => X i ω))) := by
    intro n
    haveI := hpiE n
    exact Measure.isProbabilityMeasure_map (hmeasRootE n).aemeasurable
  have hGconv : ∀ t : ℝ, Tendsto (fun n : ℕ =>
      (((Measure.pi fun _ : Fin n => empiricalMeasure fun i : Fin n => X i ω).map
        fun w => Real.sqrt n • (f (meanStatistic h w) -
          f (meanStatistic h fun i : Fin n => X i ω)))
          {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ t}).toReal) atTop
      (𝓝 (normLimitCDF (D * covH * D.transpose) nrm t)) := fun t =>
    tendsto_measure_norm_le_of_weak hpsdS hSne hnrm_add hnrm_smul hnrm_def hlamprob hBweak t
  have hB : Tendsto (fun n : ℕ => supCDFDist
      (normLimitCDF (D * covH * D.transpose) nrm)
      (fun t => (((Measure.pi fun _ : Fin n => empiricalMeasure fun i : Fin n => X i ω).map
        fun w => Real.sqrt n • (f (meanStatistic h w) -
          f (meanStatistic h fun i : Fin n => X i ω)))
          {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ t}).toReal)) atTop (𝓝 0) := by
    have hb := tendsto_supCDFDist_zero (fun n => isCDF_measure_norm_le (hlamprob n) hnrm_cont)
      hcontJ hJcdf hGconv
    simpa only [supCDFDist_comm] using hb
  -- the Pólya squeeze on the rescaled distribution functions
  have hsqueeze : Tendsto (fun n : ℕ => supCDFDist
      (fun t => (((Measure.pi fun _ : Fin n => P).map
        fun w => Real.sqrt n • (f (meanStatistic h w) - f θ))
          {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ t}).toReal)
      (fun t => (((Measure.pi fun _ : Fin n => empiricalMeasure fun i : Fin n => X i ω).map
        fun w => Real.sqrt n • (f (meanStatistic h w) -
          f (meanStatistic h fun i : Fin n => X i ω)))
          {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ t}).toReal)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
      tendsto_const_nhds (by simpa using hA.add hB) (fun n => ?_) (fun n => ?_)
    · exact supCDFDist_nonneg (isCDF_measure_norm_le (hκprob n) hnrm_cont)
        (isCDF_measure_norm_le (hlamprob n) hnrm_cont)
    · exact supCDFDist_triangle_of_isCDF (isCDF_measure_norm_le (hκprob n) hnrm_cont) hJcdf
        (isCDF_measure_norm_le (hlamprob n) hnrm_cont)
  -- undo the `√n` rescaling of the argument
  refine hsqueeze.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hsqn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hFeq : (fun s : ℝ => (Pr {ω' | nrm (f (meanStatistic h fun i : Fin n => X i ω') - f θ)
        ≤ s}).toReal)
      = fun s : ℝ => (((Measure.pi fun _ : Fin n => P).map
        fun w => Real.sqrt n • (f (meanStatistic h w) - f θ))
          {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ Real.sqrt n * s}).toReal := by
    funext s
    congr 1
    have hset : MeasurableSet {w : Fin n → 𝓢 | nrm (f (meanStatistic h w) - f θ) ≤ s} :=
      measurableSet_le (hnrm_cont.measurable.comp
        ((hfmeas.comp (measurable_meanStatistic hhmeas)).sub measurable_const)) measurable_const
    have hpre : (fun w : Fin n → 𝓢 => Real.sqrt n • (f (meanStatistic h w) - f θ)) ⁻¹'
        {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ Real.sqrt n * s}
        = {w : Fin n → 𝓢 | nrm (f (meanStatistic h w) - f θ) ≤ s} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hnrm_smul,
        abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]
      constructor
      · intro hle; exact le_of_mul_le_mul_left hle hsqn
      · intro hle; exact mul_le_mul_of_nonneg_left hle hsqn.le
    rw [Measure.map_apply (hmeasRootP n)
      (measurableSet_le hnrm_cont.measurable measurable_const), hpre, ← hmap n,
      Measure.map_apply (hφmeas n) hset]
    rfl
  have hGeq : (fun s : ℝ => ((bootstrapLaw fun i : Fin n => X i ω)
        {w | nrm (f (meanStatistic h w) -
          f (meanStatistic h fun i : Fin n => X i ω)) ≤ s}).toReal)
      = fun s : ℝ => (((Measure.pi fun _ : Fin n =>
          empiricalMeasure fun i : Fin n => X i ω).map
        fun w => Real.sqrt n • (f (meanStatistic h w) -
          f (meanStatistic h fun i : Fin n => X i ω)))
          {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ Real.sqrt n * s}).toReal := by
    funext s
    congr 1
    have hpre : (fun w : Fin n → 𝓢 => Real.sqrt n • (f (meanStatistic h w) -
          f (meanStatistic h fun i : Fin n => X i ω))) ⁻¹'
        {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ Real.sqrt n * s}
        = {w : Fin n → 𝓢 | nrm (f (meanStatistic h w) -
          f (meanStatistic h fun i : Fin n => X i ω)) ≤ s} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hnrm_smul,
        abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]
      constructor
      · intro hle; exact le_of_mul_le_mul_left hle hsqn
      · intro hle; exact mul_le_mul_of_nonneg_left hle hsqn.le
    rw [Measure.map_apply (hmeasRootE n)
      (measurableSet_le hnrm_cont.measurable measurable_const), hpre]
    rfl
  rw [hFeq, hGeq]
  exact (supCDFDist_comp_mul_left hsqn.ne'
    (fun t => (((Measure.pi fun _ : Fin n => P).map
      fun w => Real.sqrt n • (f (meanStatistic h w) - f θ))
        {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ t}).toReal)
    (fun t => (((Measure.pi fun _ : Fin n => empiricalMeasure fun i : Fin n => X i ω).map
      fun w => Real.sqrt n • (f (meanStatistic h w) -
        f (meanStatistic h fun i : Fin n => X i ω)))
        {z : EuclideanSpace ℝ (Fin q) | nrm z ≤ t}).toReal)).symm

end SmoothFunctions

end StatLean.HypothesisTesting
