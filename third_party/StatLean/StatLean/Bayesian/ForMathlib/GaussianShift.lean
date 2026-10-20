module
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.SubGaussian
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF

@[expose] public section

/-!
# Gaussian shift, inner-projection, and tail bricks

Mathlib-level facts about the standard Gaussian on `EuclideanSpace ℝ ι` and its
mean-shifts `N(θ, I) = stdGaussian.map (· + θ)`, packaged for the Dirichlet–Laplace
posterior-contraction proof.

* `stdGaussian_map_add_add` — shifting by `a` then by `b` equals shifting by `a + b`.
* `stdGaussianShift_withDensity` — the Gaussian likelihood ratio (Girsanov/Esscher):
  `N(θ, I) = N(θ₀, I).withDensity exp(⟪θ−θ₀, y−θ₀⟫ − ‖θ−θ₀‖²/2)`.
* `stdGaussian_map_inner` — a linear form `⟪c, ·⟫` pushes the standard Gaussian to
  the one-dimensional Gaussian `N(0, ‖c‖²)`.
* `gaussianReal_measure_ge_le` / `stdGaussianShift_inner_ge_le` — the sub-Gaussian
  upper tail `P(X ≥ t) ≤ exp(−t²/2v)`, in the one-dimensional form and in its
  shifted inner-projection form.

**Reference.** Mathlib-level bricks (no book statement of their own) consumed by the
Dirichlet–Laplace posterior-contraction proof (Bhattacharya–Pati–Pillai–Dunson,
*Dirichlet–Laplace priors for optimal shrinkage*, JASA 2015 / arXiv:1401.5398;
tag `BPPD §X.Y`): they supply the Gaussian shift/tail machinery for the midpoint
tests and the denominator lower bound (BPPD §6).

**Proof formalization notes.** `stdGaussianShift_withDensity` re-bases the existing
`ProbabilityTheory.stdGaussian_withDensity_exp_shift` (Girsanov at `a = θ − θ₀`)
through `stdGaussian_map_add_add`; `stdGaussian_map_inner` specializes
`ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal` at the identity
covariance; the two tail bounds transport the event through the shift and the inner
projection and finish with Mathlib's one-dimensional Gaussian sub-Gaussian tail
`ProbabilityTheory.HasSubgaussianMGF.measure_ge_le`.

**Bibliographic comments.** The exponential-tilt (Esscher/Girsanov) shift of a
Gaussian and its sub-Gaussian upper tail are classical (Esscher 1932; Cramér 1938).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Two mean-shifts compose.** Shifting the standard Gaussian by `a` and then by
`b` is the same as shifting it by `a + b`. -/
theorem stdGaussian_map_add_add (a b : EuclideanSpace ℝ ι) :
    ((stdGaussian (EuclideanSpace ℝ ι)).map (· + a)).map (· + b)
      = (stdGaussian (EuclideanSpace ℝ ι)).map (· + (a + b)) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply, add_assoc]

/-- **Gaussian likelihood ratio (Girsanov / Esscher).** The mean-shift `N(θ, I)` is
`N(θ₀, I)` re-weighted by the density `exp(⟪θ − θ₀, y − θ₀⟫ − ‖θ − θ₀‖² / 2)` — i.e.
the pointwise Radon–Nikodym derivative `dN(θ, I)/dN(θ₀, I)`. This is the DL posterior
integrand (`dlLR θ₀ θ`), stated here density-side without referencing the concept
layer. -/
theorem stdGaussianShift_withDensity (θ₀ θ : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (· + θ)
      = ((stdGaussian (EuclideanSpace ℝ ι)).map (· + θ₀)).withDensity
          (fun y => ENNReal.ofReal
            (Real.exp (⟪θ - θ₀, y - θ₀⟫ - ‖θ - θ₀‖ ^ 2 / 2))) := by
  have hD_meas : Measurable (fun y : EuclideanSpace ℝ ι =>
      ENNReal.ofReal (Real.exp (⟪θ - θ₀, y - θ₀⟫ - ‖θ - θ₀‖ ^ 2 / 2))) := by
    fun_prop
  rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
    (stdGaussian (EuclideanSpace ℝ ι)) (· + θ₀) (by fun_prop) _ hD_meas]
  -- The pulled-back density `D ∘ (·+θ₀)` is exactly the `stdGaussian`-tilt at `θ − θ₀`.
  have hDcomp :
      ((fun y : EuclideanSpace ℝ ι =>
          ENNReal.ofReal (Real.exp (⟪θ - θ₀, y - θ₀⟫ - ‖θ - θ₀‖ ^ 2 / 2))) ∘ (· + θ₀))
        = fun x : EuclideanSpace ℝ ι =>
            ENNReal.ofReal (Real.exp (⟪θ - θ₀, x⟫ - ‖θ - θ₀‖ ^ 2 / 2)) := by
    funext x
    simp only [Function.comp_apply, add_sub_cancel_right]
  rw [hDcomp, stdGaussian_withDensity_exp_shift (θ - θ₀),
    stdGaussian_map_add_add (θ - θ₀) θ₀, sub_add_cancel]

/-- **A linear form pushes the standard Gaussian to a one-dimensional Gaussian.**
For `y ∼ stdGaussian` on `EuclideanSpace ℝ ι`, the scalar `⟪c, y⟫` is `N(0, ‖c‖²)`. -/
theorem stdGaussian_map_inner (c : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun y => ⟪c, y⟫)
      = gaussianReal 0 (‖c‖₊ ^ 2) := by
  have hL_meas : Measurable (fun y : EuclideanSpace ℝ ι => ⟪c, y⟫) :=
    (continuous_const.inner continuous_id).measurable
  haveI : IsProbabilityMeasure
      ((stdGaussian (EuclideanSpace ℝ ι)).map (fun y => ⟪c, y⟫)) :=
    Measure.isProbabilityMeasure_map hL_meas.aemeasurable
  apply MeasureTheory.Measure.ext_of_charFun
  funext t
  have hLHS : charFun ((stdGaussian (EuclideanSpace ℝ ι)).map (fun y => ⟪c, y⟫)) t
      = charFun (stdGaussian (EuclideanSpace ℝ ι)) (t • c) := by
    rw [charFun_apply_real, charFun_apply]
    have h_integrand_meas : AEStronglyMeasurable
        (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I))
        ((stdGaussian (EuclideanSpace ℝ ι)).map (fun y => ⟪c, y⟫)) :=
      (by fun_prop : Continuous fun x : ℝ =>
        Complex.exp (↑t * ↑x * Complex.I)).aestronglyMeasurable
    rw [integral_map hL_meas.aemeasurable h_integrand_meas]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only []
    rw [real_inner_smul_right, real_inner_comm]
    push_cast
    ring
  rw [hLHS, charFun_stdGaussian, charFun_gaussianReal]
  congr 1
  have hns : ((‖t • c‖ : ℝ) : ℂ) ^ 2 = (t : ℂ) ^ 2 * ((‖c‖ : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow,
      show ‖t • c‖ ^ 2 = t ^ 2 * ‖c‖ ^ 2 from by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]]
    push_cast; ring
  rw [hns]
  push_cast
  ring

/-- **Sub-Gaussian upper tail of a centered one-dimensional Gaussian.**
For `X ∼ N(0, v)` and a nonnegative threshold `t`,
`P(X ≥ t) ≤ exp(−t² / (2v))`. (Holds degenerately at `v = 0`, where the right side
is `1`.) -/
theorem gaussianReal_measure_ge_le (v : ℝ≥0) (t : ℝ)
    -- LEAN-ONLY: tail domain requires a nonnegative threshold; genuine caller input
    (ht : 0 ≤ t) :
    gaussianReal 0 v {x : ℝ | t ≤ x}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * (v : ℝ)))) := by
  -- `id` is sub-Gaussian under `N(0, v)` with variance proxy `v` (MGF equality).
  have hsub : HasSubgaussianMGF (id : ℝ → ℝ) v (gaussianReal 0 v) := by
    refine ⟨fun s => ?_, fun s => ?_⟩
    · simpa using integrable_exp_mul_gaussianReal s
    · rw [mgf_id_gaussianReal]; simp
  have hle := hsub.measure_ge_le ht
  -- Transfer the real-valued measure inequality back to `ℝ≥0∞`.
  rw [← ENNReal.ofReal_toReal
    (measure_ne_top (gaussianReal 0 v) {x : ℝ | t ≤ x})]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa [Measure.real, id] using hle

/-- **Shifted inner-projection tail.** For `y ∼ N(θ', I)` the linear form
`⟪c, y − θ'⟫` is `N(0, ‖c‖²)`, so its upper tail is `exp(−t² / (2‖c‖²))` for
`t ≥ 0`. This is the error bound of the DL midpoint tests (BPPD §6). -/
theorem stdGaussianShift_inner_ge_le (θ' c : EuclideanSpace ℝ ι) (t : ℝ)
    -- LEAN-ONLY: tail domain requires a nonnegative threshold; genuine caller input
    (ht : 0 ≤ t) :
    ((stdGaussian (EuclideanSpace ℝ ι)).map (· + θ'))
        {y : EuclideanSpace ℝ ι | t ≤ ⟪c, y - θ'⟫}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * ‖c‖ ^ 2))) := by
  have hmeas_shift : Measurable (fun x : EuclideanSpace ℝ ι => x + θ') := by fun_prop
  have hmeas_inner : Measurable (fun y : EuclideanSpace ℝ ι => ⟪c, y⟫) :=
    (continuous_const.inner continuous_id).measurable
  have hset : MeasurableSet {y : EuclideanSpace ℝ ι | t ≤ ⟪c, y - θ'⟫} := by
    apply measurableSet_le measurable_const
    fun_prop
  have hIci : MeasurableSet {z : ℝ | t ≤ z} :=
    measurableSet_le measurable_const measurable_id
  calc ((stdGaussian (EuclideanSpace ℝ ι)).map (· + θ'))
          {y : EuclideanSpace ℝ ι | t ≤ ⟪c, y - θ'⟫}
      = ((stdGaussian (EuclideanSpace ℝ ι)).map (fun y => ⟪c, y⟫)) {z : ℝ | t ≤ z} := by
        rw [Measure.map_apply hmeas_shift hset,
          Measure.map_apply hmeas_inner hIci]
        congr 1
        ext x
        simp only [Set.mem_preimage, Set.mem_setOf_eq, add_sub_cancel_right]
    _ = gaussianReal 0 (‖c‖₊ ^ 2) {z : ℝ | t ≤ z} := by rw [stdGaussian_map_inner]
    _ ≤ _ := by
        have hcoe : ((‖c‖₊ ^ 2 : ℝ≥0) : ℝ) = ‖c‖ ^ 2 := by push_cast; ring
        rw [← hcoe]
        exact gaussianReal_measure_ge_le (‖c‖₊ ^ 2) t ht

end StatLean.Bayesian
