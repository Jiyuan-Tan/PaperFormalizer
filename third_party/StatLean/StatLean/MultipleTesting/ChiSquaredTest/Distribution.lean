module
public import StatLean.MultipleTesting.ForMathlib.GaussianMoments
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Chi-squared test statistic — mean and variance under H₀ and H₁

For the Gaussian sequence model $Y_i = \theta_i + z_i$ with $z_i \sim N(0,1)$ i.i.d.
($i = 1, \dots, n$), the chi-squared goodness-of-fit statistic is
$T_n = \sum_{i=1}^n Y_i^2 = \lVert Y\rVert^2$. Its first two moments — the inputs to the
power analysis through the signal-to-noise ratio $\theta_n = \lVert\theta\rVert/\sqrt{2n}$ — are:

* **Under the null $H_0$** ($\theta = 0$, so $T_n = \sum_i z_i^2$):
  $\mathbb{E}[T_n] = n$ and $\operatorname{Var}[T_n] = 2n$;
* **Under the alternative $H_1$** ($T_n = \sum_i (\theta_i + z_i)^2$):
  $\mathbb{E}[T_n] = n + \lVert\theta\rVert^2$ and
  $\operatorname{Var}[T_n] = 2n + 4\lVert\theta\rVert^2$, where
  $\lVert\theta\rVert^2 = \sum_i \theta_i^2$.

Equivalently, under $H_0$ the statistic follows the chi-squared law $T_n \sim \chi^2_n$
(mean $n$, variance $2n$), and under $H_1$ it follows a noncentral chi-squared with
noncentrality $\lVert\theta\rVert^2$.

**Reference.** E. J. Candès, *STAT 300C: Theory of Statistics*, Lecture Notes, Stanford
University, 2023, Lecture 2, §2.3 (the chi-squared test in the Gaussian sequence model and its
power via the signal-to-noise ratio $\theta_n = \lVert\theta\rVert/\sqrt{2n}$).

**Proof formalization notes.** The per-coordinate moments
$\mathbb{E}[z^2]=1$, $\mathbb{E}[z^3]=0$, $\mathbb{E}[z^4]=3$, $\operatorname{Var}[z^2]=2$ come
from the merged `ForMathlib/GaussianMoments.lean`; the sums use linearity and (for the variances)
independence across coordinates, so the cross-covariances vanish. (The exact law $T_n \sim \chi^2_n$
under $H_0$ is `ForMathlib/ChiSquared.map_sum_sq_eq_chiSquared`; the $n\to\infty$ CLT normal
approximation is a separate asymptotic statement.)

The variances are assembled from Mathlib's `ProbabilityTheory.IndepFun.variance_sum`
($\operatorname{Var}[\sum X_i] = \sum \operatorname{Var}[X_i]$ for pairwise-independent $X_i$), with
the per-coordinate variances $\operatorname{Var}[z_i^2] = 2$ and
$\operatorname{Var}[(\theta_i+z_i)^2] = 4\theta_i^2+2$ transported to the standard Gaussian via
`ProbabilityTheory.variance_map`, so a $\operatorname{Var}[\sum]$ lemma existed and no manual
cross-term expansion was needed.

**Bibliographic comments.** This is classical folklore with no single seminal source. The
chi-squared goodness-of-fit statistic originates with K. Pearson, "On the criterion that a given
system of deviations from the probable in the case of a correlated system of variables is such that
it can be reasonably supposed to have arisen from random sampling," *Philosophical Magazine*,
Series 5, **50** (1900), 157–175, where the $\chi^2$ limiting distribution was derived. The mean
and variance of $\chi^2_n$ ($n$ and $2n$) and of the noncentral $\chi^2$ are standard moment
computations found in any mathematical-statistics text; the Candès lecture notes apply them to the
Gaussian-sequence power analysis used here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : ℕ}

/-! ### Standard-Gaussian helpers (over `gaussianReal 0 1`) -/

/-- Integrability of every power `x ↦ xᵏ` against the standard Gaussian, read off from the fact
that `id` lies in every `Lᵖ` space (`memLp_id_gaussianReal'`). (Re-derived here from the public
moment API; the `GaussianMoments.lean` analogue is `private`.) -/
private lemma integrable_pow_gaussian (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp
  have h : Integrable (fun x : ℝ => ‖id x‖ ^ k) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (μ := 0) (v := 1) (k : ℝ≥0∞)
      (ENNReal.natCast_ne_top k)).integrable_norm_pow hk0.ne'
  refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp [id, Real.norm_eq_abs]

/-- Integrability of `x ↦ x` against the standard Gaussian (the `k = 1` case rewritten). -/
private lemma integrable_id_gaussian : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
  simpa using integrable_pow_gaussian 1

/-- The central second moment of `(a+Z)²` for `Z ∼ N(0,1)`: `Var[(a+Z)²] = 4a²+2`. Proved by
expanding `((a+x)²-(a²+1))² = (x²−1)² + 4a²x² + 4a x³ − 4a x` and integrating term by term against
the standard-Gaussian moments `E[x²]=1`, `E[(x²−1)²]=2`, `E[x³]=0`, `E[x]=0`. -/
private lemma variance_shift_sq_gaussian (a : ℝ) :
    variance (fun x : ℝ => (a + x) ^ 2) (gaussianReal 0 1) = 4 * a ^ 2 + 2 := by
  have hi2 : Integrable (fun x : ℝ => (x ^ 2 - 1) ^ 2) (gaussianReal 0 1) := by
    have he : ∀ x : ℝ, (x ^ 2 - 1) ^ 2 = x ^ 4 - 2 * x ^ 2 + 1 := fun x => by ring
    exact (((integrable_pow_gaussian 4).sub ((integrable_pow_gaussian 2).const_mul 2)).add
      (integrable_const 1)).congr (Filter.Eventually.of_forall fun x => (he x).symm)
  have hmean : ∫ x, (a + x) ^ 2 ∂(gaussianReal 0 1) = a ^ 2 + 1 := by
    have he : ∀ x : ℝ, (a + x) ^ 2 = a ^ 2 + 2 * a * x + x ^ 2 := fun x => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall he),
        integral_add (f := fun x => a ^ 2 + 2 * a * x) (g := fun x => x ^ 2)
          ((integrable_const (a ^ 2)).add (integrable_id_gaussian.const_mul (2 * a)))
          (integrable_pow_gaussian 2),
        integral_add (f := fun _ => a ^ 2) (g := fun x => 2 * a * x)
          (integrable_const (a ^ 2)) (integrable_id_gaussian.const_mul (2 * a)),
        integral_const, integral_const_mul, integral_id_gaussianReal, integral_sq_stdGaussian]
    simp
  rw [variance_eq_integral (by fun_prop)]
  rw [show (gaussianReal 0 1)[fun x : ℝ => (a + x) ^ 2] = a ^ 2 + 1 from hmean]
  change ∫ x, ((a + x) ^ 2 - (a ^ 2 + 1)) ^ 2 ∂(gaussianReal 0 1) = 4 * a ^ 2 + 2
  have hs : ∀ x : ℝ, ((a + x) ^ 2 - (a ^ 2 + 1)) ^ 2
      = (x ^ 2 - 1) ^ 2 + (4 * a ^ 2) * x ^ 2 + (4 * a) * x ^ 3 - (4 * a) * x := fun x => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hs),
      integral_sub (f := fun x => (x ^ 2 - 1) ^ 2 + (4 * a ^ 2) * x ^ 2 + (4 * a) * x ^ 3)
        (g := fun x => (4 * a) * x)
        ((hi2.add ((integrable_pow_gaussian 2).const_mul (4 * a ^ 2))).add
          ((integrable_pow_gaussian 3).const_mul (4 * a)))
        (integrable_id_gaussian.const_mul (4 * a)),
      integral_add (f := fun x => (x ^ 2 - 1) ^ 2 + (4 * a ^ 2) * x ^ 2)
        (g := fun x => (4 * a) * x ^ 3)
        (hi2.add ((integrable_pow_gaussian 2).const_mul (4 * a ^ 2)))
        ((integrable_pow_gaussian 3).const_mul (4 * a)),
      integral_add (f := fun x => (x ^ 2 - 1) ^ 2) (g := fun x => (4 * a ^ 2) * x ^ 2)
        hi2 ((integrable_pow_gaussian 2).const_mul (4 * a ^ 2)),
      variance_sq_stdGaussian,
      integral_const_mul, integral_sq_stdGaussian,
      integral_const_mul, integral_cube_stdGaussian,
      integral_const_mul, integral_id_gaussianReal]
  ring

/-- `Var[Z²] = 2` for `Z ∼ N(0,1)` in `variance` form (the `a = 0` case of
`variance_shift_sq_gaussian`). -/
private lemma variance_sq_gaussian : variance (fun x : ℝ => x ^ 2) (gaussianReal 0 1) = 2 := by
  rw [show (fun x : ℝ => x ^ 2) = (fun x : ℝ => (0 + x) ^ 2) from by funext x; rw [zero_add]]
  rw [variance_shift_sq_gaussian]; norm_num

/-! ### Per-coordinate facts pushed through the law `Measure.map X P = N(0,1)` -/

/-- Integrability of `ω ↦ (X ω)ᵏ` under `P`, transported from `integrable_pow_gaussian` through the
law `Measure.map X P = N(0,1)`. -/
private lemma integrable_pow_law (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hlaw : Measure.map X P = gaussianReal 0 1) (k : ℕ) :
    Integrable (fun ω => (X ω) ^ k) P := by
  have hg : Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := integrable_pow_gaussian k
  rw [← hlaw] at hg
  simpa [Function.comp] using!
    (integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable).mp hg

/-- Integrability of `X` itself under `P` (the `k = 1` case rewritten). -/
private lemma coord_integrable_id (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hlaw : Measure.map X P = gaussianReal 0 1) :
    Integrable X P := by
  have hL1 : Integrable (fun y : ℝ => y) (gaussianReal 0 1) := integrable_id_gaussian
  rw [← hlaw] at hL1
  simpa [Function.comp] using!
    (integrable_map_measure hL1.aestronglyMeasurable hX.aemeasurable).mp hL1

/-- `E[X] = 0` via `integral_map` and `integral_id_gaussianReal`. -/
private lemma coord_integral_id (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hlaw : Measure.map X P = gaussianReal 0 1) :
    ∫ ω, X ω ∂P = 0 := by
  have h : ∫ y, y ∂(Measure.map X P) = ∫ ω, X ω ∂P :=
    integral_map hX.aemeasurable (f := fun y => y) (by fun_prop)
  rw [← h, hlaw, integral_id_gaussianReal]

/-- `E[X²] = 1` via `integral_map` and `integral_sq_stdGaussian`. -/
private lemma coord_integral_sq (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hlaw : Measure.map X P = gaussianReal 0 1) :
    ∫ ω, (X ω) ^ 2 ∂P = 1 := by
  have h : ∫ y, y ^ 2 ∂(Measure.map X P) = ∫ ω, (X ω) ^ 2 ∂P :=
    integral_map hX.aemeasurable (f := fun y => y ^ 2) (by fun_prop)
  rw [← h, hlaw, integral_sq_stdGaussian]

/-- `ω ↦ (X ω)² ∈ L²(P)`, transported from `id ∈ L⁴` through the law. -/
private lemma coord_memLp_sq (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hlaw : Measure.map X P = gaussianReal 0 1) :
    MemLp (fun ω => (X ω) ^ 2) 2 P := by
  rw [memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable (fun ω => (X ω) ^ 2) P)]
  exact (integrable_pow_law P hX hlaw 4).congr (Filter.Eventually.of_forall fun ω => by ring)

/-- `ω ↦ (a + X ω)² ∈ L²(P)`, transported from the degree-4 polynomial expansion through the law. -/
private lemma coord_memLp_shift (P : Measure Ω) [IsProbabilityMeasure P] (a : ℝ) {X : Ω → ℝ}
    (hX : Measurable X) (hlaw : Measure.map X P = gaussianReal 0 1) :
    MemLp (fun ω => (a + X ω) ^ 2) 2 P := by
  rw [memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable (fun ω => (a + X ω) ^ 2) P)]
  have hpoly : Integrable (fun ω => a ^ 4 + (4 * a ^ 3) * (X ω) ^ 1 + (6 * a ^ 2) * (X ω) ^ 2
      + (4 * a) * (X ω) ^ 3 + (X ω) ^ 4) P :=
    ((((integrable_const _).add ((integrable_pow_law P hX hlaw 1).const_mul (4 * a ^ 3))).add
      ((integrable_pow_law P hX hlaw 2).const_mul (6 * a ^ 2))).add
      ((integrable_pow_law P hX hlaw 3).const_mul (4 * a))).add (integrable_pow_law P hX hlaw 4)
  exact hpoly.congr (Filter.Eventually.of_forall fun ω => by ring)

/-- `Var[X²] = 2` under `P`, transported from `variance_sq_gaussian` via `variance_map`. -/
private lemma coord_variance_sq (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hlaw : Measure.map X P = gaussianReal 0 1) :
    variance (fun ω => (X ω) ^ 2) P = 2 := by
  have hvm := variance_map (μ := P) (X := fun x : ℝ => x ^ 2) (Y := X) (by fun_prop) hX.aemeasurable
  rw [hlaw, variance_sq_gaussian] at hvm
  simp only [Function.comp_def] at hvm
  exact hvm.symm

/-- `Var[(a+X)²] = 4a²+2` under `P`, transported from `variance_shift_sq_gaussian` via
`variance_map`. -/
private lemma coord_variance_shift (P : Measure Ω) [IsProbabilityMeasure P] (a : ℝ) {X : Ω → ℝ}
    (hX : Measurable X) (hlaw : Measure.map X P = gaussianReal 0 1) :
    variance (fun ω => (a + X ω) ^ 2) P = 4 * a ^ 2 + 2 := by
  have hvm := variance_map (μ := P) (X := fun x : ℝ => (a + x) ^ 2) (Y := X)
    (by fun_prop) hX.aemeasurable
  rw [hlaw, variance_shift_sq_gaussian] at hvm
  simp only [Function.comp_def] at hvm
  exact hvm.symm

/-! ### Main statements -/

/-- **χ² statistic mean under H₀**: `E[∑ zᵢ²] = n` for `zᵢ ∼ N(0,1)` i.i.d. (Candès L2 §2.3). -/
theorem chiSq_H0_mean (P : Measure Ω) [IsProbabilityMeasure P] (z : Fin n → Ω → ℝ)
    -- USER-INPUT: each zᵢ is measurable; Candès L2 §2.3
    (hmeas : ∀ i, Measurable (z i))
    -- USER-INPUT: each zᵢ ∼ N(0,1); Candès L2 §2.3
    (hlaw : ∀ i, Measure.map (z i) P = gaussianReal 0 1) :
    ∫ ω, ∑ i, (z i ω) ^ 2 ∂P = (n : ℝ) := by
  rw [integral_finset_sum Finset.univ (fun i _ => integrable_pow_law P (hmeas i) (hlaw i) 2)]
  have hval : ∀ i, ∫ ω, (z i ω) ^ 2 ∂P = 1 := fun i => coord_integral_sq P (hmeas i) (hlaw i)
  simp_rw [hval]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **χ² statistic variance under H₀**: `Var[∑ zᵢ²] = 2n` for `zᵢ ∼ N(0,1)` i.i.d.
(Candès L2 §2.3). -/
theorem chiSq_H0_variance (P : Measure Ω) [IsProbabilityMeasure P] (z : Fin n → Ω → ℝ)
    -- USER-INPUT: each zᵢ is measurable; Candès L2 §2.3
    (hmeas : ∀ i, Measurable (z i))
    -- USER-INPUT: each zᵢ ∼ N(0,1); Candès L2 §2.3
    (hlaw : ∀ i, Measure.map (z i) P = gaussianReal 0 1)
    -- USER-INPUT: the zᵢ are jointly independent; Candès L2 §2.3
    (hindep : iIndepFun z P) :
    ∫ ω, (∑ i, (z i ω) ^ 2 - (n : ℝ)) ^ 2 ∂P = 2 * (n : ℝ) := by
  set S : Ω → ℝ := fun ω => ∑ i, (z i ω) ^ 2 with hSdef
  have haem : AEMeasurable S P :=
    (Finset.measurable_sum Finset.univ (fun i _ => by have := hmeas i; fun_prop)).aemeasurable
  have hmean : ∫ ω, S ω ∂P = (n : ℝ) := chiSq_H0_mean P z hmeas hlaw
  have hgoal : variance S P = ∫ ω, (S ω - (n : ℝ)) ^ 2 ∂P := by
    rw [variance_eq_integral haem, hmean]
  change ∫ ω, (S ω - (n : ℝ)) ^ 2 ∂P = 2 * (n : ℝ)
  rw [← hgoal]
  have hSsum : S = ∑ i : Fin n, (fun ω => (z i ω) ^ 2) := by
    rw [hSdef]; funext ω; rw [Finset.sum_apply]
  rw [hSsum, IndepFun.variance_sum
        (fun i _ => coord_memLp_sq P (hmeas i) (hlaw i))
        (fun i _ j _ hij => (hindep.comp (fun _ x => x ^ 2) (fun _ => by fun_prop)).indepFun hij)]
  have hv : ∀ i, variance (fun ω => (z i ω) ^ 2) P = 2 :=
    fun i => coord_variance_sq P (hmeas i) (hlaw i)
  simp_rw [hv]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **χ² statistic mean under H₁**: `E[∑ (θᵢ+zᵢ)²] = n + ‖θ‖²` (Candès L2 §2.3). -/
theorem chiSq_H1_mean (P : Measure Ω) [IsProbabilityMeasure P] (z : Fin n → Ω → ℝ) (θ : Fin n → ℝ)
    -- USER-INPUT: each zᵢ is measurable; Candès L2 §2.3
    (hmeas : ∀ i, Measurable (z i))
    -- USER-INPUT: each zᵢ ∼ N(0,1); Candès L2 §2.3
    (hlaw : ∀ i, Measure.map (z i) P = gaussianReal 0 1) :
    ∫ ω, ∑ i, (θ i + z i ω) ^ 2 ∂P = (∑ i, (θ i) ^ 2) + (n : ℝ) := by
  have hint : ∀ i, Integrable (fun ω => (θ i + z i ω) ^ 2) P := by
    intro i
    have h0 := coord_integrable_id P (hmeas i) (hlaw i)
    have h2 := integrable_pow_law P (hmeas i) (hlaw i) 2
    have he : ∀ ω, (θ i + z i ω) ^ 2 = (θ i) ^ 2 + (2 * θ i) * (z i ω) + (z i ω) ^ 2 :=
      fun ω => by ring
    exact (((integrable_const _).add (h0.const_mul (2 * θ i))).add h2).congr
      (Filter.Eventually.of_forall fun ω => (he ω).symm)
  have hval : ∀ i, ∫ ω, (θ i + z i ω) ^ 2 ∂P = (θ i) ^ 2 + 1 := by
    intro i
    have h0 := coord_integrable_id P (hmeas i) (hlaw i)
    have h2 := integrable_pow_law P (hmeas i) (hlaw i) 2
    have hi0 := coord_integral_id P (hmeas i) (hlaw i)
    have hi2 := coord_integral_sq P (hmeas i) (hlaw i)
    have he : ∀ ω, (θ i + z i ω) ^ 2 = (θ i) ^ 2 + (2 * θ i) * (z i ω) + (z i ω) ^ 2 :=
      fun ω => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall he),
        integral_add (f := fun ω => (θ i) ^ 2 + (2 * θ i) * (z i ω)) (g := fun ω => (z i ω) ^ 2)
          ((integrable_const ((θ i) ^ 2)).add (h0.const_mul (2 * θ i))) h2,
        integral_add (f := fun _ => (θ i) ^ 2) (g := fun ω => (2 * θ i) * (z i ω))
          (integrable_const ((θ i) ^ 2)) (h0.const_mul (2 * θ i)),
        integral_const, integral_const_mul, hi0, hi2]
    simp
  rw [integral_finset_sum Finset.univ (fun i _ => hint i)]
  simp_rw [hval]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]

/-- **χ² statistic variance under H₁**: `Var[∑ (θᵢ+zᵢ)²] = 2n + 4‖θ‖²` (Candès L2 §2.3). -/
theorem chiSq_H1_variance (P : Measure Ω) [IsProbabilityMeasure P] (z : Fin n → Ω → ℝ)
    (θ : Fin n → ℝ)
    -- USER-INPUT: each zᵢ is measurable; Candès L2 §2.3
    (hmeas : ∀ i, Measurable (z i))
    -- USER-INPUT: each zᵢ ∼ N(0,1); Candès L2 §2.3
    (hlaw : ∀ i, Measure.map (z i) P = gaussianReal 0 1)
    -- USER-INPUT: the zᵢ are jointly independent; Candès L2 §2.3
    (hindep : iIndepFun z P) :
    ∫ ω, (∑ i, (θ i + z i ω) ^ 2 - ((∑ i, (θ i) ^ 2) + (n : ℝ))) ^ 2 ∂P
      = 2 * (n : ℝ) + 4 * (∑ i, (θ i) ^ 2) := by
  set S : Ω → ℝ := fun ω => ∑ i, (θ i + z i ω) ^ 2 with hSdef
  have haem : AEMeasurable S P :=
    (Finset.measurable_sum Finset.univ (fun i _ => by have := hmeas i; fun_prop)).aemeasurable
  have hmean : ∫ ω, S ω ∂P = (∑ i, (θ i) ^ 2) + (n : ℝ) := chiSq_H1_mean P z θ hmeas hlaw
  have hgoal : variance S P = ∫ ω, (S ω - ((∑ i, (θ i) ^ 2) + (n : ℝ))) ^ 2 ∂P := by
    rw [variance_eq_integral haem, hmean]
  change ∫ ω, (S ω - ((∑ i, (θ i) ^ 2) + (n : ℝ))) ^ 2 ∂P = 2 * (n : ℝ) + 4 * (∑ i, (θ i) ^ 2)
  rw [← hgoal]
  have hSsum : S = ∑ i : Fin n, (fun ω => (θ i + z i ω) ^ 2) := by
    rw [hSdef]; funext ω; rw [Finset.sum_apply]
  rw [hSsum, IndepFun.variance_sum
        (fun i _ => coord_memLp_shift P (θ i) (hmeas i) (hlaw i))
        (fun i _ j _ hij =>
          (hindep.comp (fun i x => (θ i + x) ^ 2) (fun _ => by fun_prop)).indepFun hij)]
  have hv : ∀ i, variance (fun ω => (θ i + z i ω) ^ 2) P = 4 * (θ i) ^ 2 + 2 :=
    fun i => coord_variance_shift P (θ i) (hmeas i) (hlaw i)
  simp_rw [hv]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  ring

end StatLean.MultipleTesting
