module
public import StatLean.Bayesian.Conjugacy.NormalNormal
public import StatLean.Bayesian.ForMathlib.GaussianDeriv
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Linear-shrinkage and James–Stein risk

The optimality side of the normal hierarchy. The linear-shrinkage estimator `c·X` has frequentist
risk `∑ᵢ((1−c)²θᵢ² + c²σ²)` and Bayes risk (under `θ ∼ N(0, τ²)`) `p·((1−c)²τ² + c²σ²)`, minimized
at the oracle weight `c* = τ²/(σ²+τ²)` — the empirical-Bayes shrinkage factor whose Bayes risk
`p·σ²τ²/(σ²+τ²)` is proved in `StatLean.MultipleTesting.empiricalBayes_risk` (Candès, STAT 300C;
cited, not imported — the DAG forbids importing that area's concept files). The James–Stein
estimator `(1 − (p−2)σ²/‖X‖²)·X` strictly dominates the MLE `X` in dimension `p ≥ 3` (the Stein
effect).

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). Note 2.8.2 (the Stein effect), p. 96; Example 4.2.3 (truncated
James–Stein); §10.5 (empirical-Bayes justifications of the Stein effect), p. 484.

**Proof formalization notes.** The linear-shrinkage risk is a coordinatewise Gaussian
bias²+variance computation (`integral_id_gaussianReal`, `variance_id_gaussianReal` per coordinate,
`Measure.pi` Fubini); the Bayes risk integrates it against `N(0,τ²)`; the argmin is a real
quadratic-in-`c` minimization (`nlinarith`/completing the square). The James–Stein risk identity
uses the Gaussian integration-by-parts (Stein's lemma) built from
`ForMathlib.GaussianDeriv.hasDerivAt_gaussianPDFReal` and the pinned interval/improper IBP; the
`p ≥ 3` hypothesis is what makes `E‖X‖⁻²` finite. Dominance is the risk identity plus positivity.

**Bibliographic comments.** The inadmissibility of the sample mean in dimension `≥ 3` is C. Stein
("Inadmissibility of the usual estimator for the mean of a multivariate normal distribution,"
*Proc. Third Berkeley Symp.* 1 (1956), 197–206); the explicit dominating estimator and its risk are
W. James and C. Stein ("Estimation with quadratic loss," *Proc. Fourth Berkeley Symp.* 1 (1961),
361–379). The empirical-Bayes reading — shrinkage toward a data-estimated prior mean — is B. Efron
and C. Morris (1973).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.Bayesian

/-- The **linear-shrinkage estimator** `x ↦ c·x` (shrinkage toward the origin). -/
noncomputable def linearShrinkage (c : ℝ) {p : ℕ} (x : Fin p → ℝ) : Fin p → ℝ := fun i => c * x i

/-- The **James–Stein estimator** `x ↦ (1 − (p−2)σ²/‖x‖²)·x` (James and Stein 1961). -/
noncomputable def jamesSteinEstimator (σ2 : ℝ) {p : ℕ} (x : Fin p → ℝ) : Fin p → ℝ :=
  fun i => (1 - ((p : ℝ) - 2) * σ2 / (∑ j, (x j) ^ 2)) * x i

/-- Integrability of a shrunken square `y ↦ (c·y − b)²` against any real Gaussian (it is the square
of an `L²` function, a degree-2 polynomial). -/
private lemma gaussian_shrink_integrable (c b m : ℝ) (σ2 : ℝ≥0) :
    Integrable (fun y => (c * y - b) ^ 2) (gaussianReal m σ2) := by
  have h2 : MemLp (fun y => c * y - b) 2 (gaussianReal m σ2) :=
    ((memLp_id_gaussianReal 2).const_mul c).sub (memLp_const b)
  simpa using h2.integrable_sq

/-- Integrability of `y ↦ y²` against any real Gaussian (second moment). -/
private lemma gaussian_sq_integrable (m : ℝ) (σ2 : ℝ≥0) :
    Integrable (fun y => y ^ 2) (gaussianReal m σ2) := by
  simpa using (memLp_id_gaussianReal 2).integrable_sq

/-- The centred second moment of a real Gaussian: `∫ (y − θ)² ∂N(θ, σ²) = σ²` (its variance). -/
private lemma gaussian_centred_sq (θ : ℝ) (σ2 : ℝ≥0) :
    ∫ y, (y - θ) ^ 2 ∂(gaussianReal θ σ2) = (σ2 : ℝ) := by
  rw [← variance_id_gaussianReal (μ := θ) (v := σ2), variance_eq_integral aemeasurable_id]
  simp only [id_eq, integral_id_gaussianReal]

/-- The centred first moment of a real Gaussian: `∫ (y − θ) ∂N(θ, σ²) = 0`. -/
private lemma gaussian_centred (θ : ℝ) (σ2 : ℝ≥0) :
    ∫ y, (y - θ) ∂(gaussianReal θ σ2) = 0 := by
  have hy : Integrable (fun y : ℝ => y) (gaussianReal θ σ2) :=
    (memLp_id_gaussianReal 2).integrable (by norm_num)
  calc ∫ y, (y - θ) ∂(gaussianReal θ σ2)
      = (∫ y, y ∂(gaussianReal θ σ2)) - ∫ _y, θ ∂(gaussianReal θ σ2) :=
        integral_sub hy (integrable_const θ)
    _ = 0 := by rw [integral_id_gaussianReal, integral_const]; simp

/-- The second moment of a mean-zero real Gaussian: `∫ y² ∂N(0, τ²) = τ²`. -/
private lemma gaussian_sq_mean_zero (τ2 : ℝ≥0) :
    ∫ y, y ^ 2 ∂(gaussianReal 0 τ2) = (τ2 : ℝ) := by
  have h := gaussian_centred_sq 0 τ2
  simpa using h

/-- The **coordinatewise linear-shrinkage risk**: `∫ (c·y − θ)² ∂N(θ, σ²) = (1−c)²θ² + c²σ²`
(bias² + variance). This holds for every `σ² ≥ 0`, so the nondegeneracy hypothesis of the
headline theorem is not needed here. -/
private lemma gaussian_shrink_coord (c θ : ℝ) (σ2 : ℝ≥0) :
    ∫ y, (c * y - θ) ^ 2 ∂(gaussianReal θ σ2)
      = (1 - c) ^ 2 * θ ^ 2 + c ^ 2 * (σ2 : ℝ) := by
  have hlin : Integrable (fun y => y - θ) (gaussianReal θ σ2) :=
    ((memLp_id_gaussianReal 2).integrable (by norm_num)).sub (integrable_const θ)
  have hsq : Integrable (fun y => (y - θ) ^ 2) (gaussianReal θ σ2) := by
    have h2 : MemLp (fun y => y - θ) 2 (gaussianReal θ σ2) :=
      (memLp_id_gaussianReal 2).sub (memLp_const θ)
    simpa using h2.integrable_sq
  calc ∫ y, (c * y - θ) ^ 2 ∂(gaussianReal θ σ2)
      = ∫ y, (c ^ 2 * (y - θ) ^ 2
          + ((2 * c * (c - 1) * θ) * (y - θ) + (c - 1) ^ 2 * θ ^ 2)) ∂(gaussianReal θ σ2) := by
        apply integral_congr_ae; filter_upwards with y; ring
    _ = (∫ y, c ^ 2 * (y - θ) ^ 2 ∂(gaussianReal θ σ2))
          + ∫ y, ((2 * c * (c - 1) * θ) * (y - θ) + (c - 1) ^ 2 * θ ^ 2) ∂(gaussianReal θ σ2) :=
        integral_add (hsq.const_mul _) ((hlin.const_mul _).add (integrable_const _))
    _ = c ^ 2 * (∫ y, (y - θ) ^ 2 ∂(gaussianReal θ σ2))
          + ((2 * c * (c - 1) * θ) * (∫ y, (y - θ) ∂(gaussianReal θ σ2)) + (c - 1) ^ 2 * θ ^ 2) := by
        rw [integral_const_mul, integral_add (hlin.const_mul _) (integrable_const _),
          integral_const_mul, integral_const]
        simp
    _ = (1 - c) ^ 2 * θ ^ 2 + c ^ 2 * (σ2 : ℝ) := by
        rw [gaussian_centred_sq, gaussian_centred]; ring

/-- The linear-shrinkage frequentist risk value, computed without the nondegeneracy hypothesis so
that both the headline theorem and the Bayes-risk theorem can invoke it. -/
private lemma linearShrinkage_risk_value (c : ℝ) {p : ℕ} (θ : Fin p → ℝ) (σ2 : ℝ≥0) :
    (∫ x, ∑ i, (linearShrinkage c x i - θ i) ^ 2 ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      = ∑ i, ((1 - c) ^ 2 * (θ i) ^ 2 + c ^ 2 * (σ2 : ℝ)) := by
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [linearShrinkage]
    rw [show (∫ x, (c * x i - θ i) ^ 2 ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
          = ∫ y, (c * y - θ i) ^ 2 ∂(gaussianReal (θ i) σ2) from
        integral_comp_eval (μ := fun i => gaussianReal (θ i) σ2) (i := i)
          (f := fun y => (c * y - θ i) ^ 2)
          (gaussian_shrink_integrable c (θ i) (θ i) σ2).aestronglyMeasurable]
    exact gaussian_shrink_coord c (θ i) σ2
  · intro i _
    simp only [linearShrinkage]
    exact integrable_comp_eval (μ := fun i => gaussianReal (θ i) σ2) (i := i)
      (f := fun y => (c * y - θ i) ^ 2) (gaussian_shrink_integrable c (θ i) (θ i) σ2)

/-- **Frequentist risk of linear shrinkage** (3D.1): `R(θ, c·X) = ∑ᵢ((1−c)²θᵢ² + c²σ²)`. -/
theorem normalMeans_linearShrinkage_risk (c : ℝ) {p : ℕ} (θ : Fin p → ℝ) (σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate noise variance; Robert Note 2.8.2
    (hσ : σ2 ≠ 0) :
    (∫ x, ∑ i, (linearShrinkage c x i - θ i) ^ 2 ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      = ∑ i, ((1 - c) ^ 2 * (θ i) ^ 2 + c ^ 2 * (σ2 : ℝ)) :=
  linearShrinkage_risk_value c θ σ2

/-- **Bayes risk of linear shrinkage** (3D.2) under `θ ∼ N(0, τ²)`: `p·((1−c)²τ² + c²σ²)`. The
minimized value `p·σ²τ²/(σ²+τ²)` is `StatLean.MultipleTesting.empiricalBayes_risk`. -/
theorem normalMeans_linearShrinkage_bayesRisk (c : ℝ) (p : ℕ) (τ2 σ2 : ℝ≥0) :
    (∫ θ, (∫ x, ∑ i, (linearShrinkage c x i - θ i) ^ 2
        ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      ∂(Measure.pi fun _ : Fin p => gaussianReal 0 τ2))
      = (p : ℝ) * ((1 - c) ^ 2 * (τ2 : ℝ) + c ^ 2 * (σ2 : ℝ)) := by
  have hsq : ∀ i : Fin p, Integrable (fun θ : Fin p → ℝ => (θ i) ^ 2)
      (Measure.pi fun _ : Fin p => gaussianReal 0 τ2) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin p => gaussianReal 0 τ2) (i := i)
      (f := fun y => y ^ 2) (gaussian_sq_integrable 0 τ2)
  calc (∫ θ, (∫ x, ∑ i, (linearShrinkage c x i - θ i) ^ 2
          ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
        ∂(Measure.pi fun _ : Fin p => gaussianReal 0 τ2))
      = ∫ θ, (∑ i, ((1 - c) ^ 2 * (θ i) ^ 2 + c ^ 2 * (σ2 : ℝ)))
          ∂(Measure.pi fun _ : Fin p => gaussianReal 0 τ2) := by
        apply integral_congr_ae; filter_upwards with θ
        exact linearShrinkage_risk_value c θ σ2
    _ = ∑ i, ∫ θ, ((1 - c) ^ 2 * (θ i) ^ 2 + c ^ 2 * (σ2 : ℝ))
          ∂(Measure.pi fun _ : Fin p => gaussianReal 0 τ2) := by
        rw [integral_finset_sum]
        intro i _
        exact ((hsq i).const_mul _).add (integrable_const _)
    _ = ∑ _i : Fin p, ((1 - c) ^ 2 * (τ2 : ℝ) + c ^ 2 * (σ2 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_add ((hsq i).const_mul _) (integrable_const _), integral_const_mul,
          integral_const,
          show (∫ θ, (θ i) ^ 2 ∂(Measure.pi fun _ : Fin p => gaussianReal 0 τ2))
              = ∫ y, y ^ 2 ∂(gaussianReal 0 τ2) from
            integral_comp_eval (μ := fun _ : Fin p => gaussianReal 0 τ2) (i := i)
              (f := fun y => y ^ 2) (gaussian_sq_integrable 0 τ2).aestronglyMeasurable,
          gaussian_sq_mean_zero]
        simp
    _ = (p : ℝ) * ((1 - c) ^ 2 * (τ2 : ℝ) + c ^ 2 * (σ2 : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The oracle weight minimizes the Bayes risk** (3D.2): `c* = τ²/(σ²+τ²)` is the argmin. -/
theorem normalMeans_linearShrinkage_bayesRisk_argmin (p : ℕ) (τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate variances; Robert §10.4.2
    (hσ : σ2 ≠ 0) (hτ : τ2 ≠ 0) (c : ℝ) :
    (p : ℝ) * ((1 - (τ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ))) ^ 2 * (τ2 : ℝ)
        + ((τ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ))) ^ 2 * (σ2 : ℝ))
      ≤ (p : ℝ) * ((1 - c) ^ 2 * (τ2 : ℝ) + c ^ 2 * (σ2 : ℝ)) := by
  have hτ0 : (0 : ℝ) < (τ2 : ℝ) := NNReal.coe_pos.mpr (zero_lt_iff.mpr hτ)
  have hd : (0 : ℝ) < (σ2 : ℝ) + (τ2 : ℝ) :=
    add_pos_of_nonneg_of_pos (NNReal.coe_nonneg σ2) hτ0
  have hne : (σ2 : ℝ) + (τ2 : ℝ) ≠ 0 := ne_of_gt hd
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg p)
  have hcstar : (1 - (τ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ))) ^ 2 * (τ2 : ℝ)
        + ((τ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ))) ^ 2 * (σ2 : ℝ)
      = (σ2 : ℝ) * (τ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ)) := by
    field_simp
    ring
  rw [hcstar, div_le_iff₀ hd]
  nlinarith [sq_nonneg (((σ2 : ℝ) + (τ2 : ℝ)) * c - (τ2 : ℝ))]

/-! ### James–Stein risk (3D.4): the Gaussian Stein's-lemma development -/

/-- Derivative of the one-coordinate slice `s ↦ s/(s²+c)` of the James–Stein vector field
`x ↦ xᵢ/‖x‖²` (with `c = ∑_{j≠i} xⱼ²` the fixed contribution of the other coordinates). -/
private lemma hasDerivAt_jsSlice (c t : ℝ) (h : t ^ 2 + c ≠ 0) :
    HasDerivAt (fun s => s / (s ^ 2 + c)) ((c - t ^ 2) / (t ^ 2 + c) ^ 2) t := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + c) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const c
  have h2 : HasDerivAt (fun s : ℝ => s / (s ^ 2 + c))
      ((1 * (t ^ 2 + c) - t * (2 * t)) / (t ^ 2 + c) ^ 2) t := (hasDerivAt_id t).div h1 h
  have heq : (1 * (t ^ 2 + c) - t * (2 * t)) / (t ^ 2 + c) ^ 2
      = (c - t ^ 2) / (t ^ 2 + c) ^ 2 := by
    rw [div_eq_div_iff (pow_ne_zero 2 h) (pow_ne_zero 2 h)]; ring
  rwa [heq] at h2

/-- The **divergence identity** `∑ᵢ (S − 2xᵢ²)/S² = (p−2)/S` with `S = ‖x‖²` — the pointwise
content of `∑ᵢ ∂ᵢ(xᵢ/‖x‖²) = (p−2)/‖x‖²`. Holds unconditionally (`ℝ`-division by `0` is `0`). -/
private lemma js_div_sum {p : ℕ} (x : Fin p → ℝ) :
    ∑ i, ((∑ j, (x j) ^ 2) - 2 * (x i) ^ 2) / (∑ j, (x j) ^ 2) ^ 2
      = ((p : ℝ) - 2) / (∑ j, (x j) ^ 2) := by
  set S : ℝ := ∑ j, (x j) ^ 2 with hSdef
  rcases eq_or_ne S 0 with hS | hS
  · simp [hS]
  · rw [← Finset.sum_div]
    have hnum : ∑ i, (S - 2 * (x i) ^ 2) = (p : ℝ) * S - 2 * S := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, ← hSdef]
    rw [hnum, div_eq_div_iff (pow_ne_zero 2 hS) hS]
    ring

/-- Integrability of `t ↦ h t · gaussianPDFReal m σ² t` for bounded `h` (bounded × integrable
density). -/
private lemma integrable_bdd_mul_gaussianPDFReal (m : ℝ) (σ2 : ℝ≥0) {h : ℝ → ℝ}
    (hm : Measurable h) {C : ℝ} (hC : ∀ t, |h t| ≤ C) :
    Integrable (fun t => h t * gaussianPDFReal m σ2 t) := by
  refine ((integrable_gaussianPDFReal m σ2).const_mul C).mono'
    (hm.aestronglyMeasurable.mul (measurable_gaussianPDFReal m σ2).aestronglyMeasurable) ?_
  refine ae_of_all _ fun t => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg m σ2 t)]
  exact mul_le_mul_of_nonneg_right (hC t) (gaussianPDFReal_nonneg m σ2 t)

/-- Integrability of the Gaussian score `t ↦ (m − t) · gaussianPDFReal m σ² t` (first-moment
integrability). -/
private lemma integrable_score_gaussianPDFReal (m : ℝ) (σ2 : ℝ≥0) (hσ : σ2 ≠ 0) :
    Integrable (fun t => (m - t) * gaussianPDFReal m σ2 t) := by
  have hid : Integrable (fun t => t * gaussianPDFReal m σ2 t) := by
    have h1 : Integrable (id : ℝ → ℝ) (gaussianReal m σ2) :=
      (memLp_id_gaussianReal 1).integrable (by norm_num)
    rw [gaussianReal_of_var_ne_zero m hσ, integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF m σ2) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h1
    simpa [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg m σ2 _), smul_eq_mul,
      mul_comm] using h1
  have : (fun t => (m - t) * gaussianPDFReal m σ2 t)
      = (fun t => m * gaussianPDFReal m σ2 t - t * gaussianPDFReal m σ2 t) := by
    funext t; ring
  rw [this]
  exact ((integrable_gaussianPDFReal m σ2).const_mul m).sub hid

/-- **One-dimensional Gaussian Stein identity**: `∫ (t−m)·h ∂N(m,σ²) = σ²·∫ h' ∂N(m,σ²)` for a
differentiable `h` with `h` and `h'` bounded. The integration-by-parts boundary terms vanish by
Gaussian decay; integrability is the bounded-times-density and score lemmas above. -/
private lemma gaussian_stein_1d (m : ℝ) (σ2 : ℝ≥0) (hσ : σ2 ≠ 0) {h h' : ℝ → ℝ}
    (hm : Measurable h) (hm' : Measurable h') (hd : ∀ t, HasDerivAt h (h' t) t)
    {C : ℝ} (hhC : ∀ t, |h t| ≤ C) (hh'C : ∀ t, |h' t| ≤ C) :
    ∫ t, (t - m) * h t ∂(gaussianReal m σ2) = (σ2 : ℝ) * ∫ t, h' t ∂(gaussianReal m σ2) := by
  set pdf := gaussianPDFReal m σ2 with hpdfdef
  have hderiv : ∀ t, HasDerivAt pdf ((m - t) / (σ2 : ℝ) * pdf t) t := fun t =>
    hasDerivAt_gaussianPDFReal m σ2 hσ t
  have huv : Integrable (fun t => h t * pdf t) := integrable_bdd_mul_gaussianPDFReal m σ2 hm hhC
  have hu'v : Integrable (fun t => h' t * pdf t) := integrable_bdd_mul_gaussianPDFReal m σ2 hm' hh'C
  have hscore : Integrable (fun t => (m - t) * pdf t) := integrable_score_gaussianPDFReal m σ2 hσ
  have huv' : Integrable (fun t => h t * ((m - t) / (σ2 : ℝ) * pdf t)) := by
    have hrw : (fun t => h t * ((m - t) / (σ2 : ℝ) * pdf t))
        = fun t => (σ2 : ℝ)⁻¹ * (h t * ((m - t) * pdf t)) := by
      funext t; ring
    rw [hrw]
    exact (hscore.bdd_mul hm.aestronglyMeasurable
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hhC t)).const_mul _
  have hibp : (∫ t, h t * ((m - t) / (σ2 : ℝ) * pdf t)) = -∫ t, h' t * pdf t := by
    have key := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
      (L := ContinuousLinearMap.mul ℝ ℝ) (u := h) (u' := h') (v := pdf)
      (v' := fun t => (m - t) / (σ2 : ℝ) * pdf t)
      (fun x _ => hd x) (fun x _ => hderiv x)
      (by simpa only [ContinuousLinearMap.mul_apply'] using huv')
      (by simpa only [ContinuousLinearMap.mul_apply'] using hu'v)
      (by simpa only [ContinuousLinearMap.mul_apply'] using huv)
    simpa only [ContinuousLinearMap.mul_apply'] using key
  rw [integral_gaussianReal_eq_integral_smul hσ, integral_gaussianReal_eq_integral_smul hσ]
  simp only [smul_eq_mul, ← hpdfdef]
  have hσ' : (σ2 : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hσ
  have hpt : (fun t => pdf t * ((t - m) * h t))
      = fun t => -(σ2 : ℝ) * (h t * ((m - t) / (σ2 : ℝ) * pdf t)) := by
    funext t; field_simp; ring
  rw [hpt, integral_const_mul, hibp, neg_mul_neg]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun t => mul_comm (h' t) (pdf t))

/-! ### Brick D: finiteness of `E‖X‖⁻²` for `p ≥ 3` -/

/-- **Radial ball integrability** of `x ↦ ‖x‖⁻²` on the closed unit ball for `p ≥ 3` (Lebesgue
measure on `Fin p → ℝ`). The whole-space radial integral of `‖x‖⁻²` diverges, but restricted to the
ball it is finite: transferring to `EuclideanSpace ℝ (Fin p)` and integrating radially reduces to
`∫₀¹ r^{p-3} dr`, finite precisely because `p ≥ 3`. -/
private lemma integrableOn_inv_normSq_ball {p : ℕ} (hp : 3 ≤ p) :
    IntegrableOn (fun x : Fin p → ℝ => 1 / (∑ i, (x i) ^ 2))
      {x : Fin p → ℝ | (∑ i, (x i) ^ 2) ≤ 1} volume := by
  classical
  set F : ℝ → ℝ := fun t => if t ≤ 1 then 1 / t ^ 2 else 0 with hF
  -- Euclidean-space integrability of `y ↦ ‖y‖⁻²` on the closed unit ball.
  have hball : IntegrableOn (fun y : EuclideanSpace ℝ (Fin p) => 1 / ‖y‖ ^ 2)
      (Metric.closedBall 0 1) volume := by
    rw [← integrable_indicator_iff measurableSet_closedBall]
    have hEq : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin p)) 1).indicator
        (fun y => 1 / ‖y‖ ^ 2) = fun y => F ‖y‖ := by
      funext y
      by_cases hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin p)) 1
      · rw [Set.indicator_of_mem hy]
        have hle : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
        simp [hF, hle]
      · rw [Set.indicator_of_notMem hy]
        have hlt : ¬ ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
        simp [hF, hlt]
    haveI : Nontrivial (EuclideanSpace ℝ (Fin p)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
    rw [hEq, integrable_fun_norm_addHaar, finrank_euclideanSpace_fin,
      ← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
    constructor
    · -- On `Ioc 0 1` the integrand equals the continuous monomial `t ↦ t^{p-3}`.
      have hcont : IntegrableOn (fun t : ℝ => t ^ (p - 3)) (Set.Ioc 0 1) volume :=
        (continuous_pow (p - 3)).integrableOn_Ioc
      refine hcont.congr_fun (fun t ht => ?_) measurableSet_Ioc
      have ht1 : t ≤ 1 := ht.2
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      simp only [hF, smul_eq_mul, if_pos ht1]
      rw [show p - 1 = (p - 3) + 2 by omega, pow_add]
      field_simp
    · -- On `Ioi 1` the integrand vanishes.
      refine (integrableOn_zero).congr_fun (fun t ht => ?_) measurableSet_Ioi
      have ht1 : ¬ t ≤ 1 := not_le.mpr ht
      simp [hF, ht1]
  -- Transfer back to `Fin p → ℝ` via the volume-preserving coordinate identification.
  have hmp : MeasurePreserving (⇑((MeasurableEquiv.toLp 2 ((Fin p) → ℝ)).symm))
      (volume : Measure (EuclideanSpace ℝ (Fin p))) (volume : Measure (Fin p → ℝ)) := by
    rw [MeasurableEquiv.coe_toLp_symm]; exact PiLp.volume_preserving_ofLp (Fin p)
  have hemb : MeasurableEmbedding (⇑((MeasurableEquiv.toLp 2 ((Fin p) → ℝ)).symm)) :=
    ((MeasurableEquiv.toLp 2 ((Fin p) → ℝ)).symm).measurableEmbedding
  rw [← hmp.integrableOn_comp_preimage hemb]
  have hfun : ((fun x : Fin p → ℝ => 1 / ∑ i, (x i) ^ 2)
        ∘ ⇑((MeasurableEquiv.toLp 2 ((Fin p) → ℝ)).symm))
      = fun y : EuclideanSpace ℝ (Fin p) => 1 / ‖y‖ ^ 2 := by
    funext y
    simp only [Function.comp_apply, MeasurableEquiv.coe_toLp_symm,
      EuclideanSpace.real_norm_sq_eq]
  have hset : (⇑((MeasurableEquiv.toLp 2 ((Fin p) → ℝ)).symm)
        ⁻¹' {x : Fin p → ℝ | ∑ i, (x i) ^ 2 ≤ 1})
      = Metric.closedBall 0 1 := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq, MeasurableEquiv.coe_toLp_symm,
      Metric.mem_closedBall, dist_eq_norm, sub_zero, ← EuclideanSpace.real_norm_sq_eq]
    constructor
    · intro h; nlinarith [norm_nonneg y, h]
    · intro h; nlinarith [norm_nonneg y, h]
  rw [hfun, hset]; exact hball

/-- The Gaussian pdf is bounded by its peak height `(√(2πσ²))⁻¹` (as `exp(·) ≤ 1`). -/
private lemma gaussianPDFReal_le_peak (m : ℝ) (σ2 : ℝ≥0) (t : ℝ) :
    gaussianPDFReal m σ2 t ≤ (Real.sqrt (2 * Real.pi * σ2))⁻¹ := by
  rw [gaussianPDFReal]
  refine mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (Real.exp_le_one_iff.mpr ?_)
  exact div_nonpos_iff.mpr (Or.inr ⟨neg_nonpos_of_nonneg (sq_nonneg _), by positivity⟩)

/-- **Brick D: `E‖X‖⁻² < ∞` for `p ≥ 3`.** Integrability of `x ↦ ‖x‖⁻²` against the product
Gaussian `N = ⨂ᵢ 𝒩(θᵢ, σ²)`. Split the space into the unit ball and its complement: on the tail
`‖x‖² ≥ 1` the integrand is `≤ 1` and `N` is a probability measure; on the ball the Gaussian
density is bounded by its peak `M`, reducing to the Lebesgue ball fact
`integrableOn_inv_normSq_ball`, finite precisely for `p ≥ 3`. -/
private lemma integrable_inv_normSq_pi {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ) (σ2 : ℝ≥0)
    (hσ : σ2 ≠ 0) :
    Integrable (fun x : Fin p → ℝ => 1 / (∑ i, (x i) ^ 2))
      (Measure.pi fun i => gaussianReal (θ i) σ2) := by
  classical
  set N := Measure.pi fun i => gaussianReal (θ i) σ2 with hN
  haveI : IsProbabilityMeasure N := by rw [hN]; infer_instance
  set S : (Fin p → ℝ) → ℝ := fun x => ∑ i, (x i) ^ 2 with hS
  have hSmeas : Measurable S := by
    apply Finset.measurable_sum; intro i _; exact (measurable_pi_apply i).pow_const 2
  have hSnonneg : ∀ x, 0 ≤ S x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  -- `N` as `withDensity` of the product density against Lebesgue measure.
  haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF (θ i) σ2)) := by
    intro i; rw [← gaussianReal_of_var_ne_zero (θ i) hσ]; infer_instance
  have hNwd : N = (volume : Measure (Fin p → ℝ)).withDensity
      (fun x => ∏ i, gaussianPDF (θ i) σ2 (x i)) := by
    rw [hN, show (fun i => gaussianReal (θ i) σ2)
        = fun i => (volume : Measure ℝ).withDensity (gaussianPDF (θ i) σ2) from
      funext fun i => gaussianReal_of_var_ne_zero (θ i) hσ,
      pi_withDensity (μ := (volume : Measure ℝ)) (f := fun i => gaussianPDF (θ i) σ2)
        (fun i => measurable_gaussianPDF (θ i) σ2)]
    congr 1
  -- Peak bound on the product density.
  set M : ℝ := ((Real.sqrt (2 * Real.pi * σ2))⁻¹) ^ p with hM
  have hMnonneg : 0 ≤ M := by rw [hM]; positivity
  have hρle : ∀ x : Fin p → ℝ, (∏ i, gaussianPDF (θ i) σ2 (x i)).toReal ≤ M := by
    intro x
    rw [ENNReal.toReal_prod]
    have hfac : ∀ i, (gaussianPDF (θ i) σ2 (x i)).toReal = gaussianPDFReal (θ i) σ2 (x i) := by
      intro i; rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
    calc ∏ i, (gaussianPDF (θ i) σ2 (x i)).toReal
        = ∏ i, gaussianPDFReal (θ i) σ2 (x i) := Finset.prod_congr rfl fun i _ => hfac i
      _ ≤ ∏ _i : Fin p, (Real.sqrt (2 * Real.pi * σ2))⁻¹ :=
          Finset.prod_le_prod (fun i _ => gaussianPDFReal_nonneg _ _ _)
            (fun i _ => gaussianPDFReal_le_peak _ _ _)
      _ = M := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hM]
  -- Split `univ` into ball and tail.
  have huniv : (Set.univ : Set (Fin p → ℝ)) = {x | S x ≤ 1} ∪ {x | 1 ≤ S x} := by
    ext x; simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]
    exact le_total (S x) 1
  rw [← integrableOn_univ, huniv, integrableOn_union]
  refine ⟨?_, ?_⟩
  · -- Ball: dominate by `M · ‖x‖⁻²`, use the Lebesgue ball fact.
    have hmset0 : MeasurableSet {x : Fin p → ℝ | S x ≤ 1} :=
      measurableSet_le hSmeas measurable_const
    have hρmeas : Measurable (fun x : Fin p → ℝ => ∏ i, gaussianPDF (θ i) σ2 (x i)) :=
      Finset.measurable_prod _ fun i _ =>
        (measurable_gaussianPDF (θ i) σ2).comp (measurable_pi_apply i)
    have hballvol : IntegrableOn (fun x : Fin p → ℝ => M * (1 / S x)) {x | S x ≤ 1} volume :=
      (integrableOn_inv_normSq_ball hp).const_mul M
    rw [IntegrableOn, hNwd, restrict_withDensity hmset0,
      integrable_withDensity_iff_integrable_smul' hρmeas
        (ae_of_all _ fun x => ENNReal.prod_lt_top fun i _ => gaussianPDF_ne_top.lt_top)]
    refine hballvol.mono' ?_ ?_
    · exact (hρmeas.ennreal_toReal.mul (measurable_const.div hSmeas)).aestronglyMeasurable
    · refine ae_of_all _ fun x => ?_
      rw [Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg]
      · refine mul_le_mul_of_nonneg_right (hρle x) ?_
        positivity
      · exact mul_nonneg ENNReal.toReal_nonneg (by positivity)
  · -- Tail: `‖x‖⁻² ≤ 1`.
    have hmset1 : MeasurableSet {x : Fin p → ℝ | 1 ≤ S x} :=
      measurableSet_le measurable_const hSmeas
    refine (Integrable.mono' (g := fun _ => (1 : ℝ))
      (integrableOn_const (μ := N) (s := {x | 1 ≤ S x}) (measure_ne_top N _))
      (measurable_const.div hSmeas).aestronglyMeasurable ?_)
    rw [ae_restrict_iff' hmset1]
    refine ae_of_all _ fun x hx => ?_
    have hSpos : 0 < S x := lt_of_lt_of_le one_pos hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_le_one hSpos]; exact hx

/-! ### Brick B support: integrability of the cross-term integrands -/

/-- Each squared coordinate is dominated by the squared norm. -/
private lemma coord_sq_le_sum {p : ℕ} (x : Fin p → ℝ) (i : Fin p) :
    (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
  Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

/-- Triangle inequality in the form `|a − b| ≤ |a| + |b|`. -/
private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  cases abs_cases (a - b) with
  | inl h => rw [h.1]; nlinarith [le_abs_self a, neg_abs_le b]
  | inr h => rw [h.1]; nlinarith [neg_abs_le a, le_abs_self b]

/-- **Integrability of the cross-term integrand** `(xᵢ − θᵢ)·xᵢ/‖x‖²`, dominated pointwise by
`3/2 + (θᵢ²/2)·‖x‖⁻²` (Brick D gives the second summand). -/
private lemma integrable_jsG {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ) (σ2 : ℝ≥0) (hσ : σ2 ≠ 0)
    (i : Fin p) :
    Integrable (fun x : Fin p → ℝ => (x i - θ i) * (x i / ∑ j, (x j) ^ 2))
      (Measure.pi fun j => gaussianReal (θ j) σ2) := by
  set N := Measure.pi fun j => gaussianReal (θ j) σ2 with hN
  haveI : IsProbabilityMeasure N := by rw [hN]; infer_instance
  set S : (Fin p → ℝ) → ℝ := fun x => ∑ j, (x j) ^ 2 with hS
  have hSnn : ∀ x, 0 ≤ S x := fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hSmeas : Measurable S :=
    Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).pow_const 2
  have hg : Integrable (fun x => 3 / 2 + (θ i) ^ 2 / 2 * (1 / S x)) N :=
    (integrable_const _).add ((integrable_inv_normSq_pi hp θ σ2 hσ).const_mul _)
  refine hg.mono' (((measurable_pi_apply i).sub measurable_const).mul
      ((measurable_pi_apply i).div hSmeas)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rcases eq_or_lt_of_le (hSnn x) with h0 | hpos
  · have hz : x i / S x = 0 := by rw [← h0]; exact div_zero _
    have hnn : (0 : ℝ) ≤ (θ i) ^ 2 / 2 * (1 / S x) := by rw [← h0]; simp
    rw [hz, mul_zero, Real.norm_eq_abs, abs_zero]; linarith
  · have hSne : S x ≠ 0 := ne_of_gt hpos
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hpos, ← mul_div_assoc, div_le_iff₀ hpos,
      show (3 / 2 + (θ i) ^ 2 / 2 * (1 / S x)) * S x = 3 / 2 * S x + (θ i) ^ 2 / 2 by
        field_simp]
    nlinarith [mul_le_mul_of_nonneg_right (abs_sub_le_abs_add (x i) (θ i)) (abs_nonneg (x i)),
      sq_abs (x i), sq_abs (θ i), sq_nonneg (|x i| - |θ i|), coord_sq_le_sum x i,
      abs_nonneg (x i), abs_nonneg (θ i)]

/-- **Integrability of the divergence integrand** `(‖x‖² − 2xᵢ²)/‖x‖⁴`, dominated pointwise by
`3·‖x‖⁻²` (Brick D). -/
private lemma integrable_jsR {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ) (σ2 : ℝ≥0) (hσ : σ2 ≠ 0)
    (i : Fin p) :
    Integrable (fun x : Fin p → ℝ => ((∑ j, (x j) ^ 2) - 2 * (x i) ^ 2) / (∑ j, (x j) ^ 2) ^ 2)
      (Measure.pi fun j => gaussianReal (θ j) σ2) := by
  set N := Measure.pi fun j => gaussianReal (θ j) σ2 with hN
  haveI : IsProbabilityMeasure N := by rw [hN]; infer_instance
  set S : (Fin p → ℝ) → ℝ := fun x => ∑ j, (x j) ^ 2 with hS
  have hSnn : ∀ x, 0 ≤ S x := fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hSmeas : Measurable S :=
    Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).pow_const 2
  have hg : Integrable (fun x => 3 * (1 / S x)) N :=
    (integrable_inv_normSq_pi hp θ σ2 hσ).const_mul _
  refine hg.mono' ((hSmeas.sub (((measurable_pi_apply i).pow_const 2).const_mul 2)).div
      (hSmeas.pow_const 2)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rcases eq_or_lt_of_le (hSnn x) with h0 | hpos
  · have hz : (S x - 2 * (x i) ^ 2) / (S x) ^ 2 = 0 := by rw [← h0]; simp
    have hr : (3 : ℝ) * (1 / S x) = 0 := by rw [← h0]; simp
    rw [hz, hr]; simp
  · have hSne : S x ≠ 0 := ne_of_gt hpos
    have hS2 : (0 : ℝ) < (S x) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hS2, div_le_iff₀ hS2,
      show 3 * (1 / S x) * (S x) ^ 2 = 3 * S x by field_simp, abs_le]
    constructor <;> nlinarith [coord_sq_le_sum x i, sq_nonneg (x i), hpos.le]

/-! ### Brick B: the cross term via coordinate Fubini and the 1D Stein identity -/

/-- **Cross-term identity** (Brick B): for each coordinate `i`,
`∫ (xᵢ − θᵢ)·xᵢ/‖x‖² ∂N = σ²·∫ (‖x‖² − 2xᵢ²)/‖x‖⁴ ∂N`. Isolating coordinate `i` by the measure-
preserving `piFinSuccAbove` equivalence turns each side into an iterated integral; for a.e. choice
of the other coordinates `b` (whose squared norm `c := ∑_{j≠i} bⱼ² > 0`), the inner `xᵢ`-integral is
the
one-dimensional Gaussian Stein identity `gaussian_stein_1d` applied to `s ↦ s/(s²+c)`. -/
private lemma jamesStein_crossTerm {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ)
    (σ2 : ℝ≥0) (hσ : σ2 ≠ 0) (i : Fin p) :
    (∫ x, (x i - θ i) * (x i / ∑ j, (x j) ^ 2) ∂(Measure.pi fun j => gaussianReal (θ j) σ2))
      = (σ2 : ℝ) * ∫ x, ((∑ j, (x j) ^ 2) - 2 * (x i) ^ 2) / (∑ j, (x j) ^ 2) ^ 2
          ∂(Measure.pi fun j => gaussianReal (θ j) σ2) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have hp3 : 3 ≤ n + 1 := hp
  set μ : Fin (n + 1) → Measure ℝ := fun j => gaussianReal (θ j) σ2 with hμ
  haveI : ∀ j, IsProbabilityMeasure (μ j) := fun j => by rw [hμ]; infer_instance
  set e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
  have mp : MeasurePreserving e (Measure.pi μ)
      ((μ i).prod (Measure.pi fun j => μ (i.succAbove j))) :=
    measurePreserving_piFinSuccAbove μ i
  set νr : Measure (Fin n → ℝ) := Measure.pi fun j => μ (i.succAbove j) with hνr
  haveI : IsProbabilityMeasure νr := by rw [hνr]; infer_instance
  have mps : MeasurePreserving e.symm ((μ i).prod νr) (Measure.pi μ) :=
    MeasurePreserving.symm e mp
  -- coordinate identities for `e.symm (a, b) = insertNth i a b`
  have hes : ∀ (a : ℝ) (b : Fin n → ℝ),
      e.symm (a, b) = Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i a b := fun _ _ => rfl
  have hsame : ∀ (a : ℝ) (b : Fin n → ℝ),
      (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i a b) i = a :=
    fun a b => Fin.insertNth_apply_same (α := fun _ => ℝ) i a b
  have hsum : ∀ (a : ℝ) (b : Fin n → ℝ),
      ∑ j, ((Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i a b) j) ^ 2
        = a ^ 2 + ∑ j, (b j) ^ 2 := by
    intro a b
    rw [Fin.sum_univ_succAbove
        (fun k => ((Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i a b) k) ^ 2) i, hsame]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.insertNth_apply_succAbove (α := fun _ => ℝ)]
  -- a.e. positivity of `c = ∑_{j≠i} bⱼ²` under the product Gaussian on the frozen coordinates
  have hn1 : 0 < n := by omega
  have hkpos : ∀ᵐ b ∂νr, (0 : ℝ) < ∑ j, (b j) ^ 2 := by
    set k : Fin n := ⟨0, hn1⟩ with hk
    haveI : NullSingletonClass (μ (i.succAbove k)) := nullSingletonClass_gaussianReal hσ
    have hmpk : MeasurePreserving (Function.eval k) νr (μ (i.succAbove k)) := by
      rw [hνr]; exact measurePreserving_eval (μ := fun j => μ (i.succAbove j)) k
    have hatom : ∀ᵐ y ∂(μ (i.succAbove k)), y ≠ 0 := by
      simpa only [ae_iff, not_ne_iff, Set.setOf_eq_eq_singleton] using
        measure_singleton (μ := μ (i.succAbove k)) 0
    have hbk : ∀ᵐ b ∂νr, (b k) ≠ 0 :=
      ae_of_ae_map hmpk.measurable.aemeasurable (hmpk.map_eq ▸ hatom)
    filter_upwards [hbk] with b hb
    have hpos : 0 < (b k) ^ 2 := by positivity
    exact lt_of_lt_of_le hpos (coord_sq_le_sum b k)
  -- transfer both integrals through the equivalence and Fubini
  have hGint : Integrable (fun x => (x i - θ i) * (x i / ∑ j, (x j) ^ 2)) (Measure.pi μ) := by
    rw [hμ]; exact integrable_jsG hp3 θ σ2 hσ i
  have hRint : Integrable (fun x => ((∑ j, (x j) ^ 2) - 2 * (x i) ^ 2) / (∑ j, (x j) ^ 2) ^ 2)
      (Measure.pi μ) := by rw [hμ]; exact integrable_jsR hp3 θ σ2 hσ i
  have hGint2 : Integrable (fun z => (e.symm z i - θ i) * (e.symm z i / ∑ j, (e.symm z j) ^ 2))
      ((μ i).prod νr) :=
    (mps.integrable_comp_emb e.symm.measurableEmbedding).mpr hGint
  have hRint2 : Integrable (fun z => ((∑ j, (e.symm z j) ^ 2) - 2 * (e.symm z i) ^ 2)
      / (∑ j, (e.symm z j) ^ 2) ^ 2) ((μ i).prod νr) :=
    (mps.integrable_comp_emb e.symm.measurableEmbedding).mpr hRint
  rw [← mps.integral_comp' (fun x => (x i - θ i) * (x i / ∑ j, (x j) ^ 2)),
      ← mps.integral_comp' (fun x => ((∑ j, (x j) ^ 2) - 2 * (x i) ^ 2) / (∑ j, (x j) ^ 2) ^ 2),
      integral_prod_symm _ hGint2, integral_prod_symm _ hRint2, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hkpos] with b hcb
  set c : ℝ := ∑ j, (b j) ^ 2 with hc
  have hμi : μ i = gaussianReal (θ i) σ2 := rfl
  have hGeq :
      (fun a : ℝ => (e.symm (a, b) i - θ i) * (e.symm (a, b) i / ∑ j, (e.symm (a, b) j) ^ 2))
      = fun a : ℝ => (a - θ i) * (a / (a ^ 2 + c)) := by
    funext a; rw [hes a b, hsame a b, hsum a b]
  have hReq : (fun a : ℝ => ((∑ j, (e.symm (a, b) j) ^ 2) - 2 * (e.symm (a, b) i) ^ 2)
        / (∑ j, (e.symm (a, b) j) ^ 2) ^ 2)
      = fun a : ℝ => (c - a ^ 2) / (a ^ 2 + c) ^ 2 := by
    funext a; rw [hes a b, hsame a b, hsum a b]; ring
  rw [hGeq, hReq, hμi]
  -- inner Stein identity
  have hbound_h : ∀ a : ℝ, |a / (a ^ 2 + c)| ≤ 1 / (2 * Real.sqrt c) := by
    intro a
    rw [abs_div, abs_of_pos (show (0 : ℝ) < a ^ 2 + c by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (|a| - Real.sqrt c), Real.sq_sqrt hcb.le, sq_abs a,
      Real.sqrt_nonneg c, abs_nonneg a]
  have hbound_h' : ∀ a : ℝ, |(c - a ^ 2) / (a ^ 2 + c) ^ 2| ≤ 1 / c := by
    intro a
    rw [abs_div, abs_of_pos (show (0 : ℝ) < (a ^ 2 + c) ^ 2 by positivity),
      div_le_div_iff₀ (by positivity) hcb]
    have h1 : |c - a ^ 2| ≤ a ^ 2 + c := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg a, hcb.le]
    nlinarith [h1, sq_nonneg a, hcb.le, mul_nonneg (abs_nonneg (c - a ^ 2)) hcb.le,
      mul_le_mul h1 (show c ≤ a ^ 2 + c by nlinarith [sq_nonneg a]) hcb.le
        (by positivity : (0 : ℝ) ≤ a ^ 2 + c)]
  have hd : ∀ t : ℝ, HasDerivAt (fun s => s / (s ^ 2 + c)) ((c - t ^ 2) / (t ^ 2 + c) ^ 2) t :=
    fun t => hasDerivAt_jsSlice c t (show (0 : ℝ) < t ^ 2 + c by positivity).ne'
  exact gaussian_stein_1d (θ i) σ2 hσ (C := 1 / (2 * Real.sqrt c) + 1 / c)
    (by fun_prop) (by fun_prop) hd
    (fun t => (hbound_h t).trans (le_add_of_nonneg_right (by positivity)))
    (fun t => (hbound_h' t).trans (le_add_of_nonneg_left (by positivity)))

theorem jamesStein_risk_difference {p : ℕ}
    -- USER-INPUT: the Stein effect requires dimension ≥ 3; James–Stein 1961
    (hp : 3 ≤ p) (θ : Fin p → ℝ) (σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate noise variance; Robert Note 2.8.2
    (hσ : σ2 ≠ 0) :
    (∫ x, ∑ i, (jamesSteinEstimator (σ2 : ℝ) x i - θ i) ^ 2
        ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      = (p : ℝ) * (σ2 : ℝ) - ((p : ℝ) - 2) ^ 2 * (σ2 : ℝ) ^ 2
          * (∫ x, 1 / (∑ i, (x i) ^ 2) ∂(Measure.pi fun i => gaussianReal (θ i) σ2)) := by
  classical
  -- Expanding the loss pointwise:
  --   ∑ᵢ(δ_JS,ᵢ − θᵢ)² = ∑ᵢ(Xᵢ − θᵢ)² − 2k·∑ᵢ(Xᵢ − θᵢ)Xᵢ/‖X‖² + k²·‖X‖⁻²,  k = (p−2)σ².
  -- Integrate termwise; the cross term uses `jamesStein_crossTerm` and the divergence identity
  -- `js_div_sum`, the last term uses Brick D `integrable_inv_normSq_pi`.
  set M := Measure.pi fun i => gaussianReal (θ i) σ2 with hM
  haveI : IsProbabilityMeasure M := by rw [hM]; infer_instance
  -- integrability of the coordinate second moments
  have term1 : ∀ i, Integrable (fun x : Fin p → ℝ => (x i - θ i) ^ 2) M := by
    intro i
    have hgi : Integrable (fun y : ℝ => (y - θ i) ^ 2) (gaussianReal (θ i) σ2) := by
      have h2 : MemLp (fun y => y - θ i) 2 (gaussianReal (θ i) σ2) :=
        (memLp_id_gaussianReal 2).sub (memLp_const _)
      simpa using h2.integrable_sq
    rw [hM]
    exact integrable_comp_eval (μ := fun i => gaussianReal (θ i) σ2) (i := i)
      (f := fun y => (y - θ i) ^ 2) hgi
  have hDint : Integrable (fun x : Fin p → ℝ => 1 / ∑ j, (x j) ^ 2) M := by
    rw [hM]; exact integrable_inv_normSq_pi hp θ σ2 hσ
  have hGi : ∀ i, Integrable (fun x : Fin p → ℝ => (x i - θ i) * (x i / ∑ j, (x j) ^ 2)) M :=
    fun i => by rw [hM]; exact integrable_jsG hp θ σ2 hσ i
  have hf1 : Integrable (fun x : Fin p → ℝ => ∑ i, (x i - θ i) ^ 2) M :=
    integrable_finset_sum _ fun i _ => term1 i
  have hf2 : Integrable (fun x : Fin p → ℝ => ∑ i, (x i - θ i) * (x i / ∑ j, (x j) ^ 2)) M :=
    integrable_finset_sum _ fun i _ => hGi i
  -- pointwise expansion of the loss
  have hexpand : ∀ x : Fin p → ℝ, ∑ i, (jamesSteinEstimator (σ2 : ℝ) x i - θ i) ^ 2
      = (∑ i, (x i - θ i) ^ 2)
        - 2 * (((p : ℝ) - 2) * σ2) * (∑ i, (x i - θ i) * (x i / ∑ j, (x j) ^ 2))
        + (((p : ℝ) - 2) * σ2) ^ 2 * (1 / ∑ j, (x j) ^ 2) := by
    intro x
    have hV : ∑ i, (x i / ∑ j, (x j) ^ 2) ^ 2 = 1 / ∑ j, (x j) ^ 2 := by
      rcases eq_or_ne (∑ j, (x j) ^ 2) 0 with h0 | hne
      · simp [h0]
      · rw [Finset.sum_congr rfl fun i _ => (div_pow (x i) (∑ j, (x j) ^ 2) 2), ← Finset.sum_div,
          div_eq_div_iff (pow_ne_zero 2 hne) hne]
        ring
    have hpt : ∀ i, (jamesSteinEstimator (σ2 : ℝ) x i - θ i) ^ 2
        = (x i - θ i) ^ 2
          - 2 * (((p : ℝ) - 2) * σ2) * ((x i - θ i) * (x i / ∑ j, (x j) ^ 2))
          + (((p : ℝ) - 2) * σ2) ^ 2 * (x i / ∑ j, (x j) ^ 2) ^ 2 := by
      intro i
      simp only [jamesSteinEstimator]
      rcases eq_or_ne (∑ j, (x j) ^ 2) 0 with h0 | hne
      · rw [h0]; simp
      · field_simp; ring
    rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hV]
  -- value of the first term: `∑ᵢ σ² = pσ²`
  have hI1 : ∫ x, (∑ i, (x i - θ i) ^ 2) ∂M = (p : ℝ) * (σ2 : ℝ) := by
    rw [integral_finset_sum _ fun i _ => term1 i]
    have : (∑ i, ∫ x, (x i - θ i) ^ 2 ∂M) = ∑ _i : Fin p, (σ2 : ℝ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hM, integral_comp_eval (μ := fun i => gaussianReal (θ i) σ2) (i := i)
        (f := fun y => (y - θ i) ^ 2)
        (by have h2 : MemLp (fun y => y - θ i) 2 (gaussianReal (θ i) σ2) :=
              (memLp_id_gaussianReal 2).sub (memLp_const _)
            simpa using h2.integrable_sq.aestronglyMeasurable)]
      exact gaussian_centred_sq (θ i) σ2
    rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- cross-term identity and divergence-integrand integrability, stated over `M`
  have crossM : ∀ i, ∫ x, (x i - θ i) * (x i / ∑ j, (x j) ^ 2) ∂M
      = (σ2 : ℝ) * ∫ x, ((∑ j, (x j) ^ 2) - 2 * (x i) ^ 2) / (∑ j, (x j) ^ 2) ^ 2 ∂M :=
    fun i => by rw [hM]; exact jamesStein_crossTerm hp θ σ2 hσ i
  have jsRM : ∀ i, Integrable
      (fun x : Fin p → ℝ => ((∑ j, (x j) ^ 2) - 2 * (x i) ^ 2) / (∑ j, (x j) ^ 2) ^ 2) M :=
    fun i => by rw [hM]; exact integrable_jsR hp θ σ2 hσ i
  -- value of the cross term: `σ²(p−2)·E‖X‖⁻²`
  have hI2 : ∫ x, (∑ i, (x i - θ i) * (x i / ∑ j, (x j) ^ 2)) ∂M
      = (σ2 : ℝ) * ((p : ℝ) - 2) * ∫ x, 1 / ∑ j, (x j) ^ 2 ∂M := by
    rw [integral_finset_sum _ fun i _ => hGi i, Finset.sum_congr rfl fun i _ => crossM i,
      ← Finset.mul_sum, ← integral_finset_sum _ fun i _ => jsRM i,
      integral_congr_ae (ae_of_all _ fun x => js_div_sum x),
      show (fun x : Fin p → ℝ => ((p : ℝ) - 2) / ∑ j, (x j) ^ 2)
          = fun x => ((p : ℝ) - 2) * (1 / ∑ j, (x j) ^ 2) from by funext x; rw [mul_one_div],
      integral_const_mul]
    ring
  -- assemble by linearity
  have hfa : Integrable (fun x : Fin p → ℝ => (∑ i, (x i - θ i) ^ 2)
      - 2 * (((p : ℝ) - 2) * σ2) * (∑ i, (x i - θ i) * (x i / ∑ j, (x j) ^ 2))) M :=
    hf1.sub (hf2.const_mul _)
  have hfb : Integrable
      (fun x : Fin p → ℝ => (((p : ℝ) - 2) * σ2) ^ 2 * (1 / ∑ j, (x j) ^ 2)) M :=
    hDint.const_mul _
  rw [integral_congr_ae (ae_of_all _ hexpand), integral_add hfa hfb,
    integral_sub hf1 (hf2.const_mul _), integral_const_mul, integral_const_mul, hI1, hI2]
  ring

/-- **James–Stein dominates the MLE** (3D.4, stretch): in dimension `p ≥ 3` the James–Stein risk is
strictly below the MLE risk `p·σ²` for every `θ` (the Stein effect). -/
theorem jamesStein_dominates_mle {p : ℕ}
    -- USER-INPUT: the Stein effect requires dimension ≥ 3; James–Stein 1961
    (hp : 3 ≤ p) (θ : Fin p → ℝ) (σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate noise variance; Robert Note 2.8.2
    (hσ : σ2 ≠ 0) :
    (∫ x, ∑ i, (jamesSteinEstimator (σ2 : ℝ) x i - θ i) ^ 2
        ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      < (p : ℝ) * (σ2 : ℝ) := by
  classical
  -- The risk identity plus strict positivity of the subtracted term `(p−2)²σ⁴·E‖X‖⁻²`.
  rw [jamesStein_risk_difference hp θ σ2 hσ]
  set M := Measure.pi fun i => gaussianReal (θ i) σ2 with hM
  haveI : IsProbabilityMeasure M := by rw [hM]; infer_instance
  have hnn_fn : (0 : (Fin p → ℝ) → ℝ) ≤ fun x => 1 / ∑ i, (x i) ^ 2 :=
    fun x => one_div_nonneg.mpr (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hDint : Integrable (fun x : Fin p → ℝ => 1 / ∑ i, (x i) ^ 2) M := by
    rw [hM]; exact integrable_inv_normSq_pi hp θ σ2 hσ
  -- `‖x‖² > 0` for a.e. `x` (the zero point is null under the atomless product Gaussian)
  have hae : ∀ᵐ x ∂M, (0 : ℝ) < ∑ i, (x i) ^ 2 := by
    have h0lt : 0 < p := by omega
    set k : Fin p := ⟨0, h0lt⟩ with hk
    haveI : NullSingletonClass (gaussianReal (θ k) σ2) := nullSingletonClass_gaussianReal hσ
    have hmpk : MeasurePreserving (Function.eval k) M (gaussianReal (θ k) σ2) := by
      rw [hM]; exact measurePreserving_eval (μ := fun i => gaussianReal (θ i) σ2) k
    have hatom : ∀ᵐ y ∂(gaussianReal (θ k) σ2), y ≠ 0 := by
      simpa only [ae_iff, not_ne_iff, Set.setOf_eq_eq_singleton] using
        measure_singleton (μ := gaussianReal (θ k) σ2) 0
    filter_upwards [ae_of_ae_map hmpk.measurable.aemeasurable (hmpk.map_eq ▸ hatom)] with x hx
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < (x k) ^ 2) (coord_sq_le_sum x k)
  -- `E‖X‖⁻² > 0`
  have hEpos : 0 < ∫ x, 1 / ∑ i, (x i) ^ 2 ∂M := by
    rcases (integral_nonneg hnn_fn).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz := (integral_eq_zero_iff_of_nonneg hnn_fn hDint).mp h.symm
      have hbad : ∀ᵐ x ∂M, False := by
        filter_upwards [hz, hae] with x hx0 hxpos
        rw [Pi.zero_apply, one_div, inv_eq_zero] at hx0
        linarith
      rw [ae_iff] at hbad
      simp only [not_false_iff, Set.setOf_true, measure_univ] at hbad
      exact one_ne_zero hbad
  have hcoef : 0 < ((p : ℝ) - 2) ^ 2 * (σ2 : ℝ) ^ 2 := by
    have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      linarith
    have hσ2 : (0 : ℝ) < (σ2 : ℝ) := by rw [NNReal.coe_pos]; exact zero_lt_iff.mpr hσ
    positivity
  linarith [mul_pos hcoef hEpos]

end StatLean.Bayesian

