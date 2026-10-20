module
public import StatLean.AsymptoticStatistics.DQM.Properties
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ZEstimatorNormality
public import StatLean.AsymptoticStatistics.ForMathlib.PosDefCoercivity
public import StatLean.AsymptoticStatistics.ParametricFamily.FisherInformation
public import StatLean.AsymptoticStatistics.ParametricFamily.Score

@[expose] public section

/-!
# DQM score and Fisher-information adapters for maximum likelihood

For a finite-dimensional DQM model at `θ₀`, the true law is

`P₀ = μ.withDensity (ENNReal.ofReal ∘ M.density θ₀)`.

This file aligns the DQM score `ℓ` with the `psiVec`/`psiCov` interface used by
M-estimator asymptotic normality.  It also packages the matrix consequences of
positive-definite Fisher information for the canonical curvature `V = -I`.
No sigma-finiteness, pointwise log derivative, strict positivity, or provider
compatibility equality is used.
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace AsymptoticStatistics

open EmpiricalProcess

/-- The finite-dimensional Fisher information matrix in the standard
Euclidean basis.  Under DQM its entries are genuine finite second moments.
Without the later DQM integrability theorem, Lean's Bochner-integral convention
still gives a total matrix-valued definition. -/
noncomputable def fisherInformationMatrix
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))) (μ : Measure Ω)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (ℓ : Ω → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => fisherInformation M μ θ₀ ℓ
    (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single j (1 : ℝ))

/-- The quadratic Fisher-information form agrees with the Euclidean inner
product against the standard-basis Fisher matrix.  The integrability premise
is an internal DQM consequence in the 5.39 assembly, not a headline input. -/
lemma fisherInformation_eq_inner_fisherInformationMatrix
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))) (μ : Measure Ω)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (ℓ : Ω → EuclideanSpace ℝ (Fin d))
    -- Supplied by differentiability in quadratic mean.
    (hFisher : ∀ u : EuclideanSpace ℝ (Fin d),
      Integrable (fun x => ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) μ)
    (h : EuclideanSpace ℝ (Fin d)) :
    fisherInformation M μ θ₀ ℓ h h =
      ⟪h, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
        (fisherInformationMatrix M μ θ₀ ℓ) h⟫ := by
  let e : Fin d → EuclideanSpace ℝ (Fin d) :=
    fun i => EuclideanSpace.single i (1 : ℝ)
  have hcross (u v : EuclideanSpace ℝ (Fin d)) :
      Integrable (fun x => (⟪u, ℓ x⟫ * ⟪v, ℓ x⟫) * M.density θ₀ x) μ := by
    have hpol := (hFisher (u + v)).sub ((hFisher u).add (hFisher v))
    have hhalf := hpol.const_mul ((2 : ℝ)⁻¹)
    apply hhalf.congr
    filter_upwards with x
    simp only [Pi.sub_apply, Pi.add_apply, inner_add_left]
    ring
  have heval (i : Fin d) (x : Ω) : ⟪e i, ℓ x⟫ = (ℓ x).ofLp i := by
    simpa [e] using EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ) (ℓ x)
  have hinner (x : Ω) :
      ⟪h, ℓ x⟫ = ∑ i, h.ofLp i * ⟪e i, ℓ x⟫ := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [heval]
    change (ℓ x).ofLp i * h.ofLp i = h.ofLp i * (ℓ x).ofLp i
    ring
  have hterm (i j : Fin d) :
      Integrable (fun x => (h.ofLp i * h.ofLp j) *
        ((⟪e i, ℓ x⟫ * ⟪e j, ℓ x⟫) * M.density θ₀ x)) μ :=
    (hcross (e i) (e j)).const_mul (h.ofLp i * h.ofLp j)
  rw [fisherInformation, Matrix.inner_toEuclideanCLM]
  simp only [fisherInformationMatrix, dotProduct, Matrix.mulVec]
  calc
    ∫ x, ⟪h, ℓ x⟫ * ⟪h, ℓ x⟫ * M.density θ₀ x ∂μ =
        ∫ x, ∑ i, ∑ j, (h.ofLp i * h.ofLp j) *
          ((⟪e i, ℓ x⟫ * ⟪e j, ℓ x⟫) * M.density θ₀ x) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hinner, Fintype.sum_mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [heval, heval]
      ring
    _ = ∑ i, ∫ x, ∑ j, (h.ofLp i * h.ofLp j) *
          ((⟪e i, ℓ x⟫ * ⟪e j, ℓ x⟫) * M.density θ₀ x) ∂μ := by
      apply integral_finset_sum
      intro i _
      apply integrable_finset_sum
      intro j _
      exact hterm i j
    _ = ∑ i, ∑ j, ∫ x, (h.ofLp i * h.ofLp j) *
          ((⟪e i, ℓ x⟫ * ⟪e j, ℓ x⟫) * M.density θ₀ x) ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_finset_sum
      intro j _
      exact hterm i j
    _ = ∑ i, h.ofLp i * ∑ j,
          (∫ x, (⟪e i, ℓ x⟫ * ⟪e j, ℓ x⟫) * M.density θ₀ x ∂μ) * h.ofLp j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
      ring
    _ = ∑ i, h.ofLp i * ∑ j,
          fisherInformation M μ θ₀ ℓ (EuclideanSpace.single i 1)
            (EuclideanSpace.single j 1) * h.ofLp j := by
      rfl

/-- The M-estimator score vector obtained by taking coordinates of the DQM
score is definitionally the original Euclidean score. -/
@[simp] lemma psiVec_score_eq
    {d : ℕ} {Ω : Type*} (θ₀ : EuclideanSpace ℝ (Fin d))
    (ℓ : Ω → EuclideanSpace ℝ (Fin d)) (x : Ω) :
    psiVec (fun _ i x => ℓ x i) θ₀ x = ℓ x := by
  rfl

/-- A normalized density induces the true probability law as a `withDensity`
measure.  Zero density is retained as zero mass; no strict-positivity premise
is needed. -/
lemma withDensity_density_isProbabilityMeasure
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))) (μ : Measure Ω)
    -- Normalized integrable densities for the parametric family.
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin d)) :
    IsProbabilityMeasure
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) := by
  refine ⟨?_⟩
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hPDF.density_integrable θ₀)
      (Filter.Eventually.of_forall (M.density_nonneg θ₀)),
    hPDF.density_integral_eq_one θ₀, ENNReal.ofReal_one]

/-- DQM implies that the bundled finite-dimensional score belongs to
`L²(P₀)`.  This is the score-integrability boundary consumed by T8, derived
from DQM rather than exposed by the eventual MLE headline. -/
lemma dqm_scoreVector_memLp_two
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))) (μ : Measure Ω)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (ℓ : Ω → EuclideanSpace ℝ (Fin d))
    -- Measurability of the DQM score map.
    (hℓ : Measurable ℓ)
    -- Normalized integrable densities for the parametric family.
    (hPDF : IsPDFOf M μ)
    -- Differentiability in quadratic mean at the true parameter.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) :
    MemLp (psiVec (fun _ i x => ℓ x i) θ₀) 2
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) := by
  change MemLp ℓ 2 (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
  refine (memLp_two_iff_integrable_sq_norm hℓ.aestronglyMeasurable).2 ?_
  rw [integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal, M.density_nonneg] using
    dqm_norm_sq_score_integrable M μ θ₀ ℓ (hPDF.density_integrable θ₀) hDQM
      (fun t u => hPDF.density_integrable (θ₀ + t • u))

/-- Every coordinate of a DQM score has mean zero under the true law `P₀`.
This uses the score theorem itself, not the older `SigmaFinite`-bearing LAN
wrapper. -/
lemma dqm_scoreCoordinate_mean_zero
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))) (μ : Measure Ω)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (ℓ : Ω → EuclideanSpace ℝ (Fin d))
    -- Measurability of the DQM score map.
    (hℓ : Measurable ℓ)
    -- Normalized integrable densities for the parametric family.
    (hPDF : IsPDFOf M μ)
    -- Differentiability in quadratic mean at the true parameter.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) (i : Fin d) :
    ∫ x, ℓ x i
      ∂(μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) = 0 := by
  let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i (1 : ℝ)
  have hcoord : ∀ x, ⟪e, ℓ x⟫ = ℓ x i := by
    intro x
    have h := EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ) (ℓ x)
    rw [map_one, one_mul] at h
    exact h
  have hzero : ∫ x, ⟪e, ℓ x⟫ * M.density θ₀ x ∂μ = 0 :=
    Score.score_mean_zero M μ θ₀ ℓ hℓ
      (hPDF.density_integral_eq_one θ₀) (hPDF.density_integrable θ₀)
      (fun t u => hPDF.density_integral_eq_one (θ₀ + t • u))
      (fun t u => hPDF.density_integrable (θ₀ + t • u)) hDQM
      (dqm_fisher_integrable M μ θ₀ ℓ (hPDF.density_integrable θ₀) hDQM e
        (fun t => hPDF.density_integrable (θ₀ + t • e)))
      (dqm_residual_eventually_memLp M μ θ₀ ℓ hDQM e)
  rw [integral_withDensity_eq_integral_toReal_smul
    (M.density_meas θ₀).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    ∫ x, (ENNReal.ofReal (M.density θ₀ x)).toReal • ℓ x i ∂μ
        = ∫ x, ⟪e, ℓ x⟫ * M.density θ₀ x ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x), hcoord]
            simp [mul_comm]
    _ = 0 := hzero

/-- The covariance matrix constructed by the empirical-process interface from
the DQM score coordinates is exactly the standard-basis Fisher information
matrix.  This is a definition/measure-change adapter, not a compatibility
hypothesis. -/
lemma psiCov_score_eq_fisherInformationMatrix
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))) (μ : Measure Ω)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (ℓ : Ω → EuclideanSpace ℝ (Fin d)) :
    psiCov (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
      (fun _ i x => ℓ x i) θ₀ = fisherInformationMatrix M μ θ₀ ℓ := by
  ext i j
  simp only [psiCov, fisherInformationMatrix, fisherInformation, Matrix.of_apply]
  rw [integral_withDensity_eq_integral_toReal_smul
    (M.density_meas θ₀).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  have hi := EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ) (ℓ x)
  have hj := EuclideanSpace.inner_single_left (𝕜 := ℝ) j (1 : ℝ) (ℓ x)
  rw [map_one, one_mul] at hi hj
  rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x), ← hi, ← hj]
  change M.density θ₀ x * (⟪EuclideanSpace.single i 1, ℓ x⟫ *
      ⟪EuclideanSpace.single j 1, ℓ x⟫) =
    (⟪EuclideanSpace.single i 1, ℓ x⟫ *
      ⟪EuclideanSpace.single j 1, ℓ x⟫) * M.density θ₀ x
  ring

/-- Positive-definite Fisher information supplies all matrix data needed by
the M-estimator theorem for the canonical log-likelihood curvature `V = -I`:
Hermitian symmetry, nonsingularity, and uniform negative definiteness. -/
lemma neg_posDef_as_mEstimator_curvature
    {d : ℕ} {I : Matrix (Fin d) (Fin d) ℝ}
    -- Nonsingular Fisher information, as required by vdV 5.39.
    -- nondegeneracy condition.
    (hI : I.PosDef) :
    ∃ c : ℝ, 0 < c ∧
      (-I).IsHermitian ∧ IsUnit (-I).det ∧
      ∀ x : EuclideanSpace ℝ (Fin d),
        ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-I) x⟫
          ≤ -c * ‖x‖ ^ 2 := by
  obtain ⟨c, hc, hcoerc⟩ := hI.exists_inner_toEuclideanCLM_ge
  refine ⟨c, hc, hI.isHermitian.neg, ?_, fun x => ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det (-I)).mp hI.isUnit.neg
  · have hx := neg_le_neg (hcoerc x)
    simpa [map_neg, neg_mul] using hx

/-- With score covariance `I` and log-likelihood curvature `V = -I`, the T8
sandwich covariance `V⁻¹ I V⁻ᵀ` reduces to the inverse Fisher information.
The zero-dimensional case is covered by the same matrix identity. -/
lemma mEstimator_fisher_covariance_collapse
    {d : ℕ} (I : Matrix (Fin d) (Fin d) ℝ)
    -- Nonsingular Fisher information.
    (hI : I.PosDef) :
    (-I)⁻¹ * I * ((-I)⁻¹).transpose = I⁻¹ := by
  let A : Matrix (Fin d) (Fin d) ℝ := (-I)⁻¹
  have hdet : IsUnit I.det := (Matrix.isUnit_iff_isUnit_det I).mp hI.isUnit
  have hnegdet : IsUnit (-I).det :=
    (Matrix.isUnit_iff_isUnit_det (-I)).mp hI.isUnit.neg
  have hAherm : A.IsHermitian := hI.isHermitian.neg.inv
  have hAtrans : A.transpose = A := by
    ext i j
    change A j i = A i j
    simpa using hAherm.apply i j
  have hAI : A * I = -1 := by
    have h := Matrix.nonsing_inv_mul (-I) hnegdet
    change A * (-I) = 1 at h
    calc
      A * I = -(A * (-I)) := by
        rw [mul_neg]
        exact (neg_neg (A * I)).symm
      _ = -1 := by rw [h]
  have hnegAI : (-A) * I = 1 := by
    have h := Matrix.nonsing_inv_mul (-I) hnegdet
    change A * (-I) = 1 at h
    simpa [neg_mul, mul_neg] using h
  have hnegA_eq : -A = I⁻¹ := by
    calc
      -A = (-A) * 1 := by rw [mul_one]
      _ = (-A) * (I * I⁻¹) := by rw [Matrix.mul_nonsing_inv I hdet]
      _ = ((-A) * I) * I⁻¹ := by rw [Matrix.mul_assoc]
      _ = I⁻¹ := by rw [hnegAI, one_mul]
  change A * I * A.transpose = I⁻¹
  rw [hAtrans, hAI, neg_one_mul, hnegA_eq]

end AsymptoticStatistics
