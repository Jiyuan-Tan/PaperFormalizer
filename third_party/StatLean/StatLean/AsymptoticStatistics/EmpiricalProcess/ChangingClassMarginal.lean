module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChangingLindeberg
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChangingClassCore
public import StatLean.AsymptoticStatistics.EmpiricalProcess.TriangularLindeberg
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess

@[expose] public section

/-!
# Finite-dimensional convergence for changing classes

This file proves marginal convergence for van der
Vaart Theorem 19.28.  It specializes the row-iid triangular Lindeberg theorem
to finitely many coordinates of a changing class, derives positivity of every
finite cut of the limiting covariance kernel, and records the exact empirical-
process coordinate readout.

Reference: van der Vaart, *Asymptotic Statistics*, Theorem 19.28, pp.282--283.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Real Topology

variable {Ω T : Type*} [MeasurableSpace Ω]

-- Port note (Lean v4.33 / Mathlib db584cd): instance search no longer sees a covariance written as
-- a bare lambda `fun i j => …` through the `Matrix` type, so `isGaussian_multivariateGaussian`
-- is not found for it; this local instance restates the same fact for such arguments.
instance isProbabilityMeasure_multivariateGaussian_fun {ι : Type*} [Fintype ι]
    [DecidableEq ι] (μ : EuclideanSpace ℝ ι) (S : ι → ι → ℝ) :
    IsProbabilityMeasure (multivariateGaussian μ S) :=
  (isGaussian_multivariateGaussian (μ := μ) (S := S)).toIsProbabilityMeasure

/-- The centered covariance of two coordinates in row `n` of a changing class.

Constitutive (vdV Theorem 19.28 pp.282--283): this is exactly
`P fₙ,s fₙ,t - P fₙ,s P fₙ,t`.  Lean's Bochner integral is total, but every
use in the marginal theorem derives rowwise `L²`, so the nonintegrable
fallback is not reached. -/
noncomputable def changingCovariance
    (P : Measure Ω) (f : ℕ → T → Ω → ℝ) (n : ℕ) (s t : T) : ℝ :=
  ∫ x, f n s x * f n t x ∂P -
    (∫ x, f n s x ∂P) * (∫ x, f n t x ∂P)

/-- The raw Euclidean vector obtained by reading finitely many coordinates of
a changing class.

This is the finite-coordinate encoding used for vdV Theorem 19.28. Edge
behavior: when `k = 0`, this is the unique vector in the zero-dimensional
Euclidean space. -/
noncomputable def coordinateVector
    (f : ℕ → T → Ω → ℝ) {k : ℕ} (t : Fin k → T)
    (n : ℕ) (x : Ω) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => f n (t i) x)

/-- Subtracting the Bochner mean of the raw coordinate vector gives the
existing coordinatewise-centered vector. -/
lemma coordinateVector_sub_integral_eq_centeredCoordinateVector
    (P : Measure Ω) (f : ℕ → T → Ω → ℝ) {k : ℕ} (t : Fin k → T)
    (n : ℕ) (x : Ω)
    (hf_int : Integrable (coordinateVector f t n) P) :
    coordinateVector f t n x - ∫ y, coordinateVector f t n y ∂P =
      centeredCoordinateVector P f t n x := by
  ext i
  change f n (t i) x - (∫ y, coordinateVector f t n y ∂P) i =
    f n (t i) x - ∫ y, f n (t i) y ∂P
  rw [MeasureTheory.eval_integral_piLp (fun j => hf_int.eval_piLp j) i]
  rfl

/-- The centered covariance matrix of a raw coordinate vector is the
corresponding finite cut of `changingCovariance`. -/
lemma centeredCovMatrix_coordinateVector
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → T → Ω → ℝ) {k : ℕ} (t : Fin k → T) (n : ℕ)
    (hf_memLp : ∀ i, MemLp (fun x => f n (t i) x) 2 P) :
    centeredCovMatrix P (coordinateVector f t) n =
      fun i j => changingCovariance P f n (t i) (t j) := by
  have hvec_memLp : MemLp (coordinateVector f t n) 2 P := by
    apply MeasureTheory.MemLp.of_eval_piLp
    intro i
    simpa only [coordinateVector] using hf_memLp i
  have hvec_int : Integrable (coordinateVector f t n) P :=
    hvec_memLp.integrable (by norm_num)
  ext i j
  simp_rw [centeredCovMatrix, centeredVectorRow,
    coordinateVector_sub_integral_eq_centeredCoordinateVector P f t n _ hvec_int]
  change cov[(fun x => f n (t i) x), (fun x => f n (t j) x); P] = _
  rw [covariance_eq_sub (hf_memLp i) (hf_memLp j)]
  rfl

/-- The normalized sum of centered coordinate vectors is exactly the vector
of empirical-process readouts.  Both sides are zero when `n = 0`. -/
lemma centeredCoordinateSum_eq_empiricalProcessVector
    (P : Measure Ω) (f : ℕ → T → Ω → ℝ) {k n : ℕ}
    (t : Fin k → T) (X : Fin n → Ω) :
    (Real.sqrt n)⁻¹ •
        ∑ i : Fin n, centeredCoordinateVector P f t n (X i) =
      WithLp.toLp 2 (fun j => empiricalProcess P n X (f n (t j))) := by
  apply WithLp.ofLp_injective
  ext j
  simp only [WithLp.ofLp_smul, WithLp.ofLp_sum, centeredCoordinateVector,
    Finset.sum_apply, Pi.smul_apply]
  by_cases hn : n = 0
  · subst n
    simp [empiricalProcess]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
    change (Real.sqrt n)⁻¹ *
        ∑ i, (f n (t j) (X i) - ∫ y, f n (t j) y ∂P) =
      Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i, f n (t j) (X i) -
        ∫ y, f n (t j) y ∂P)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [hsqrt, hn']
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]

/-- Every finite cut of the pointwise limiting changing-class covariance
kernel is positive semidefinite.

This is derived from the positive semidefiniteness of the centered row
covariance matrices and is deliberately not a hypothesis of
`changingClass_fdd`.  Empty finite cuts and singular limits are included. -/
theorem changingClass_kernelCovariance_posSemidef
    {P : Measure Ω} [IsProbabilityMeasure P]
    {f : ℕ → T → Ω → ℝ} {Φ : ℕ → Ω → ℝ}
    (hΦ : ChangingEnvelope f Φ)
    (hLin : ChangingLindeberg P Φ)
    (hf_meas : ∀ n t, Measurable (f n t))
    (hΦmeas : ∀ n, Measurable (Φ n))
    {C : T → T → ℝ}
    (hC : ∀ s t, Tendsto (fun n => changingCovariance P f n s t)
      atTop (𝓝 (C s t))) :
    ∀ k (t : Fin k → T),
      Matrix.PosSemidef (fun i j : Fin k => C (t i) (t j)) := by
  intro k t
  have hf_coord : ∀ n i, MemLp (fun x => f n (t i) x) 2 P := by
    intro n i
    exact MemLp.mono' (hLin.envelope_memLp_two hΦmeas n)
      (hf_meas n (t i)).aestronglyMeasurable (Eventually.of_forall fun x => by
        have hΦnonneg : 0 ≤ Φ n x := (abs_nonneg _).trans (hΦ n (t i) x)
        simpa only [Real.norm_eq_abs, abs_of_nonneg hΦnonneg] using hΦ n (t i) x)
  have hvec_memLp : ∀ n, MemLp (coordinateVector f t n) 2 P := by
    intro n
    apply MeasureTheory.MemLp.of_eval_piLp
    intro i
    simpa only [coordinateVector] using hf_coord n i
  have hcov : Tendsto (centeredCovMatrix P (coordinateVector f t)) atTop
      (𝓝 (fun i j : Fin k => C (t i) (t j))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    convert hC (t i) (t j) using 1
    funext n
    exact congrFun (congrFun
      (centeredCovMatrix_coordinateVector P f t n (hf_coord n)) i) j
  exact posSemidef_of_tendsto_centeredCovMatrix hvec_memLp hcov

/-- Finite-dimensional convergence for the changing-class empirical process
in van der Vaart Theorem 19.28.

The conclusion is ordinary convergence in distribution of every finite
coordinate vector.  It permits `k = 0`, `n = 0`, and singular limiting
covariance matrices; no Feller condition, cross-row law, positive-definiteness
certificate, or supplied Gaussian law is assumed. -/
theorem changingClass_fdd
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : iIndepFun X μ)
    (hX_idem : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (f : ℕ → T → Ω → ℝ)
    (Φ : ℕ → Ω → ℝ)
    (hΦ : ChangingEnvelope f Φ)
    (hLin : ChangingLindeberg P Φ)
    (hf_meas : ∀ n t, Measurable (f n t))
    (hΦmeas : ∀ n, Measurable (Φ n))
    (C : T → T → ℝ)
    (hC : ∀ s t, Tendsto (fun n => changingCovariance P f n s t)
      atTop (𝓝 (C s t)))
    {k : ℕ} (t : Fin k → T) :
    TendstoInDistribution
      (fun (n : ℕ) ξ => (Real.sqrt n)⁻¹ •
        ∑ i : Fin n, centeredCoordinateVector P f t n (X i.val ξ))
      atTop (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
      (fun _ => μ) (multivariateGaussian 0 (fun i j => C (t i) (t j))) := by
  have hf_coord : ∀ n i, MemLp (fun x => f n (t i) x) 2 P := by
    intro n i
    exact MemLp.mono' (hLin.envelope_memLp_two hΦmeas n)
      (hf_meas n (t i)).aestronglyMeasurable (Eventually.of_forall fun x => by
        have hΦnonneg : 0 ≤ Φ n x := (abs_nonneg _).trans (hΦ n (t i) x)
        simpa only [Real.norm_eq_abs, abs_of_nonneg hΦnonneg] using hΦ n (t i) x)
  have hvec_memLp : ∀ n, MemLp (coordinateVector f t n) 2 P := by
    intro n
    apply MeasureTheory.MemLp.of_eval_piLp
    intro i
    simpa only [coordinateVector] using hf_coord n i
  have hvec_meas : ∀ n, Measurable (coordinateVector f t n) := by
    intro n
    exact (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp
      (measurable_pi_iff.mpr fun i => hf_meas n (t i))
  have hcenter : ∀ n x,
      centeredVectorRow P (coordinateVector f t) n x =
        centeredCoordinateVector P f t n x := by
    intro n x
    simpa only [centeredVectorRow] using
      coordinateVector_sub_integral_eq_centeredCoordinateVector
        P f t n x ((hvec_memLp n).integrable (by norm_num))
  have hcov : Tendsto (centeredCovMatrix P (coordinateVector f t)) atTop
      (𝓝 (fun i j : Fin k => C (t i) (t j))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    convert hC (t i) (t j) using 1
    funext n
    exact congrFun (congrFun
      (centeredCovMatrix_coordinateVector P f t n (hf_coord n)) i) j
  have hLin_vec : ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun n : ℕ => ∫⁻ x in
          {x | ε * Real.sqrt n < ‖centeredVectorRow P (coordinateVector f t) n x‖},
          ENNReal.ofReal (‖centeredVectorRow P (coordinateVector f t) n x‖ ^ 2) ∂P)
        atTop (𝓝 0) := by
    intro ε hε
    simpa only [hcenter] using envelope_lindeberg_vector
      hΦ hLin hf_meas hΦmeas t ε hε
  simpa only [hcenter] using
    (tendstoInDistribution_triangular_iid_lindeberg
      P μ X hX_meas hX_iindep hX_idem hX_law
      (coordinateVector f t) hvec_meas hvec_memLp hcov hLin_vec)

/-- The row-`n` changing-class empirical process as a bounded path on `T`.

The changing envelope gives the uniform pointwise bound
`|𝔾ₙ fₙ,ₜ| ≤ √n (Pₙ|Φₙ| + P|Φₙ|)`, while the changing
Lindeberg condition and envelope measurability make `P|Φₙ|` finite.
Thus no boundedness or truncation certificate is supplied by the caller. -/
noncomputable def changingClassEmpiricalProcessLinf
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → T → Ω → ℝ) (Φ : ℕ → Ω → ℝ)
    (hΦ : ChangingEnvelope f Φ) (hLin : ChangingLindeberg P Φ)
    (hf_meas : ∀ n t, Measurable (f n t)) (hΦmeas : ∀ n, Measurable (Φ n))
    (n : ℕ) (sample : Fin n → Ω) : LinfT T :=
  ⟨fun t ↦ empiricalProcess P n sample (f n t), by
    have hΦint : Integrable (fun x ↦ |Φ n x|) P :=
      hLin.envelope_abs_integrable hΦmeas n
    refine memℓp_infty ⟨Real.sqrt n *
      (empiricalAvg (fun x ↦ |Φ n x|) n sample + ∫ x, |Φ n x| ∂P), ?_⟩
    rintro _ ⟨t, rfl⟩
    simp only [Real.norm_eq_abs]
    have hf_memLp : MemLp (f n t) 2 P :=
      MemLp.mono' (hLin.envelope_memLp_two hΦmeas n)
        (hf_meas n t).aestronglyMeasurable
        (Eventually.of_forall fun x ↦ by
          have hΦnonneg : 0 ≤ Φ n x := (abs_nonneg _).trans (hΦ n t x)
          simpa only [Real.norm_eq_abs, abs_of_nonneg hΦnonneg] using hΦ n t x)
    have hf_int : Integrable (f n t) P := hf_memLp.integrable (by norm_num)
    have hPn : |empiricalAvg (f n t) n sample| ≤
        empiricalAvg (fun x ↦ |Φ n x|) n sample := by
      unfold empiricalAvg
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc
        |∑ i, f n t (sample i)| ≤ ∑ i, |f n t (sample i)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |Φ n (sample i)| := Finset.sum_le_sum fun i _ ↦
          (hΦ n t (sample i)).trans (le_abs_self _)
    have hP : |∫ x, f n t x ∂P| ≤ ∫ x, |Φ n x| ∂P := by
      calc
        |∫ x, f n t x ∂P| ≤ ∫ x, |f n t x| ∂P :=
          abs_integral_le_integral_abs
        _ ≤ ∫ x, |Φ n x| ∂P := integral_mono hf_int.abs hΦint fun x ↦
          (hΦ n t x).trans (le_abs_self _)
    unfold empiricalProcess
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    exact (abs_sub _ _).trans (add_le_add hPn hP)⟩

/-- Finite evaluation of the bounded changing-class path is exactly the
normalized centered-coordinate sum used by `changingClass_fdd`. -/
lemma finiteCoordinateProjection_changingClassEmpiricalProcessLinf
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → T → Ω → ℝ) (Φ : ℕ → Ω → ℝ)
    (hΦ : ChangingEnvelope f Φ) (hLin : ChangingLindeberg P Φ)
    (hf_meas : ∀ n t, Measurable (f n t)) (hΦmeas : ∀ n, Measurable (Φ n))
    {k n : ℕ} (t : Fin k → T) (sample : Fin n → Ω) :
    finiteCoordinateProjection t
        (changingClassEmpiricalProcessLinf P f Φ hΦ hLin hf_meas hΦmeas n sample) =
      (Real.sqrt n)⁻¹ •
        ∑ i : Fin n, centeredCoordinateVector P f t n (sample i) := by
  rw [centeredCoordinateSum_eq_empiricalProcessVector]
  apply WithLp.ofLp_injective
  ext j
  rfl

/-- The changing-class empirical-process paths satisfy the finite-dimensional
convergence predicate on `LinfT T`. -/
theorem changingClass_fdd_linfT
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : iIndepFun X μ)
    (hX_idem : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (f : ℕ → T → Ω → ℝ) (Φ : ℕ → Ω → ℝ)
    (hΦ : ChangingEnvelope f Φ) (hLin : ChangingLindeberg P Φ)
    (hf_meas : ∀ n t, Measurable (f n t)) (hΦmeas : ∀ n, Measurable (Φ n))
    (C : T → T → ℝ)
    (hC : ∀ s t, Tendsto (fun n ↦ changingCovariance P f n s t)
      atTop (𝓝 (C s t))) :
    FDDConverges (fun _ ↦ μ)
      (fun n ξ ↦ changingClassEmpiricalProcessLinf P f Φ hΦ hLin hf_meas hΦmeas n
        (fun i ↦ X i.val ξ)) C := by
  intro k t
  refine MeasureTheory.TendstoInDistribution.congr ?_ (Eventually.of_forall fun _ ↦ rfl)
    (changingClass_fdd P μ X hX_meas hX_iindep hX_idem hX_law
      f Φ hΦ hLin hf_meas hΦmeas C hC t)
  intro n
  exact Eventually.of_forall fun ξ ↦
    (finiteCoordinateProjection_changingClassEmpiricalProcessLinf
      P f Φ hΦ hLin hf_meas hΦmeas t (fun i ↦ X i.val ξ)).symm

end AsymptoticStatistics.EmpiricalProcess
