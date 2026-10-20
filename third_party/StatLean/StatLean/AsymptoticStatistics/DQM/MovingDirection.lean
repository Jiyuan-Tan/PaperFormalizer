module
public import StatLean.AsymptoticStatistics.DQM.ZeroDensity

@[expose] public section

/-!
# DQM along moving local directions

Support-free consequences of differentiability in quadratic mean along parameter
sequences whose sample-size-scaled displacement converges.  These statements extend
the fixed-direction residual and singular-mass controls in `DQM/Properties.lean` to
the moving directions needed by local product-experiment comparisons.
-/

open MeasureTheory Asymptotics Filter Topology
open scoped RealInnerProductSpace

namespace AsymptoticStatistics

variable {d : ℕ}
variable {𝒳 : Type*} [MeasurableSpace 𝒳]

private lemma movingDisplacement_tendsto_zero
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (θ : ℕ → EuclideanSpace ℝ (Fin d)) (θ₀ h : EuclideanSpace ℝ (Fin d))
    (hθ : Tendsto (fun n => Real.sqrt (m n) • (θ n - θ₀)) atTop (nhds h)) :
    Tendsto (fun n => θ n - θ₀) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n => Real.sqrt (m n)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).comp hm
  have hinv : Tendsto (fun n => (Real.sqrt (m n))⁻¹) atTop (nhds 0) := by
    simpa using! hsqrt.inv_tendsto_atTop
  have hprod := hinv.smul hθ
  simp only [zero_smul] at hprod
  refine hprod.congr' ?_
  filter_upwards [hm.eventually (eventually_ge_atTop 1)] with n hn
  have hsqrt_ne : Real.sqrt (m n) ≠ 0 := by positivity
  rw [smul_smul, inv_mul_cancel₀ hsqrt_ne, one_smul]

private lemma movingResidual_eventually_memLp
    (M : ParametricFamily 𝒳 (EuclideanSpace ℝ (Fin d))) (μ : Measure 𝒳)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (ℓ : 𝒳 → EuclideanSpace ℝ (Fin d))
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (θ : ℕ → EuclideanSpace ℝ (Fin d))
    (h : EuclideanSpace ℝ (Fin d))
    (hθ : Tendsto (fun n => Real.sqrt (m n) • (θ n - θ₀)) atTop (nhds h)) :
    ∀ᶠ n in atTop, MemLp (fun x =>
      Real.sqrt (m n) * (M.sqrtDensity (θ n) x - M.sqrtDensity θ₀ x) -
        (1 / 2 : ℝ) * ⟪Real.sqrt (m n) • (θ n - θ₀), ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
  have hmem := (movingDisplacement_tendsto_zero m hm θ θ₀ h hθ).eventually hDQM.mem
  filter_upwards [hmem] with n hn
  have hθeq : θ₀ + (θ n - θ₀) = θ n := by simp [sub_eq_add_neg]
  rw [← hθeq]
  simp_rw [real_inner_smul_left]
  convert hn.const_mul (Real.sqrt (m n)) using 1
  funext x
  simp only [add_sub_cancel_left]
  ring

/-- **DQM residual convergence along a moving local direction.**

If `m n → ∞` and `√(m n) • (θ n - θ₀) → h`, then the squared `L²(μ)`
norm of the DQM residual, scaled by `m n`, tends to zero.  The score term uses
the actual scaled direction at index `n`; the limit `h` enters only through the
assumed convergence.
-/
theorem dqm_scaled_path_residual_tendsto
    (M : ParametricFamily 𝒳 (EuclideanSpace ℝ (Fin d)))
    (μ : Measure 𝒳)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (ℓ : 𝒳 → EuclideanSpace ℝ (Fin d))
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (θ : ℕ → EuclideanSpace ℝ (Fin d))
    (h : EuclideanSpace ℝ (Fin d))
    (hθ : Tendsto (fun n => Real.sqrt (m n) • (θ n - θ₀)) atTop (nhds h)) :
    Tendsto
      (fun n : ℕ =>
        ∫ x,
          (Real.sqrt (m n) * (M.sqrtDensity (θ n) x - M.sqrtDensity θ₀ x)
            - (1 / 2 : ℝ) *
              ⟪Real.sqrt (m n) • (θ n - θ₀), ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
      atTop (nhds 0) := by
  let δ : ℕ → EuclideanSpace ℝ (Fin d) := fun n => θ n - θ₀
  have hδ : Tendsto δ atTop (nhds 0) :=
    movingDisplacement_tendsto_zero m hm θ θ₀ h hθ
  have hsmall : (fun n : ℕ =>
        ∫ x, (M.sqrtDensity (θ₀ + δ n) x - M.sqrtDensity θ₀ x
          - (1 / 2 : ℝ) * ⟪δ n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
      =o[atTop] (fun n => ‖δ n‖ ^ 2) := hDQM.isLittleO.comp_tendsto hδ
  have hmul : (fun n : ℕ => (m n : ℝ) *
        ∫ x, (M.sqrtDensity (θ₀ + δ n) x - M.sqrtDensity θ₀ x
          - (1 / 2 : ℝ) * ⟪δ n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
      =o[atTop] (fun n => (m n : ℝ) * ‖δ n‖ ^ 2) :=
    (isBigO_refl (fun n : ℕ => (m n : ℝ)) atTop).mul_isLittleO hsmall
  have hscale : (fun n => (m n : ℝ) * ‖δ n‖ ^ 2) =
      fun n => ‖Real.sqrt (m n) • (θ n - θ₀)‖ ^ 2 := by
    funext n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have hscaleO : (fun n => (m n : ℝ) * ‖δ n‖ ^ 2) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
    rw [hscale]
    exact (hθ.norm.pow 2).isBigO_one ℝ
  have htend : Tendsto (fun n : ℕ => (m n : ℝ) *
        ∫ x, (M.sqrtDensity (θ₀ + δ n) x - M.sqrtDensity θ₀ x
          - (1 / 2 : ℝ) * ⟪δ n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
      atTop (nhds 0) := (isLittleO_one_iff ℝ).mp (hmul.trans_isBigO hscaleO)
  refine htend.congr' (Eventually.of_forall fun n => ?_)
  dsimp only
  have hθeq : θ₀ + δ n = θ n := by simp [δ, sub_eq_add_neg]
  rw [← hθeq]
  simp_rw [real_inner_smul_left]
  calc
    (m n : ℝ) * ∫ x, (M.sqrtDensity (θ₀ + δ n) x - M.sqrtDensity θ₀ x
        - (1 / 2 : ℝ) * ⟪δ n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
        = (Real.sqrt (m n)) ^ 2 * ∫ x,
            (M.sqrtDensity (θ₀ + δ n) x - M.sqrtDensity θ₀ x
              - (1 / 2 : ℝ) * ⟪δ n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
          rw [Real.sq_sqrt (Nat.cast_nonneg _)]
    _ = ∫ x, (Real.sqrt (m n) * (M.sqrtDensity (θ₀ + δ n) x
            - M.sqrtDensity θ₀ x) - (1 / 2 : ℝ) *
          (Real.sqrt (m n) * ⟪δ n, ℓ x⟫) * M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by simp

/-- **Moving-path deficit mass is `o(1 / m)`.**

Along the same local path, the `θ n` density mass on the zero set of the base
density is negligible after multiplication by `m n`.  This is the support-free
replacement for assuming that every local alternative is absolutely continuous
with respect to the base law.
-/
theorem dqm_scaled_path_deficit_mass_tendsto
    (M : ParametricFamily 𝒳 (EuclideanSpace ℝ (Fin d)))
    (μ : Measure 𝒳)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (ℓ : 𝒳 → EuclideanSpace ℝ (Fin d))
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (θ : ℕ → EuclideanSpace ℝ (Fin d))
    (h : EuclideanSpace ℝ (Fin d))
    (hθ : Tendsto (fun n => Real.sqrt (m n) • (θ n - θ₀)) atTop (nhds h)) :
    Tendsto
      (fun n : ℕ =>
        (m n : ℝ) * ∫ x in {x | M.density θ₀ x = 0}, M.density (θ n) x ∂μ)
      atTop (nhds 0) := by
  have hR := dqm_scaled_path_residual_tendsto M μ θ₀ ℓ hDQM m hm θ h hθ
  have hX := movingResidual_eventually_memLp M μ θ₀ ℓ hDQM m hm θ h hθ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) hR
    (Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _)
      (setIntegral_nonneg (measurableSet_eq_fun (M.density_meas θ₀) measurable_const)
        (fun x _ => M.density_nonneg _ x))) ?_
  filter_upwards [hX] with n hn
  have hs : MeasurableSet {x | M.density θ₀ x = 0} :=
    measurableSet_eq_fun (M.density_meas θ₀) measurable_const
  have heq : (m n : ℝ) * ∫ x in {x | M.density θ₀ x = 0}, M.density (θ n) x ∂μ =
      ∫ x in {x | M.density θ₀ x = 0},
        (Real.sqrt (m n) * (M.sqrtDensity (θ n) x - M.sqrtDensity θ₀ x) -
          (1 / 2 : ℝ) * ⟪Real.sqrt (m n) • (θ n - θ₀), ℓ x⟫ *
            M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hs (fun x hx => ?_)
    have hsqrt0 : M.sqrtDensity θ₀ x = 0 := by
      unfold ParametricFamily.sqrtDensity
      rw [hx, Real.sqrt_zero]
    rw [hsqrt0, sub_zero, mul_zero, sub_zero, mul_pow, M.sqrtDensity_sq,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [heq]
  exact setIntegral_le_integral hn.integrable_sq
    (Eventually.of_forall fun _ => sq_nonneg _)

/-- **Moving-path reverse singular mass is `o(1 / m)`.**

Along the same local path, the base density mass on the zero set of the moving
`θ n` density is negligible after multiplication by `m n`.  Together with
`dqm_scaled_path_deficit_mass_tendsto`, this controls both support-mismatch terms
without imposing common support or mutual absolute continuity.
-/
theorem dqm_scaled_path_excess_mass_tendsto
    (M : ParametricFamily 𝒳 (EuclideanSpace ℝ (Fin d)))
    (μ : Measure 𝒳)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (ℓ : 𝒳 → EuclideanSpace ℝ (Fin d))
    (hPDF : IsPDFOf M μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (θ : ℕ → EuclideanSpace ℝ (Fin d))
    (h : EuclideanSpace ℝ (Fin d))
    (hθ : Tendsto (fun n => Real.sqrt (m n) • (θ n - θ₀)) atTop (nhds h)) :
    Tendsto
      (fun n : ℕ =>
        (m n : ℝ) * ∫ x in {x | M.density (θ n) x = 0}, M.density θ₀ x ∂μ)
      atTop (nhds 0) := by
  have hθ₀ : Tendsto θ atTop (nhds θ₀) := by
    have hadd := (tendsto_const_nhds : Tendsto (fun _ : ℕ => θ₀) atTop (nhds θ₀)).add
      (movingDisplacement_tendsto_zero m hm θ θ₀ h hθ)
    have heq : (fun n => θ₀ + (θ n - θ₀)) = θ := by
      funext n
      abel
    rw [heq, add_zero] at hadd
    exact hadd
  have hsmall : (fun n =>
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)).real
        {x | M.density (θ n) x = 0}) =o[atTop]
      (fun n => ‖θ n - θ₀‖ ^ 2) := by
    simpa only [Function.comp_apply] using!
      (dqm_zeroDensity_mass_isLittleO M μ θ₀ ℓ hPDF hDQM).comp_tendsto hθ₀
  have hmul := (isBigO_refl (fun n : ℕ => (m n : ℝ)) atTop).mul_isLittleO hsmall
  have hscale : (fun n => (m n : ℝ) * ‖θ n - θ₀‖ ^ 2) =
      fun n => ‖Real.sqrt (m n) • (θ n - θ₀)‖ ^ 2 := by
    funext n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have hscaleO : (fun n => (m n : ℝ) * ‖θ n - θ₀‖ ^ 2) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
    rw [hscale]
    exact (hθ.norm.pow 2).isBigO_one ℝ
  have htend := (isLittleO_one_iff ℝ).mp (hmul.trans_isBigO hscaleO)
  refine htend.congr' (Eventually.of_forall fun n => ?_)
  have hs : MeasurableSet {x | M.density (θ n) x = 0} :=
    measurableSet_eq_fun (M.density_meas _) measurable_const
  have hi := hPDF.density_integrable θ₀
  have hnonneg : 0 ≤ ∫ x in {x | M.density (θ n) x = 0}, M.density θ₀ x ∂μ :=
    setIntegral_nonneg hs (fun x _ => M.density_nonneg _ x)
  congr 1
  rw [Measure.real, withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hi.restrict
      (ae_restrict_of_ae (Eventually.of_forall (M.density_nonneg θ₀))),
    ENNReal.toReal_ofReal hnonneg]

end AsymptoticStatistics
