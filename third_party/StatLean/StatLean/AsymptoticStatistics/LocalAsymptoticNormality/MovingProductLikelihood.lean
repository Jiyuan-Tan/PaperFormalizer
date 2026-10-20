module
public import StatLean.AsymptoticStatistics.DQM.MovingDirection
public import StatLean.AsymptoticStatistics.ForMathlib.FiniteProductLikelihood
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.AsymptoticRepresentation

@[expose] public section

/-!
# Likelihood comparison for moving local product experiments

The moving-path counterpart of the fixed-direction likelihood comparison used in
the LAN representation theorem.  The sample size is `m n`, while the alternative
parameter `θ n` may vary with `n` subject to convergence of the scaled displacement.
-/

open MeasureTheory Filter Topology

namespace AsymptoticStatistics
namespace AsymptoticRepresentation

variable {k : ℕ}
variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The log-likelihood ratio for a moving local product experiment:
`Lₙ = ∑_{i < m n} log (p_{θ n}(Xᵢ) / p_{θ₀}(Xᵢ))`.

If `m n = 0`, the sample type has no coordinates and the empty sum is `0`.  Zero
density ratios use the totalized `Real.log` convention, exactly as in
`logLikelihood`.
-/
noncomputable def movingLogLikelihood
    (M : ParametricFamily 𝓧 (Θ k)) (θ₀ : Θ k) (m : ℕ → ℕ) (θ : ℕ → Θ k)
    (n : ℕ) (ω : Fin (m n) → 𝓧) : ℝ :=
  ∑ i, Real.log (M.density (θ n) (ω i) / M.density θ₀ (ω i))

/-- Measurability of the moving-path log-likelihood ratio. -/
lemma movingLogLikelihood_measurable
    (M : ParametricFamily 𝓧 (Θ k)) (θ₀ : Θ k) (m : ℕ → ℕ) (θ : ℕ → Θ k)
    (n : ℕ) :
    Measurable (movingLogLikelihood M θ₀ m θ n) := by
  unfold movingLogLikelihood
  refine Finset.univ.measurable_sum (fun i _ => ?_)
  refine Measurable.log ?_
  exact ((M.density_meas _).comp (measurable_pi_apply i)).div
    ((M.density_meas _).comp (measurable_pi_apply i))

/-- **Moving-product likelihood comparison.**

Along a moving local path with `m n → ∞` and
`√(m n) • (θ n - θ₀) → h`, the exponential moving log-likelihood is integrable
under the base product law, its total mass tends to one, and its event integrals
uniformly approximate the corresponding moving-alternative probabilities with a
single real error rate tending to zero.

The proof combines the fixed-direction product
comparison with `dqm_scaled_path_deficit_mass_tendsto` and
`dqm_scaled_path_excess_mass_tendsto`; no common-support or absolute-continuity
assumption is imposed.
-/
theorem movingProductMeasure_likelihood_comparison
    -- the parametric family under study.
    (M : ParametricFamily 𝓧 (Θ k))
    -- a dominating measure for the supplied densities.
    (μ : Measure 𝓧)
    -- the base parameter.
    (θ₀ : Θ k)
    -- the DQM score at the base parameter.
    (ℓ : 𝓧 → Θ k)
    -- every family member is a probability density with respect to `μ`.
    (hPDF : IsPDFOf M μ)
    -- differentiability in quadratic mean at `θ₀` with score `ℓ`.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- sample sizes along the local path.
    (m : ℕ → ℕ)
    -- strict monotonicity packages divergence of the indexed sample sizes.
    (hm : StrictMono m)
    -- the moving parameter sequence.
    (θ : ℕ → Θ k)
    -- the limiting scaled direction.
    (h : Θ k)
    -- convergence of the sample-size-scaled displacement.
    (hθ : Tendsto (fun n => Real.sqrt (m n) • (θ n - θ₀)) atTop (nhds h)) :
    (∀ n : ℕ,
      Integrable (fun ω => Real.exp (movingLogLikelihood M θ₀ m θ n ω))
        (productMeasure M μ θ₀ (m n))) ∧
    Tendsto
      (fun n : ℕ =>
        ∫ ω, Real.exp (movingLogLikelihood M θ₀ m θ n ω)
          ∂(productMeasure M μ θ₀ (m n)))
      atTop (nhds 1) ∧
    ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (nhds 0) ∧
      ∀ A : ∀ n, Set (Fin (m n) → 𝓧),
        (∀ n, MeasurableSet (A n)) → ∀ n,
          |(productMeasure M μ (θ n) (m n)).real (A n) -
              ∫ ω in A n, Real.exp (movingLogLikelihood M θ₀ m θ n ω)
                ∂(productMeasure M μ θ₀ (m n))| ≤ ρ n := by
  classical
  let D : ℕ → ℝ := fun n =>
    ∫ x in {x | M.density θ₀ x = 0}, M.density (θ n) x ∂μ
  let E : ℕ → ℝ := fun n =>
    ∫ x in {x | M.density (θ n) x = 0}, M.density θ₀ x ∂μ
  let c : ℕ → ℝ := fun n => 1 - D n + E n
  have hm_top : Tendsto m atTop atTop := hm.tendsto_atTop
  have hcore : ∀ n,
      Integrable (fun ω => Real.exp (movingLogLikelihood M θ₀ m θ n ω))
          (productMeasure M μ θ₀ (m n)) ∧
        (∫ ω, Real.exp (movingLogLikelihood M θ₀ m θ n ω)
            ∂(productMeasure M μ θ₀ (m n)) = c n ^ m n) ∧
        ∀ A : Set (Fin (m n) → 𝓧), MeasurableSet A →
          |(productMeasure M μ (θ n) (m n)).real A -
              ∫ ω in A, Real.exp (movingLogLikelihood M θ₀ m θ n ω)
                ∂(productMeasure M μ θ₀ (m n))| ≤
            2 * (m n : ℝ) * D n + |c n ^ m n - 1| := by
    intro n
    simpa only [FiniteProductLikelihood.productMeasureOfDensity,
      FiniteProductLikelihood.logLikelihood, Function.comp_apply, productMeasure,
      movingLogLikelihood, D, E, c] using!
      (FiniteProductLikelihood.finiteProduct_expLog_comparison μ
        (M.density θ₀) (M.density (θ n)) (m n)
        (M.density_meas θ₀) (M.density_meas (θ n))
        (M.density_nonneg θ₀) (M.density_nonneg (θ n))
        (hPDF.density_integrable θ₀) (hPDF.density_integrable (θ n))
        (hPDF.density_integral_eq_one θ₀) (hPDF.density_integral_eq_one (θ n)))
  have hD : Tendsto (fun n => (m n : ℝ) * D n) atTop (nhds 0) := by
    simpa only [D] using
      dqm_scaled_path_deficit_mass_tendsto M μ θ₀ ℓ hDQM m hm_top θ h hθ
  have hE : Tendsto (fun n => (m n : ℝ) * E n) atTop (nhds 0) := by
    simpa only [E] using
      dqm_scaled_path_excess_mass_tendsto M μ θ₀ ℓ hPDF hDQM m hm_top θ h hθ
  have hscaled : Tendsto (fun n => (m n : ℝ) * (E n - D n)) atTop (nhds 0) := by
    have hsub := hE.sub hD
    simpa only [sub_zero] using hsub.congr' (Eventually.of_forall fun n => by ring)
  have hpow : Tendsto (fun n => c n ^ m n) atTop (nhds 1) := by
    have h := FiniteProductLikelihood.tendsto_one_add_pow_nat_zero_of_scaled_tendsto
      m (fun n => E n - D n) hm_top hscaled
    exact h.congr' (Eventually.of_forall fun n => by
      congr 1
      simp only [c]
      ring)
  have hmass : Tendsto
      (fun n : ℕ =>
        ∫ ω, Real.exp (movingLogLikelihood M θ₀ m θ n ω)
          ∂(productMeasure M μ θ₀ (m n))) atTop (nhds 1) :=
    hpow.congr' (Eventually.of_forall fun n => (hcore n).2.1.symm)
  let ρ : ℕ → ℝ := fun n =>
    2 * ((m n : ℝ) * D n) + |c n ^ m n - 1|
  have hρ : Tendsto ρ atTop (nhds 0) := by
    have habs : Tendsto (fun n => |c n ^ m n - 1|) atTop (nhds 0) := by
      simpa using (hpow.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))).abs
    simpa only [ρ, mul_zero, zero_add] using (hD.const_mul 2).add habs
  refine ⟨fun n => (hcore n).1, hmass, ρ, hρ, ?_⟩
  intro A hA n
  simpa only [ρ, mul_assoc] using (hcore n).2.2 (A n) (hA n)

end AsymptoticRepresentation
end AsymptoticStatistics
