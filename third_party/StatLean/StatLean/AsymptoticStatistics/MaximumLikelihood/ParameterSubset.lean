module
public import StatLean.AsymptoticStatistics.DQM.ParameterSubset
public import StatLean.AsymptoticStatistics.MaximumLikelihood.FisherAdapters
public import StatLean.AsymptoticStatistics.MaximumLikelihood.Likelihood

@[expose] public section

/-!
# Maximum likelihood on a parameter subset

Adapters in this file connect an MLE indexed by `Θ ⊆ ℝᵈ` to the canonical
ambient extension of its model.  They also transfer the local likelihood
regularity used in van der Vaart, Theorem 5.39.
-/

namespace AsymptoticStatistics.MaximumLikelihood

open MeasureTheory Filter Topology

/-- The Fisher information matrix for a model indexed by `Θ ⊆ ℝᵈ`, computed
from its canonical ambient extension.  Outside `Θ` the extension equals the
true density; the matrix is evaluated at the interior point `θ₀`. -/
noncomputable def fisherInformationMatrixOn
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Θ : Set (EuclideanSpace ℝ (Fin d))}
    (M : ParametricFamily Ω Θ) (μ : Measure Ω) (θ₀ : Θ)
    (ℓ : Ω → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ := by
  exact fisherInformationMatrix (M.extendFromSetAt θ₀) μ
    (θ₀ : EuclideanSpace ℝ (Fin d)) ℓ

/-- The subset Fisher matrix unfolds to the Fisher matrix of the canonical
ambient extension. -/
theorem fisherInformationMatrixOn_eq
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Θ : Set (EuclideanSpace ℝ (Fin d))}
    (M : ParametricFamily Ω Θ) (μ : Measure Ω) (θ₀ : Θ)
    (ℓ : Ω → EuclideanSpace ℝ (Fin d)) :
    fisherInformationMatrixOn M μ θ₀ ℓ =
      fisherInformationMatrix (M.extendFromSetAt θ₀) μ (θ₀ : EuclideanSpace ℝ (Fin d)) ℓ := by
  rfl

/-- Coerce a subset-valued estimator to the ambient Euclidean parameter
space. -/
def liftEstimatorFromSet
    {d : ℕ} {Ω : Type*} {Θ : Set (EuclideanSpace ℝ (Fin d))}
    (θhat : ∀ n, (Fin n → Ω) → Θ) :
    ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d) := by
  exact fun n x => θhat n x

/-- Lifting a subset-valued estimator only applies the subtype coercion. -/
@[simp] theorem liftEstimatorFromSet_apply
    {d : ℕ} {Ω : Type*} {Θ : Set (EuclideanSpace ℝ (Fin d))}
    (θhat : ∀ n, (Fin n → Ω) → Θ) (n : ℕ) (x : Fin n → Ω) :
    liftEstimatorFromSet θhat n x = (θhat n x : EuclideanSpace ℝ (Fin d)) := by
  rfl

/-- An exact MLE over `Θ` lifts to an exact MLE of the ambient extension.
Outside `Θ` the likelihood equals that at `θ₀`, while the subset MLE
already dominates the truth point. -/
theorem isMaximumLikelihoodEstimator_extendFromSetAt
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Θ : Set (EuclideanSpace ℝ (Fin d))}
    (M : ParametricFamily Ω Θ) (θ₀ : Θ)
    (θhat : ∀ n, (Fin n → Ω) → Θ)
    -- Exact product-likelihood maximization over the book's parameter set.
    (hMLE : IsMaximumLikelihoodEstimator M θhat) :
    IsMaximumLikelihoodEstimator (M.extendFromSetAt θ₀)
      (liftEstimatorFromSet θhat) := by
  intro n x θ
  by_cases hθ : θ ∈ Θ
  · simpa [sampleLikelihood, liftEstimatorFromSet,
      ParametricFamily.extendFromSetAt_density_of_mem, hθ] using
      hMLE n x ⟨θ, hθ⟩
  · calc
      sampleLikelihood (M.extendFromSetAt θ₀) θ n x =
          sampleLikelihood M θ₀ n x := by
            simp [sampleLikelihood,
              ParametricFamily.extendFromSetAt_density_of_not_mem, hθ]
      _ ≤ sampleLikelihood M (θhat n x) n x := hMLE n x θ₀
      _ = sampleLikelihood (M.extendFromSetAt θ₀)
          (liftEstimatorFromSet θhat n x) n x := by
            simp [sampleLikelihood, liftEstimatorFromSet]

/-- At an interior point, a local pairwise log-Lipschitz bound on `Θ`
transfers to the ambient extension after shrinking the radius.  The returned
radius is positive and no larger than the supplied neighborhood radius. -/
theorem exists_radius_extendFromSetAt_logDensity_lipschitz
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Θ : Set (EuclideanSpace ℝ (Fin d))}
    (M : ParametricFamily Ω Θ) (θ₀ : Θ) (menv : Ω → ℝ) (ρ : ℝ)
    -- The truth is an inner point of the book's parameter set.
    (hθ₀int : (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ interior Θ)
    -- The supplied likelihood neighborhood is nontrivial.
    (hρ : 0 < ρ)
    -- Pairwise local log-likelihood Lipschitz condition within `Θ`.
    (hLip : ∀ θ₁ : Θ,
      (θ₁ : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (θ₀ : EuclideanSpace ℝ (Fin d)) ρ →
      ∀ θ₂ : Θ,
        (θ₂ : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (θ₀ : EuclideanSpace ℝ (Fin d)) ρ →
        ∀ x,
          |M.logDensity θ₁ x - M.logDensity θ₂ x| ≤
            menv x * ‖(θ₁ : EuclideanSpace ℝ (Fin d)) - (θ₂ : EuclideanSpace ℝ (Fin d))‖) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧
      ∀ θ₁ ∈ Metric.closedBall (θ₀ : EuclideanSpace ℝ (Fin d)) r,
        ∀ θ₂ ∈ Metric.closedBall (θ₀ : EuclideanSpace ℝ (Fin d)) r, ∀ x,
          |(M.extendFromSetAt θ₀).logDensity θ₁ x -
              (M.extendFromSetAt θ₀).logDensity θ₂ x| ≤
            menv x * ‖θ₁ - θ₂‖ := by
  have hΘnhds : Θ ∈ 𝓝 (θ₀ : EuclideanSpace ℝ (Fin d)) :=
    mem_of_superset (isOpen_interior.mem_nhds hθ₀int) interior_subset
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hΘnhds
  let r := min ρ ε / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrρ : r ≤ ρ := by
    dsimp [r]
    nlinarith [min_le_left ρ ε]
  have hrε : r < ε := by
    dsimp [r]
    nlinarith [min_le_right ρ ε]
  refine ⟨r, hr, hrρ, ?_⟩
  intro θ₁ hθ₁ θ₂ hθ₂ x
  have hθ₁mem : θ₁ ∈ Θ :=
    hball (Metric.closedBall_subset_ball hrε hθ₁)
  have hθ₂mem : θ₂ ∈ Θ :=
    hball (Metric.closedBall_subset_ball hrε hθ₂)
  have hθ₁ρ : θ₁ ∈ Metric.closedBall (θ₀ : EuclideanSpace ℝ (Fin d)) ρ :=
    Metric.closedBall_subset_closedBall hrρ hθ₁
  have hθ₂ρ : θ₂ ∈ Metric.closedBall (θ₀ : EuclideanSpace ℝ (Fin d)) ρ :=
    Metric.closedBall_subset_closedBall hrρ hθ₂
  simpa [ParametricFamily.logDensity,
    ParametricFamily.extendFromSetAt_density_of_mem, hθ₁mem, hθ₂mem] using
    hLip ⟨θ₁, hθ₁mem⟩ hθ₁ρ ⟨θ₂, hθ₂mem⟩ hθ₂ρ x

end AsymptoticStatistics.MaximumLikelihood
