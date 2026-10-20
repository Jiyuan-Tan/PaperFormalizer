module
public import StatLean.AsymptoticStatistics.ClassicalZEstimator.RootExistence
public import StatLean.AsymptoticStatistics.ClassicalZEstimator.AsymptoticNormality
public import StatLean.AsymptoticStatistics.ForMathlib.SecondOrderCalculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

/-!
# Classical Z-estimator roots as local maxima (vdV Theorem 5.42, final assertion)

This file proves the final assertion of vdV Theorem 5.42 (§*5.6, book p. 69): if the
estimating function `ψ_θ = ṁ_θ` is the gradient of some
function `m_θ`, and `θ₀` is a point of local maximum of `θ ↦ Pm_θ`, then the consistent root
sequence `θ̂ₙ` produced by `RootExistence.classical_zEstimator_root_exists_consistent` can be
chosen to consist of **local maxima** of the empirical maps `θ ↦ ℙₙm_θ`.

## Proof route (vdV p.69)

The Hessian of `θ ↦ Pm_θ` at `θ₀` is `Pṁ̇_{θ₀} = Pψ̇_{θ₀} = V`, which is negative definite:
`θ₀` is a local maximum so `V` is negative semidefinite (`hessian_negSemidef_of_isLocalMax`),
and `V` is nonsingular by the 5.41 hypothesis, hence negative definite
(`V_negdef_of_localmax`). A Taylor expansion (as in the proof of Theorem 5.41) shows
the empirical Hessian `ℙₙψ̇_{θ̂ₙ}` at a consistent zero `θ̂ₙ` converges in probability to `V`,
so it is negative definite with probability tending to 1 (`empirical_hessian_negdef_wp1`).
At a critical point with a negative-definite Hessian the empirical criterion has a local
maximum (`ForMathlib.isLocalMax_of_negdef_hessian`).

The needed properties of the population Hessian follow from the assumptions: `V` is
symmetric because `ψ = ṁ` makes `ψ̇` a second derivative
(`psiDot_symm_of_grad` / `Vmat_isHermitian_of_grad`, equality of mixed partials), and the
second-order expansion of `θ ↦ P(m_θ − m_{θ₀})` comes from integrating the pointwise
expansion of `m` (`population_taylor2_m`). The same pointwise expansion, averaged over the
sample, supplies the Taylor hypothesis of `isLocalMax_of_negdef_hessian`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Topology RealInnerProductSpace Matrix

namespace AsymptoticStatistics.ClassicalZEstimator

open AsymptoticStatistics.EmpiricalProcess

/-- **Empirical Jacobian `ℙₙψ̇_θ`** (empirical Hessian of `θ ↦ ℙₙm_θ` when `ψ = ṁ`). Entry
`(j, i)` is the empirical average `ℙₙ ψ̇_{θ}(·)ⱼᵢ = (1/n)∑ₗ ψ̇_θ(Xₗ)ⱼᵢ`. Its negative
definiteness at a consistent root is established below. -/
noncomputable def empVmat {k : ℕ} {Ω : Type*}
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ) (Xs : Fin n → Ω) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun j i => empiricalAvg (fun x => psiDot ψ θ x j i) n Xs

/-! ### Euclidean and measure estimates

The Euclidean estimates compare coordinates, norms, and quadratic forms. The
measure estimate removes an outer-small bad event from a measurable inner
witness while preserving convergence to one in inner probability. -/

/-- Real Euclidean inner product in coordinates. -/
private lemma real_inner_euclid {k : ℕ} (v w : EuclideanSpace ℝ (Fin k)) :
    ⟪v, w⟫ = ∑ j, v j * w j := by
  have h := Matrix.inner_toEuclideanCLM (n := Fin k) 1 v w
  rw [map_one] at h
  simpa [dotProduct, Matrix.one_mulVec] using h

/-- A coordinate is dominated by the Euclidean norm. -/
private lemma coord_abs_le_norm {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (j : Fin k) :
    |x j| ≤ ‖x‖ := by
  have hnn : (0 : ℝ) ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h1 : |x j| ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
    have : ‖x j‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j)
    rwa [Real.norm_eq_abs] at this
  rw [EuclideanSpace.norm_eq]
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∑ i, ‖x i‖ ^ 2), abs_nonneg (x j)]

/-- Coordinate bound ⇒ Euclidean norm bound. -/
private lemma norm_le_of_coord_bound {k : ℕ} (y : EuclideanSpace ℝ (Fin k)) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ j, |y j| ≤ B) : ‖y‖ ≤ Real.sqrt k * B := by
  have hnorm_sq : ‖y‖ ^ 2 = ∑ j, |y j| ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => by positivity)]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs]
  have hsum : ∑ j, |y j| ^ 2 ≤ (k : ℝ) * B ^ 2 := by
    calc ∑ j, |y j| ^ 2 ≤ ∑ _j : Fin k, B ^ 2 :=
          Finset.sum_le_sum fun j _ => by nlinarith [h j, abs_nonneg (y j)]
      _ = (k : ℝ) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hC : (Real.sqrt k * B) ^ 2 = (k : ℝ) * B ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  nlinarith [norm_nonneg y, mul_nonneg (Real.sqrt_nonneg (k : ℝ)) hB, hnorm_sq, hsum, hC]

/-- Coordinates of `toEuclideanCLM M x`. -/
private lemma toEuclidCLM_coord {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin k)) (j : Fin k) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M x) j = ∑ i, M j i * x i := rfl

/-- The quadratic form of a matrix in coordinates. -/
private lemma inner_toEuclidCLM_quad {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (y : EuclideanSpace ℝ (Fin k)) :
    ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M y⟫
      = ∑ j, (∑ i, M j i * y i) * y j := by
  rw [Matrix.inner_toEuclideanCLM]
  simp [dotProduct, Matrix.mulVec, mul_comm]

/-- **Entrywise closeness ⇒ quadratic-form closeness.** If every entry of `M − V` is at most
`ζ` in absolute value, the quadratic form of `M` exceeds that of `V` by at most
`√k·k·ζ·‖x‖²`. This is the matrix-perturbation estimate used below. -/
private lemma inner_toEuclidCLM_pert {k : ℕ} (M V : Matrix (Fin k) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin k)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (h : ∀ j i, |M j i - V j i| ≤ ζ) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M x⟫
      ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V x⟫
        + Real.sqrt k * ((k : ℝ) * ζ) * ‖x‖ ^ 2 := by
  have hcoord : ∀ j, |(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M x
      - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V x) j| ≤ (k : ℝ) * ζ * ‖x‖ := by
    intro j
    have hj : (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M x
        - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V x) j
        = ∑ i, (M j i - V j i) * x i := by
      change (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M x) j
        - (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V x) j = _
      rw [toEuclidCLM_coord, toEuclidCLM_coord, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hj]
    calc |∑ i, (M j i - V j i) * x i| ≤ ∑ i, |(M j i - V j i) * x i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin k, ζ * ‖x‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (h j i) (coord_abs_le_norm x i) (abs_nonneg _) hζ
      _ = (k : ℝ) * ζ * ‖x‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M x
      - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V x‖
      ≤ Real.sqrt k * ((k : ℝ) * ζ) * ‖x‖ := by
    calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M x
          - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V x‖
        ≤ Real.sqrt k * ((k : ℝ) * ζ * ‖x‖) :=
          norm_le_of_coord_bound _ (by positivity) hcoord
      _ = Real.sqrt k * ((k : ℝ) * ζ) * ‖x‖ := by ring
  have hsplit : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M x⟫
      - ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V x⟫
      = ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M x
          - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V x⟫ := by
    rw [inner_sub_right]
  have hcs : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M x
      - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V x⟫
      ≤ ‖x‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M x
        - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V x‖ := real_inner_le_norm _ _
  nlinarith [norm_nonneg x, hnorm, hcs, hsplit]

/-- **Inner-probability-safe bad-event removal.** If `A n` contains a measurable inner witness
of probability tending to one, `μ.real (B n) → 0`, and `A n ∩ (B n)ᶜ ⊆ G n`, then `G n`
also has inner probability tending to one. The new witness removes the measurable hull
`toMeasurable μ (B n)` from the witness for `A n`; the hull has the same outer measure as
`B n`, so no measurability of `A`, `B`, or `G` is needed. -/
private lemma tendstoInnerProbOne_of_good {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (A B G : ℕ → Set Ξ)
    (hsub : ∀ n, A n ∩ (B n)ᶜ ⊆ G n)
    (hA : TendstoInnerProbOne μ A)
    (hB : Tendsto (fun n => μ.real (B n)) atTop (𝓝 0)) :
    TendstoInnerProbOne μ G := by
  obtain ⟨E, hEmeas, hEA, hElim⟩ := hA
  refine ⟨fun n => E n ∩ (toMeasurable μ (B n))ᶜ, ?_, ?_, ?_⟩
  · intro n
    exact (hEmeas n).inter (measurableSet_toMeasurable μ (B n)).compl
  · intro n ξ hξ
    refine hsub n ⟨hEA n hξ.1, ?_⟩
    intro hξB
    exact hξ.2 (subset_toMeasurable μ (B n) hξB)
  · have hlow : ∀ n, μ.real (E n) - μ.real (B n) ≤
        μ.real (E n ∩ (toMeasurable μ (B n))ᶜ) := by
      intro n
      have hcover : E n ⊆
          (E n ∩ (toMeasurable μ (B n))ᶜ) ∪ toMeasurable μ (B n) := by
        intro ξ hξ
        by_cases hb : ξ ∈ toMeasurable μ (B n)
        · exact Or.inr hb
        · exact Or.inl ⟨hξ, hb⟩
      have h1 : μ.real (E n) ≤ μ.real (E n ∩ (toMeasurable μ (B n))ᶜ)
          + μ.real (toMeasurable μ (B n)) :=
        (measureReal_mono hcover).trans (measureReal_union_le _ _)
      have hB_eq : μ.real (toMeasurable μ (B n)) = μ.real (B n) := by
        simp only [measureReal_def, measure_toMeasurable]
      linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hElim.sub hB)
      tendsto_const_nhds (Eventually.of_forall hlow)
      (Eventually.of_forall fun _ => measureReal_le_one)

/-! ### Symmetry of the Hessian `ψ̇_θ = m̈_θ`. -/

/-- **`ψ̇_θ(x)` is a symmetric matrix when `ψ_θ = ṁ_θ`.** If `ψ` is the gradient of `m`
(`hgrad`) and is `C¹` (implied by `hC2`), then `ψ̇_θ(x)` is the second derivative of
`θ' ↦ m_{θ'}(x)` at `θ`, hence symmetric by equality of mixed partials
(`second_derivative_symmetric_of_eventually`). This is what makes vdV's Hessian
`Pm̈_{θ₀} = Pψ̇_{θ₀}` symmetric, as the book's phrasing "the Hessian" presupposes. -/
theorem psiDot_symm_of_grad {k : ℕ} {Ω : Type*}
    (m : EuclideanSpace ℝ (Fin k) → Ω → ℝ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ_open : IsOpen Θ)
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ => ψ θ j x) Θ)
    (hgrad : ∀ θ ∈ Θ, ∀ x, HasFDerivAt (fun θ' => m θ' x) (innerSL ℝ (psiVec ψ θ x)) θ)
    (θ : EuclideanSpace ℝ (Fin k)) (hθ : θ ∈ Θ) (x : Ω) (j i : Fin k) :
    psiDot ψ θ x j i = psiDot ψ θ x i j := by
  classical
  set f' : EuclideanSpace ℝ (Fin k) → (EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) :=
    fun θ' => innerSL ℝ (psiVec ψ θ' x) with hf'_def
  -- `f'` is the derivative of `θ' ↦ m_{θ'}(x)` throughout the open set `Θ`.
  have hf : ∀ᶠ y in 𝓝 θ, HasFDerivAt (fun θ' => m θ' x) (f' y) y := by
    filter_upwards [hΘ_open.mem_nhds hθ] with y hy using hgrad y hy x
  -- Rewrite `f'` as a finite sum of `(scalar) • (constant functional)`, which exhibits its
  -- differentiability and its derivative.
  have hcoordfun : ∀ θ' : EuclideanSpace ℝ (Fin k),
      f' θ' = ∑ h : Fin k, (ψ θ' h x) • (innerSL ℝ (EuclideanSpace.single h (1 : ℝ))) := by
    intro θ'
    ext w
    rw [hf'_def]
    simp only [innerSL_apply_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rw [real_inner_euclid]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [real_inner_euclid]
    simp [psiVec, EuclideanSpace.single, PiLp.single_apply, Finset.sum_ite_eq']
  have hf'_sum : f' = ∑ h : Fin k, (fun θ' : EuclideanSpace ℝ (Fin k) =>
      (ψ θ' h x) • (innerSL ℝ (EuclideanSpace.single h (1 : ℝ)))) := by
    funext θ'
    rw [Finset.sum_apply]
    exact hcoordfun θ'
  have hψdiff : ∀ h : Fin k, DifferentiableAt ℝ (fun θ' => ψ θ' h x) θ := fun h =>
    ((hC2 h x).differentiableOn (by norm_num)).differentiableAt (hΘ_open.mem_nhds hθ)
  set F : EuclideanSpace ℝ (Fin k) →L[ℝ] (EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) :=
    ∑ h : Fin k, (fderiv ℝ (fun θ' => ψ θ' h x) θ).smulRight
      (innerSL ℝ (EuclideanSpace.single h (1 : ℝ))) with hF_def
  have hF : HasFDerivAt f' F θ := by
    rw [hf'_sum, hF_def]
    exact HasFDerivAt.sum fun h _ =>
      (hψdiff h).hasFDerivAt.smul_const (innerSL ℝ (EuclideanSpace.single h (1 : ℝ)))
  -- The second derivative in coordinates.
  have hFapply : ∀ (v w : EuclideanSpace ℝ (Fin k)),
      F v w = ∑ h : Fin k, (fderiv ℝ (fun θ' => ψ θ' h x) θ v) * w h := by
    intro v w
    rw [hF_def]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [real_inner_euclid]
    simp [EuclideanSpace.single, PiLp.single_apply, Finset.sum_ite_eq']
  have hkey := second_derivative_symmetric_of_eventually (𝕜 := ℝ) hf hF
    (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
  rw [hFapply, hFapply] at hkey
  have hL : ∑ h : Fin k, (fderiv ℝ (fun θ' => ψ θ' h x) θ (EuclideanSpace.single i (1 : ℝ)))
      * (EuclideanSpace.single j (1 : ℝ)) h = psiDot ψ θ x j i := by
    simp [psiDot, EuclideanSpace.single, PiLp.single_apply, Finset.sum_ite_eq']
  have hR : ∑ h : Fin k, (fderiv ℝ (fun θ' => ψ θ' h x) θ (EuclideanSpace.single j (1 : ℝ)))
      * (EuclideanSpace.single i (1 : ℝ)) h = psiDot ψ θ x i j := by
    simp [psiDot, EuclideanSpace.single, PiLp.single_apply, Finset.sum_ite_eq']
  rw [hL, hR] at hkey
  exact hkey

/-- **`V = Pψ̇_{θ₀}` is symmetric.** Integrating `psiDot_symm_of_grad`. -/
theorem Vmat_isHermitian_of_grad {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (m : EuclideanSpace ℝ (Fin k) → Ω → ℝ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ_open : IsOpen Θ)
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ => ψ θ j x) Θ)
    (hgrad : ∀ θ ∈ Θ, ∀ x, HasFDerivAt (fun θ' => m θ' x) (innerSL ℝ (psiVec ψ θ x)) θ)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ ∈ Θ) :
    (Vmat P ψ θ₀).IsHermitian := by
  ext j i
  simp only [Matrix.conjTranspose_apply, star_trivial, Vmat, Matrix.of_apply]
  exact integral_congr_ae (Eventually.of_forall fun x =>
    psiDot_symm_of_grad m ψ Θ hΘ_open hC2 hgrad θ₀ hθ₀ x i j)

/-! ### The population Hessian `V` is negative definite -/

/-- **The population Hessian `V = Pṁ̇_{θ₀}` is negative definite.** Since `θ₀` is a local maximum of
`θ ↦ P(m_θ − m_{θ₀})` with second-order Hessian `V = Vmat P ψ θ₀` (`hTaylorPop`), the
second-order necessary condition (`hessian_negSemidef_of_isLocalMax`) makes `V` negative
semidefinite; being symmetric (`hVsymm`, from `ψ = ṁ`) and nonsingular (`hV`), it is negative
definite: `∃ c > 0, ∀ x, ⟪x, Vx⟫ ≤ −c‖x‖²`. vdV p.69 "the Hessian `Pṁ̇_{θ₀}` of `θ ↦ Pm_θ` at
`θ₀` is negative definite, by assumption." -/
theorem V_negdef_of_localmax {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin k) → Ω → ℝ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (hVsymm : (Vmat P ψ θ₀).IsHermitian)
    (hmax : IsLocalMax (fun θ => ∫ x, (m θ x - m θ₀ x) ∂P) θ₀)
    (hTaylorPop : Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ => (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
            (Vmat P ψ θ₀) (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2))
    (hV : IsUnit (Vmat P ψ θ₀).det) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : EuclideanSpace ℝ (Fin k),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x⟫ ≤ - c * ‖x‖ ^ 2 := by
  -- **Step 1** (second-order necessary condition at an interior local maximum): `V` is
  -- negative *semi*definite.  `hTaylorPop` is already in the brick's shape once one notes
  -- that the difference criterion vanishes at `θ₀`.
  have hNSD : ∀ x : EuclideanSpace ℝ (Fin k),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x⟫ ≤ 0 := by
    refine hessian_negSemidef_of_isLocalMax
      (fun θ => ∫ x, (m θ x - m θ₀ x) ∂P) θ₀ (Vmat P ψ θ₀) hmax ?_
    simpa only [sub_self, integral_zero, sub_zero] using hTaylorPop
  -- **Step 2a**: `V` is symmetric (real Hermitian), so `(x, y) ↦ ⟪x, Vy⟫` is a symmetric
  -- bilinear form.
  have hVT : (Vmat P ψ θ₀)ᵀ = Vmat P ψ θ₀ := by
    ext i j
    simpa using hVsymm.apply i j
  have hvm : ∀ z : Fin k → ℝ, z ᵥ* Vmat P ψ θ₀ = Vmat P ψ θ₀ *ᵥ z := by
    intro z
    conv_lhs => rw [← hVT]
    exact Matrix.vecMul_transpose _ _
  have hsymm : ∀ x y : EuclideanSpace ℝ (Fin k),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) y⟫
        = ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x⟫ := by
    intro x y
    rw [Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM, Matrix.dotProduct_mulVec,
      hvm, dotProduct_comm]
  -- **Step 2b**: on a negative semidefinite *symmetric* form, a null vector of the quadratic
  -- form lies in the kernel.  Perturbation form of Cauchy–Schwarz: if `⟪x, Vx⟫ = 0` then
  -- `t ↦ ⟪x + t·y, V(x + t·y)⟫ = 2t⟪y, Vx⟫ + t²⟪y, Vy⟫ ≤ 0` has no constant term, so its
  -- linear coefficient must vanish (else a small `t` of the right sign makes it positive).
  have hker : ∀ x : EuclideanSpace ℝ (Fin k),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x⟫ = 0 →
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x = 0 := by
    intro x hx
    have hall : ∀ y : EuclideanSpace ℝ (Fin k),
        ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x⟫ = 0 := by
      intro y
      set a : ℝ := ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x⟫ with ha
      set b : ℝ := ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) y⟫ with hb
      have hb0 : b ≤ 0 := hNSD y
      have hquad : ∀ t : ℝ, 2 * t * a + t ^ 2 * b ≤ 0 := by
        intro t
        have h := hNSD (x + t • y)
        have hexp : ⟪x + t • y, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
              (Vmat P ψ θ₀) (x + t • y)⟫
            = ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x⟫
              + t * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) y⟫
              + t * a + t ^ 2 * b := by
          rw [ha, hb]
          simp only [map_add, map_smul, inner_add_left, inner_add_right,
            real_inner_smul_left, real_inner_smul_right]
          ring
        rw [hexp, hx, hsymm x y] at h
        linarith
      by_contra hy
      have ha2 : 0 < a ^ 2 := by positivity
      obtain ⟨s, hspos, hsb⟩ : ∃ s : ℝ, 0 < s ∧ s * (-b) < 2 := by
        have habs : (0 : ℝ) < |b| + 1 := by positivity
        refine ⟨1 / (|b| + 1), by positivity, ?_⟩
        have h1 : -b ≤ |b| := neg_le_abs b
        rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ habs]
        linarith
      have hkey := hquad (a * s)
      nlinarith [hkey, mul_pos (mul_pos ha2 hspos) (show (0 : ℝ) < 2 + s * b by linarith)]
    exact inner_self_eq_zero.mp
      (hall (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x))
  -- **Step 2c**: nonsingularity turns "negative semidefinite with trivial kernel" into
  -- strict negativity off the origin.
  have hdet : (Vmat P ψ θ₀).det ≠ 0 := hV.ne_zero
  have hND : ∀ x : EuclideanSpace ℝ (Fin k), x ≠ 0 →
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x⟫ < 0 := by
    intro x hx
    rcases (hNSD x).lt_or_eq with h | h
    · exact h
    · refine absurd ?_ hx
      have hmv : Vmat P ψ θ₀ *ᵥ (WithLp.ofLp x) = 0 := by
        simpa [Matrix.ofLp_toEuclideanCLM] using congrArg WithLp.ofLp (hker x h)
      have := Matrix.eq_zero_of_mulVec_eq_zero hdet hmv
      ext i
      simpa using congrFun this i
  -- **Step 3**: a uniform constant by compactness of the unit sphere, plus homogeneity.
  by_cases hk : k = 0
  · -- Degenerate ambient space: the sphere is empty, but every vector is `0`.
    subst hk
    refine ⟨1, one_pos, fun x => ?_⟩
    have hx0 : x = 0 := by ext i; exact i.elim0
    simp [hx0]
  · have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1).Nonempty := by
      have : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk)
      exact NormedSpace.sphere_nonempty.mpr zero_le_one
    have hcont : Continuous fun x : EuclideanSpace ℝ (Fin k) =>
        ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x⟫ := by
      fun_prop
    obtain ⟨x₀, hx₀mem, hx₀max⟩ :=
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin k)) 1).exists_isMaxOn hne hcont.continuousOn
    have hx₀ne : x₀ ≠ 0 := by
      rintro rfl
      simp at hx₀mem
    refine ⟨-⟪x₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x₀⟫,
      neg_pos.mpr (hND x₀ hx₀ne), fun x => ?_⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have hnpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
      have hmem : (‖x‖⁻¹ : ℝ) • x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 := by
        rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hnpos), inv_mul_cancel₀ hnpos.ne']
      have hle := (isMaxOn_iff.mp hx₀max) _ hmem
      have hscale : ⟪(‖x‖⁻¹ : ℝ) • x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
            (Vmat P ψ θ₀) ((‖x‖⁻¹ : ℝ) • x)⟫
          = (‖x‖⁻¹) ^ 2
              * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x⟫ := by
        rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
      rw [hscale] at hle
      have hinv : ‖x‖ ^ 2 * (‖x‖⁻¹) ^ 2 = 1 := by field_simp
      have hstep := mul_le_mul_of_nonneg_left hle (sq_nonneg ‖x‖)
      rw [← mul_assoc, hinv, one_mul] at hstep
      linarith

/-! ### Second-order Taylor expansion of the criterion `m` (cubic remainder).

vdV's proof of the final assertion of Theorem 5.42 needs the criterion `θ ↦ ℙₙm_θ` (and its
population analogue `θ ↦ Pm_θ`) to admit a second-order Taylor expansion with Hessian
`ℙₙψ̇_θ` (resp. `Pψ̇_{θ₀}`). Since `ψ = ṁ` is `C¹` with second derivative dominated by the
integrable `ψ̈`, integrating the first-order Taylor bound for `ψ` along the segment
gives a remainder of order `ψ̈(x)‖θ − t‖³`, uniformly in `x`. That uniformity is what lets the
bound survive both the empirical average and the `P`-integral. -/

/-- **Pointwise second-order Taylor expansion of `m` with cubic remainder.** For `t` and `θ`
in the ball of radius `ρ/4` around `θ₀` (so that a ball around `t` large enough to contain
the segment still lies inside the domination ball),

    `|m_θ(x) − m_t(x) − ⟨ψ_t(x), θ − t⟩ − ½⟨θ − t, ψ̇_t(x)(θ − t)⟩| ≤ (k/2) ψ̈(x) ‖θ − t‖³`.

Route: differentiate along the segment `s ↦ m_{t + s(θ−t)}(x)`, whose derivative is
`⟨ψ_{t+s(θ−t)}(x), θ − t⟩` by `hgrad`; subtract the first two terms of its own expansion and
bound the resulting derivative by `pointwise_taylor_bound` applied at the centre
`t`; finish with the mean-value inequality on `[0, 1]`. -/
theorem pointwise_taylor2_m {k : ℕ} {Ω : Type*}
    (m : EuclideanSpace ℝ (Fin k) → Ω → ℝ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (Θ : Set (EuclideanSpace ℝ (Fin k)))
    (ψddot : Ω → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hΘ_open : IsOpen Θ) (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ => ψ θ j x) Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x)
    (hgrad : ∀ θ ∈ Θ, ∀ x, HasFDerivAt (fun θ' => m θ' x) (innerSL ℝ (psiVec ψ θ x)) θ) :
    ∀ t ∈ Metric.closedBall θ₀ (ρ / 4), ∀ θ ∈ Metric.closedBall θ₀ (ρ / 4), ∀ x : Ω,
      |m θ x - m t x - (∑ j, ψ t j x * (θ - t) j)
          - 1 / 2 * ∑ j, (∑ i, psiDot ψ t x j i * (θ - t) i) * (θ - t) j|
        ≤ (k : ℝ) / 2 * ψddot x * ‖θ - t‖ ^ 3 := by
  classical
  intro t ht θ hθ x
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hzero : θ = t := by ext i; exact i.elim0
    simp [hzero]
  have hψd : 0 ≤ ψddot x :=
    le_trans (norm_nonneg _) (hdom θ₀ (Metric.mem_closedBall_self hρ.le) ⟨0, hk⟩ x)
  have htn : ‖t - θ₀‖ ≤ ρ / 4 := by
    simpa [dist_eq_norm] using Metric.mem_closedBall.mp ht
  have hθn : ‖θ - θ₀‖ ≤ ρ / 4 := by
    simpa [dist_eq_norm] using Metric.mem_closedBall.mp hθ
  set v : EuclideanSpace ℝ (Fin k) := θ - t with hv
  have hvn : ‖v‖ ≤ ρ / 2 := by
    have hsplit : v = (θ - θ₀) - (t - θ₀) := by rw [hv]; abel
    calc ‖v‖ ≤ ‖θ - θ₀‖ + ‖t - θ₀‖ := by rw [hsplit]; exact norm_sub_le _ _
      _ ≤ ρ / 2 := by linarith
  set r : ℝ := ‖v‖ + ρ / 4 with hr
  have hrpos : 0 < r := by rw [hr]; have := norm_nonneg v; linarith
  have hsubball : Metric.closedBall t r ⊆ Metric.closedBall θ₀ ρ := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    calc dist z θ₀ ≤ dist z t + dist t θ₀ := dist_triangle _ _ _
      _ ≤ r + ρ / 4 := add_le_add hz (by rw [dist_eq_norm]; exact htn)
      _ ≤ ρ := by rw [hr]; linarith
  -- The pointwise Taylor bound centred at `t`, valid on the ball of radius `r`.
  have hB := pointwise_taylor_bound ψ t Θ ψddot hrpos hΘ_open (hsubball.trans hball) hC2
    (fun z hz => hdom z (hsubball hz))
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, t + s • v ∈ Metric.closedBall t r := by
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs.1]
    calc s * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ = ‖v‖ := one_mul _
      _ ≤ r := by rw [hr]; linarith
  set Lin : ℝ := ∑ j, ψ t j x * v j with hLin
  set Q : ℝ := ∑ j, (∑ i, psiDot ψ t x j i * v i) * v j with hQ
  set u : ℝ → ℝ := fun s => m (t + s • v) x - m t x - s * Lin - s ^ 2 / 2 * Q with hu
  set D : ℝ → ℝ := fun s => (∑ j, ψ (t + s • v) j x * v j) - Lin - s * Q with hD
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (D s) s := by
    intro s hs
    have hγ : HasDerivAt (fun s' : ℝ => t + s' • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add t
    have h1 : HasDerivAt (fun s' : ℝ => m (t + s' • v) x)
        ((innerSL ℝ (psiVec ψ (t + s • v) x)) v) s := by
      simpa [Function.comp_def] using
        (hgrad (t + s • v) (hball (hsubball (hseg s hs))) x).comp_hasDerivAt s hγ
    have hval : (innerSL ℝ (psiVec ψ (t + s • v) x)) v = ∑ j, ψ (t + s • v) j x * v j := by
      rw [innerSL_apply_apply, real_inner_euclid]
      exact Finset.sum_congr rfl fun j _ => by simp [psiVec]
    rw [hval] at h1
    have h2 : HasDerivAt (fun s' : ℝ => s' * Lin) Lin s := by
      simpa using (hasDerivAt_id s).mul_const Lin
    have h3 : HasDerivAt (fun s' : ℝ => s' ^ 2 / 2 * Q) (s * Q) s := by
      have h0 : HasDerivAt (fun s' : ℝ => s' ^ 2 / 2) s s := by
        simpa using (hasDerivAt_pow 2 s).div_const 2
      simpa using h0.mul_const Q
    exact ((h1.sub_const (m t x)).sub h2).sub h3
  set C : ℝ := (k : ℝ) / 2 * ψddot x * ‖v‖ ^ 3 with hC
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖D s‖ ≤ C := by
    intro s hs
    have hcoord : ∀ i : Fin k, (t + s • v - t) i = s * v i := by
      intro i; simp [add_sub_cancel_left]
    have hrw : D s = ∑ j, (ψ (t + s • v) j x - ψ t j x
        - ∑ i, psiDot ψ t x j i * (t + s • v - t) i) * v j := by
      have hstep : ∀ j : Fin k, (ψ (t + s • v) j x - ψ t j x
          - ∑ i, psiDot ψ t x j i * (t + s • v - t) i) * v j
          = ψ (t + s • v) j x * v j - ψ t j x * v j
            - s * ((∑ i, psiDot ψ t x j i * v i) * v j) := by
        intro j
        simp only [hcoord]
        have hs' : ∑ i, psiDot ψ t x j i * (s * v i) = s * ∑ i, psiDot ψ t x j i * v i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hs']
        ring
      rw [hD, hLin, hQ]
      simp only [hstep]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hnv : ‖t + s • v - t‖ ≤ ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc s * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ = ‖v‖ := one_mul _
    have hterm : ∀ j : Fin k, |(ψ (t + s • v) j x - ψ t j x
        - ∑ i, psiDot ψ t x j i * (t + s • v - t) i) * v j|
        ≤ 1 / 2 * ψddot x * ‖v‖ ^ 2 * ‖v‖ := by
      intro j
      rw [abs_mul]
      have hb := hB (t + s • v) (hseg s hs) j x
      have hb2 : |ψ (t + s • v) j x - ψ t j x
          - ∑ i, psiDot ψ t x j i * (t + s • v - t) i| ≤ 1 / 2 * ψddot x * ‖v‖ ^ 2 := by
        refine hb.trans ?_
        have hsq : ‖t + s • v - t‖ ^ 2 ≤ ‖v‖ ^ 2 := by
          nlinarith [norm_nonneg (t + s • v - t), norm_nonneg v, hnv]
        nlinarith [hψd]
      exact mul_le_mul hb2 (coord_abs_le_norm v j) (abs_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, hrw]
    calc |∑ j, (ψ (t + s • v) j x - ψ t j x
            - ∑ i, psiDot ψ t x j i * (t + s • v - t) i) * v j|
        ≤ ∑ j, |(ψ (t + s • v) j x - ψ t j x
            - ∑ i, psiDot ψ t x j i * (t + s • v - t) i) * v j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin k, 1 / 2 * ψddot x * ‖v‖ ^ 2 * ‖v‖ := Finset.sum_le_sum fun j _ => hterm j
      _ = C := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hC]; ring
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := u) (f' := D) (s := Set.Icc (0 : ℝ) 1) (C := C)
    (fun s hs => (hderiv s hs).hasDerivWithinAt) hbound (convex_Icc 0 1)
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
  have hu0 : u 0 = 0 := by simp [hu]
  have hu1 : u 1 = m θ x - m t x - Lin - 1 / 2 * Q := by
    have hone : t + (1 : ℝ) • v = θ := by rw [hv]; simp
    rw [hu]
    simp only [hone, one_pow, one_mul]
  rw [hu0, hu1, sub_zero, Real.norm_eq_abs] at hmv
  have hfin : |m θ x - m t x - Lin - 1 / 2 * Q| ≤ C := by
    simpa using hmv
  rw [hC] at hfin
  exact hfin

/-- **Empirical second-order Taylor expansion of `m`.** Averaging `pointwise_taylor2_m`
(supplied as `hbound2`) over a sample: the empirical criterion `θ ↦ ℙₙm_θ` expands around any
`t` in the ball with gradient `ℙₙψ_t` and Hessian `empVmat ψ t n Xs = ℙₙψ̇_t`, with remainder
`(k/2)(ℙₙψ̈)‖θ − t‖³`. -/
theorem empirical_taylor2_m {k : ℕ} {Ω : Type*}
    (m : EuclideanSpace ℝ (Fin k) → Ω → ℝ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (ψddot : Ω → ℝ) {ρ : ℝ}
    (hbound2 : ∀ t ∈ Metric.closedBall θ₀ (ρ / 4), ∀ θ ∈ Metric.closedBall θ₀ (ρ / 4),
      ∀ x : Ω, |m θ x - m t x - (∑ j, ψ t j x * (θ - t) j)
          - 1 / 2 * ∑ j, (∑ i, psiDot ψ t x j i * (θ - t) i) * (θ - t) j|
        ≤ (k : ℝ) / 2 * ψddot x * ‖θ - t‖ ^ 3)
    (n : ℕ) (Xs : Fin n → Ω) :
    ∀ t ∈ Metric.closedBall θ₀ (ρ / 4), ∀ θ ∈ Metric.closedBall θ₀ (ρ / 4),
      |empiricalAvg (m θ) n Xs - empiricalAvg (m t) n Xs
          - (∑ j, empiricalAvg (ψ t j) n Xs * (θ - t) j)
          - 1 / 2 * ∑ j, (∑ i, empVmat ψ t n Xs j i * (θ - t) i) * (θ - t) j|
        ≤ (k : ℝ) / 2 * empiricalAvg ψddot n Xs * ‖θ - t‖ ^ 3 := by
  classical
  intro t ht θ hθ
  have hA : empiricalAvg (m θ) n Xs - empiricalAvg (m t) n Xs
      = (n : ℝ)⁻¹ * ∑ l, (m θ (Xs l) - m t (Xs l)) := by
    simp only [empiricalAvg, Finset.sum_sub_distrib, mul_sub]
  have hBb : ∑ j, empiricalAvg (ψ t j) n Xs * (θ - t) j
      = (n : ℝ)⁻¹ * ∑ l, ∑ j, ψ t j (Xs l) * (θ - t) j := by
    calc ∑ j, empiricalAvg (ψ t j) n Xs * (θ - t) j
        = ∑ j, (n : ℝ)⁻¹ * ∑ l, ψ t j (Xs l) * (θ - t) j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [empiricalAvg]
          rw [mul_assoc, Finset.sum_mul]
      _ = (n : ℝ)⁻¹ * ∑ j, ∑ l, ψ t j (Xs l) * (θ - t) j := by rw [← Finset.mul_sum]
      _ = (n : ℝ)⁻¹ * ∑ l, ∑ j, ψ t j (Xs l) * (θ - t) j := by rw [Finset.sum_comm]
  have hCc : ∑ j, (∑ i, empVmat ψ t n Xs j i * (θ - t) i) * (θ - t) j
      = (n : ℝ)⁻¹ * ∑ l, ∑ j, (∑ i, psiDot ψ t (Xs l) j i * (θ - t) i) * (θ - t) j := by
    have hentry : ∀ j : Fin k, ∑ i, empVmat ψ t n Xs j i * (θ - t) i
        = (n : ℝ)⁻¹ * ∑ l, ∑ i, psiDot ψ t (Xs l) j i * (θ - t) i := by
      intro j
      calc ∑ i, empVmat ψ t n Xs j i * (θ - t) i
          = ∑ i, (n : ℝ)⁻¹ * ∑ l, psiDot ψ t (Xs l) j i * (θ - t) i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [empVmat, Matrix.of_apply, empiricalAvg]
            rw [mul_assoc, Finset.sum_mul]
        _ = (n : ℝ)⁻¹ * ∑ i, ∑ l, psiDot ψ t (Xs l) j i * (θ - t) i := by rw [← Finset.mul_sum]
        _ = (n : ℝ)⁻¹ * ∑ l, ∑ i, psiDot ψ t (Xs l) j i * (θ - t) i := by rw [Finset.sum_comm]
    calc ∑ j, (∑ i, empVmat ψ t n Xs j i * (θ - t) i) * (θ - t) j
        = ∑ j, (n : ℝ)⁻¹ * ∑ l, (∑ i, psiDot ψ t (Xs l) j i * (θ - t) i) * (θ - t) j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hentry j, mul_assoc, Finset.sum_mul]
      _ = (n : ℝ)⁻¹ * ∑ j, ∑ l, (∑ i, psiDot ψ t (Xs l) j i * (θ - t) i) * (θ - t) j := by
          rw [← Finset.mul_sum]
      _ = (n : ℝ)⁻¹ * ∑ l, ∑ j, (∑ i, psiDot ψ t (Xs l) j i * (θ - t) i) * (θ - t) j := by
          rw [Finset.sum_comm]
  have hsplit : ∑ l, (m θ (Xs l) - m t (Xs l) - (∑ j, ψ t j (Xs l) * (θ - t) j)
        - 1 / 2 * ∑ j, (∑ i, psiDot ψ t (Xs l) j i * (θ - t) i) * (θ - t) j)
      = (∑ l, (m θ (Xs l) - m t (Xs l))) - (∑ l, ∑ j, ψ t j (Xs l) * (θ - t) j)
        - 1 / 2 * ∑ l, ∑ j, (∑ i, psiDot ψ t (Xs l) j i * (θ - t) i) * (θ - t) j := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hrw : empiricalAvg (m θ) n Xs - empiricalAvg (m t) n Xs
        - (∑ j, empiricalAvg (ψ t j) n Xs * (θ - t) j)
        - 1 / 2 * ∑ j, (∑ i, empVmat ψ t n Xs j i * (θ - t) i) * (θ - t) j
      = (n : ℝ)⁻¹ * ∑ l, (m θ (Xs l) - m t (Xs l) - (∑ j, ψ t j (Xs l) * (θ - t) j)
          - 1 / 2 * ∑ j, (∑ i, psiDot ψ t (Xs l) j i * (θ - t) i) * (θ - t) j) := by
    rw [hsplit, hA, hBb, hCc]; ring
  have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  rw [hrw, abs_mul, abs_of_nonneg hinv]
  calc (n : ℝ)⁻¹ * |∑ l, (m θ (Xs l) - m t (Xs l) - (∑ j, ψ t j (Xs l) * (θ - t) j)
          - 1 / 2 * ∑ j, (∑ i, psiDot ψ t (Xs l) j i * (θ - t) i) * (θ - t) j)|
      ≤ (n : ℝ)⁻¹ * ∑ l, ((k : ℝ) / 2 * ψddot (Xs l) * ‖θ - t‖ ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ hinv
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun l _ => hbound2 t ht θ hθ (Xs l))
    _ = (k : ℝ) / 2 * empiricalAvg ψddot n Xs * ‖θ - t‖ ^ 3 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        simp only [empiricalAvg]
        ring

/-- **Population second-order Taylor expansion of `m`.** Integrating `pointwise_taylor2_m`
(supplied as `hbound2`) against `P`: `θ ↦ P(m_θ − m_{θ₀})` expands around `θ₀` with gradient
`Pψ_{θ₀}` and Hessian `V = Pψ̇_{θ₀}`, and cubic remainder `(k/2)(Pψ̈)‖θ − θ₀‖³`. The
integrability of `m_θ − m_{θ₀}` is **derived** from the expansion, not assumed. -/
theorem population_taylor2_m {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (m : EuclideanSpace ℝ (Fin k) → Ω → ℝ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (ψddot : Ω → ℝ) {ρ : ℝ}
    (hbound2 : ∀ θ ∈ Metric.closedBall θ₀ (ρ / 4), ∀ x : Ω,
      |m θ x - m θ₀ x - (∑ j, ψ θ₀ j x * (θ - θ₀) j)
          - 1 / 2 * ∑ j, (∑ i, psiDot ψ θ₀ x j i * (θ - θ₀) i) * (θ - θ₀) j|
        ≤ (k : ℝ) / 2 * ψddot x * ‖θ - θ₀‖ ^ 3)
    (hm_meas : ∀ θ, Measurable (m θ))
    (hψint : ∀ j, Integrable (ψ θ₀ j) P)
    (hVint : ∀ j i, Integrable (fun x => psiDot ψ θ₀ x j i) P)
    (hψddot_int : Integrable ψddot P) :
    ∀ θ ∈ Metric.closedBall θ₀ (ρ / 4),
      |(∫ x, (m θ x - m θ₀ x) ∂P) - (∑ j, (∫ x, ψ θ₀ j x ∂P) * (θ - θ₀) j)
          - 1 / 2 * ∑ j, (∑ i, Vmat P ψ θ₀ j i * (θ - θ₀) i) * (θ - θ₀) j|
        ≤ (k : ℝ) / 2 * (∫ x, ψddot x ∂P) * ‖θ - θ₀‖ ^ 3 := by
  classical
  intro θ hθ
  set v : EuclideanSpace ℝ (Fin k) := θ - θ₀ with hv
  set L : Ω → ℝ := fun x => (∑ j, ψ θ₀ j x * v j)
    + 1 / 2 * ∑ j, (∑ i, psiDot ψ θ₀ x j i * v i) * v j with hL
  set R : Ω → ℝ := fun x => m θ x - m θ₀ x - L x with hR
  -- Integrability of the linear-plus-quadratic part.
  have hLint : Integrable L P := by
    refine Integrable.add (integrable_finset_sum _ fun j _ => (hψint j).mul_const _) ?_
    refine Integrable.const_mul ?_ _
    exact integrable_finset_sum _ fun j _ =>
      ((integrable_finset_sum _ fun i _ => (hVint j i).mul_const _)).mul_const _
  -- Integrability of the remainder, from the cubic bound.
  have hgint : Integrable (fun x => (k : ℝ) / 2 * ψddot x * ‖v‖ ^ 3) P :=
    (hψddot_int.const_mul _).mul_const _
  have hRmeas : AEStronglyMeasurable R P := by
    have h1 : AEStronglyMeasurable (fun x => m θ x - m θ₀ x) P :=
      ((hm_meas θ).sub (hm_meas θ₀)).aestronglyMeasurable
    exact h1.sub hLint.aestronglyMeasurable
  have hRint : Integrable R P := by
    refine hgint.mono' hRmeas (Eventually.of_forall fun x => ?_)
    have hb := hbound2 θ hθ x
    rw [Real.norm_eq_abs, hR, hL]
    calc |m θ x - m θ₀ x - ((∑ j, ψ θ₀ j x * v j)
            + 1 / 2 * ∑ j, (∑ i, psiDot ψ θ₀ x j i * v i) * v j)|
        = |m θ x - m θ₀ x - (∑ j, ψ θ₀ j x * v j)
            - 1 / 2 * ∑ j, (∑ i, psiDot ψ θ₀ x j i * v i) * v j| := by ring_nf
      _ ≤ (k : ℝ) / 2 * ψddot x * ‖v‖ ^ 3 := hb
  have hmint : Integrable (fun x => m θ x - m θ₀ x) P := by
    have : (fun x => m θ x - m θ₀ x) = fun x => R x + L x := by
      funext x; rw [hR]; ring
    rw [this]
    exact hRint.add hLint
  -- Split the integral.
  have hLval : ∫ x, L x ∂P = (∑ j, (∫ x, ψ θ₀ j x ∂P) * v j)
      + 1 / 2 * ∑ j, (∑ i, Vmat P ψ θ₀ j i * v i) * v j := by
    rw [hL]
    rw [integral_add (integrable_finset_sum _ fun j _ => (hψint j).mul_const _)
      (Integrable.const_mul (integrable_finset_sum _ fun j _ =>
        ((integrable_finset_sum _ fun i _ => (hVint j i).mul_const _)).mul_const _) _)]
    congr 1
    · rw [integral_finset_sum _ fun j _ => (hψint j).mul_const _]
      exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
    · rw [integral_const_mul,
        integral_finset_sum _ fun j _ =>
          ((integrable_finset_sum _ fun i _ => (hVint j i).mul_const _)).mul_const _]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_mul_const,
        integral_finset_sum _ fun i _ => (hVint j i).mul_const _]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by
        rw [integral_mul_const]; rfl
  have hRval : ∫ x, R x ∂P = (∫ x, (m θ x - m θ₀ x) ∂P)
      - (∑ j, (∫ x, ψ θ₀ j x ∂P) * v j)
      - 1 / 2 * ∑ j, (∑ i, Vmat P ψ θ₀ j i * v i) * v j := by
    rw [hR, integral_sub hmint hLint, hLval]; ring
  rw [← hRval]
  calc |∫ x, R x ∂P| ≤ ∫ x, |R x| ∂P := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := P) (f := R)
    _ ≤ ∫ x, (k : ℝ) / 2 * ψddot x * ‖v‖ ^ 3 ∂P := by
        refine integral_mono hRint.abs hgint fun x => ?_
        have hb := hbound2 θ hθ x
        rw [hR, hL]
        calc |m θ x - m θ₀ x - ((∑ j, ψ θ₀ j x * v j)
                + 1 / 2 * ∑ j, (∑ i, psiDot ψ θ₀ x j i * v i) * v j)|
            = |m θ x - m θ₀ x - (∑ j, ψ θ₀ j x * v j)
                - 1 / 2 * ∑ j, (∑ i, psiDot ψ θ₀ x j i * v i) * v j| := by ring_nf
          _ ≤ (k : ℝ) / 2 * ψddot x * ‖v‖ ^ 3 := hb
    _ = (k : ℝ) / 2 * (∫ x, ψddot x ∂P) * ‖v‖ ^ 3 := by
        rw [integral_mul_const, integral_const_mul]

/-! ### The empirical Hessian is negative definite with probability tending to one -/

/-- **Bad-event form for the empirical Hessian.** The set on which the empirical Hessian at
the consistent zero `θ̂ₙ` fails to satisfy the *uniform* negative-definiteness bound
`⟪x, ℙₙψ̇_{θ̂ₙ} x⟫ ≤ −(c/2)‖x‖²` has outer measure tending to `0`.

This form carries the uniform constant `c/2` needed by
`isLocalMax_of_negdef_hessian`, and it is stated on the *bad* event so that it can be
intersected with other high-probability events without any measurability assumption on
`θ̂ₙ` (only subadditivity of the outer measure is required).

Route (vdV p.69): `ℙₙψ̇_{θ̂ₙ} − V = (ℙₙψ̇_{θ̂ₙ} − ℙₙψ̇_{θ₀}) + (ℙₙψ̇_{θ₀} − V)`. The second
bracket is `o_P(1)` entrywise by the law of large numbers; the first is bounded by
`(ℙₙψ̈)‖θ̂ₙ − θ₀‖ = O_P(1)·o_P(1)` by the Lipschitz bound `psiDot_lipschitz` averaged
over the sample together with boundedness of `ℙₙψ̈` and consistency. Entrywise closeness transfers to the
quadratic form by `inner_toEuclidCLM_pert`. -/
private lemma empirical_hessian_negdef_bad {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ_open : IsOpen Θ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) {c : ℝ} (hc : 0 < c)
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin k),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x⟫ ≤ - c * ‖x‖ ^ 2)
    (hVmeas : ∀ j i, Measurable (fun x => psiDot ψ θ₀ x j i))
    (hVint : ∀ j i, Integrable (fun x => psiDot ψ θ₀ x j i) P)
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ => ψ θ j x) Θ)
    (ψddot : Ω → ℝ) (hψddot_meas : Measurable ψddot) (hψddot_int : Integrable ψddot P)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hcons : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :
    Tendsto (fun n => μ.real {ξ | ¬ ∀ x : EuclideanSpace ℝ (Fin k),
        ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
            (empVmat ψ (θ_hat n (fun i : Fin n => X i.val ξ)) n
              (fun i : Fin n => X i.val ξ)) x⟫ ≤ - (c / 2) * ‖x‖ ^ 2}) atTop (𝓝 0) := by
  classical
  -- The Jacobian is `ψ̈`-Lipschitz on the ball.
  have hlip := psiDot_lipschitz ψ θ₀ Θ ψddot hρ hΘ_open hball hC2 hdom
  -- The empirical Jacobian converges entrywise and `ℙₙψ̈ = O_P(1)`.
  have hD := empiricalPsiDot_tendsto P ψ θ₀ hVmeas hVint μ X hX_meas hX_indep hX_id hX_law
  have hE := empiricalPsiDdot_OP P ψddot hψddot_meas hψddot_int μ X hX_meas hX_indep hX_id
    hX_law
  -- Averaging the Lipschitz bound over the sample controls the moving-centre part of the Hessian.
  have hentry1 : ∀ t ∈ Metric.closedBall θ₀ ρ, ∀ (n : ℕ) (Xs : Fin n → Ω) (j i : Fin k),
      |empVmat ψ t n Xs j i - empVmat ψ θ₀ n Xs j i|
        ≤ empiricalAvg ψddot n Xs * ‖t - θ₀‖ := by
    intro t ht n Xs j i
    have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    have hrw : empVmat ψ t n Xs j i - empVmat ψ θ₀ n Xs j i
        = (n : ℝ)⁻¹ * ∑ l, (psiDot ψ t (Xs l) j i - psiDot ψ θ₀ (Xs l) j i) := by
      simp only [empVmat, Matrix.of_apply, empiricalAvg, Finset.sum_sub_distrib, mul_sub]
    rw [hrw, abs_mul, abs_of_nonneg hinv]
    calc (n : ℝ)⁻¹ * |∑ l, (psiDot ψ t (Xs l) j i - psiDot ψ θ₀ (Xs l) j i)|
        ≤ (n : ℝ)⁻¹ * ∑ l, ψddot (Xs l) * ‖t - θ₀‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hinv
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ =>
            hlip t ht θ₀ (Metric.mem_closedBall_self hρ.le) j i (Xs l))
      _ = empiricalAvg ψddot n Xs * ‖t - θ₀‖ := by
          rw [← Finset.sum_mul]; simp only [empiricalAvg]; ring
  -- Entrywise tolerance.
  set ζ : ℝ := c / (2 * (Real.sqrt k * k + 1)) with hζ_def
  have hζ_pos : 0 < ζ := by
    rw [hζ_def]
    have : (0 : ℝ) < 2 * (Real.sqrt k * k + 1) := by positivity
    positivity
  have hζ_small : Real.sqrt k * (k : ℝ) * ζ ≤ c / 2 := by
    have hζ' : ζ * (2 * (Real.sqrt k * k + 1)) = c := by
      rw [hζ_def]; field_simp
    have hkk : (0 : ℝ) ≤ Real.sqrt k * k := by positivity
    calc Real.sqrt k * (k : ℝ) * ζ ≤ (Real.sqrt k * k + 1) * ζ :=
          mul_le_mul_of_nonneg_right (by linarith) hζ_pos.le
      _ = c / 2 := by rw [← hζ']; ring
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨MK₀, hMK₀⟩ := hE (η / 4) (by positivity)
  set MK : ℝ := max MK₀ 1 with hMK_def
  have hMK_pos : 0 < MK := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set δ : ℝ := min ρ (ζ / (2 * MK)) with hδ_def
  have hδ_pos : 0 < δ := lt_min hρ (by positivity)
  obtain ⟨N₃, hN₃⟩ := Metric.tendsto_atTop.mp (hcons δ hδ_pos) (η / 4) (by positivity)
  have hMsum : Tendsto (fun n => ∑ p : Fin k × Fin k, μ.real
      {ξ | ζ / 2 ≤ ‖empiricalAvg (fun x => psiDot ψ θ₀ x p.1 p.2) n
        (fun i : Fin n => X i.val ξ) - Vmat P ψ θ₀ p.1 p.2‖}) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin k × Fin k))
      (fun p _ => hD p.1 p.2 (ζ / 2) (by positivity))
    simpa using h
  obtain ⟨N₄, hN₄⟩ := Metric.tendsto_atTop.mp hMsum (η / 4) (by positivity)
  refine ⟨max N₃ N₄, fun n hn => ?_⟩
  set S1 : Set Ξ := {ξ | MK < ‖empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)‖} with hS1
  set S3 : Set Ξ := {ξ | δ ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} with hS3
  set S4 : Set Ξ := ⋃ p : Fin k × Fin k,
    {ξ | ζ / 2 ≤ ‖empiricalAvg (fun x => psiDot ψ θ₀ x p.1 p.2) n (fun i : Fin n => X i.val ξ)
      - Vmat P ψ θ₀ p.1 p.2‖} with hS4
  have hkey : ∀ ξ : Ξ, ξ ∉ S1 → ξ ∉ S3 → ξ ∉ S4 →
      ∀ x : EuclideanSpace ℝ (Fin k),
        ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
            (empVmat ψ (θ_hat n (fun i : Fin n => X i.val ξ)) n
              (fun i : Fin n => X i.val ξ)) x⟫ ≤ - (c / 2) * ‖x‖ ^ 2 := by
    intro ξ h1 h3 h4 x
    rw [hS1] at h1; rw [hS3] at h3; rw [hS4] at h4
    simp only [Set.mem_setOf_eq, not_lt, Real.norm_eq_abs] at h1
    simp only [Set.mem_setOf_eq, not_le] at h3
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le, Real.norm_eq_abs] at h4
    set t : EuclideanSpace ℝ (Fin k) := θ_hat n (fun i : Fin n => X i.val ξ) with ht_def
    set Xs : Fin n → Ω := fun i : Fin n => X i.val ξ with hXs_def
    have hδρ : δ ≤ ρ := min_le_left _ _
    have htball : t ∈ Metric.closedBall θ₀ ρ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact le_of_lt (lt_of_lt_of_le h3 hδρ)
    -- Entrywise: `‖ℙₙψ̇_{θ̂ₙ} − V‖_∞ ≤ ζ`.
    have hpiece1 : ∀ j i : Fin k,
        |empVmat ψ t n Xs j i - empVmat ψ θ₀ n Xs j i| ≤ ζ / 2 := by
      intro j i
      refine (hentry1 t htball n Xs j i).trans ?_
      have hδζ : δ ≤ ζ / (2 * MK) := min_le_right _ _
      have hnn : (0 : ℝ) ≤ ‖t - θ₀‖ := norm_nonneg _
      have havg : empiricalAvg ψddot n Xs ≤ MK :=
        le_trans (le_abs_self _) h1
      have havg0 : |empiricalAvg ψddot n Xs| ≤ MK := h1
      have hprod : empiricalAvg ψddot n Xs * ‖t - θ₀‖ ≤ MK * δ := by
        by_cases hneg : empiricalAvg ψddot n Xs ≤ 0
        · calc empiricalAvg ψddot n Xs * ‖t - θ₀‖ ≤ 0 :=
                mul_nonpos_of_nonpos_of_nonneg hneg hnn
            _ ≤ MK * δ := by positivity
        · exact mul_le_mul havg h3.le hnn hMK_pos.le
      refine hprod.trans ?_
      calc MK * δ ≤ MK * (ζ / (2 * MK)) := mul_le_mul_of_nonneg_left hδζ hMK_pos.le
        _ = ζ / 2 := by field_simp
    have hclose : ∀ j i : Fin k, |empVmat ψ t n Xs j i - Vmat P ψ θ₀ j i| ≤ ζ := by
      intro j i
      have h2 : |empVmat ψ θ₀ n Xs j i - Vmat P ψ θ₀ j i| ≤ ζ / 2 := by
        have := h4 (j, i)
        simp only [empVmat, Matrix.of_apply]
        exact this.le
      calc |empVmat ψ t n Xs j i - Vmat P ψ θ₀ j i|
          ≤ |empVmat ψ t n Xs j i - empVmat ψ θ₀ n Xs j i|
            + |empVmat ψ θ₀ n Xs j i - Vmat P ψ θ₀ j i| := by
            have : empVmat ψ t n Xs j i - Vmat P ψ θ₀ j i
                = (empVmat ψ t n Xs j i - empVmat ψ θ₀ n Xs j i)
                  + (empVmat ψ θ₀ n Xs j i - Vmat P ψ θ₀ j i) := by ring
            rw [this]; exact abs_add_le _ _
        _ ≤ ζ := by linarith [hpiece1 j i, h2]
    have hpert := inner_toEuclidCLM_pert (empVmat ψ t n Xs) (Vmat P ψ θ₀) x hζ_pos.le hclose
    have hV := hVneg x
    nlinarith [hpert, hV, sq_nonneg ‖x‖, hζ_small, norm_nonneg x]
  -- The bad set is contained in the union of the three bad events.
  have hsub : {ξ : Ξ | ¬ ∀ x : EuclideanSpace ℝ (Fin k),
        ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
            (empVmat ψ (θ_hat n (fun i : Fin n => X i.val ξ)) n
              (fun i : Fin n => X i.val ξ)) x⟫ ≤ - (c / 2) * ‖x‖ ^ 2}
      ⊆ S1 ∪ S3 ∪ S4 := by
    intro ξ hξ
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨q1, q3⟩, q4⟩ := hcon
    exact hξ (hkey ξ q1 q3 q4)
  have hb1 : μ.real S1 ≤ η / 4 := by
    have hsub1 : S1 ⊆ {ξ | MK₀ < ‖empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)‖} := by
      rw [hS1]; exact fun ξ hξ => lt_of_le_of_lt (le_max_left MK₀ 1) hξ
    exact le_trans (measureReal_mono hsub1) (hMK₀ n)
  have hb3 : μ.real S3 < η / 4 := by
    have h := hN₃ n (le_of_max_le_left hn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h
    rw [hS3]; exact h
  have hb4 : μ.real S4 < η / 4 := by
    have h := hN₄ n (le_of_max_le_right hn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg
      fun _ _ => measureReal_nonneg)] at h
    refine lt_of_le_of_lt ?_ h
    rw [hS4]
    exact measureReal_iUnion_fintype_le _
  have a1 := measureReal_union_le (μ := μ) (S1 ∪ S3) S4
  have a2 := measureReal_union_le (μ := μ) S1 S3
  have hle := measureReal_mono (μ := μ) hsub
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  linarith

/-- **The empirical Hessian `ℙₙψ̇_{θ̂ₙ}` is negative definite with probability → 1.** By a
Taylor expansion (as in the proof of Theorem 5.41), the empirical Hessian `empVmat ψ θ̂ₙ`
at a consistent zero
`θ̂ₙ →ₚ θ₀` converges in probability to the negative-definite `V = Vmat P ψ θ₀`
(`empiricalPsiDot_tendsto`, `psiDot_lipschitz`, and `hcons`); hence its quadratic form
is negative on all nonzero vectors with probability tending to `1`. vdV p.69 "the Hessian
`ℙₙψ̇_{θ̂ₙ}` at any consistent zero `θ̂ₙ` converges in probability to the negative-definite
matrix `Pψ̇_{θ₀}` and is negative-definite with probability tending to 1."

Corollary of the bad-event form `empirical_hessian_negdef_bad`. The hypotheses beyond the
Hessian data (`Θ`, `hΘ_open`, `hC2`, `ψddot`, `hψddot_meas`, `hψddot_int`, `ρ`, `hρ`,
`hball`, `hdom`) are exactly the classical smoothness conditions of vdV §*5.6 (p.67) already
carried by both theorems; they let the proof move the Hessian's centre from `θ₀`
to `θ̂ₙ` via `psiDot_lipschitz` and `empiricalPsiDdot_OP`. -/
theorem empirical_hessian_negdef_wp1 {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ_open : IsOpen Θ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) {c : ℝ} (hc : 0 < c)
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin k),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) x⟫ ≤ - c * ‖x‖ ^ 2)
    (hVmeas : ∀ j i, Measurable (fun x => psiDot ψ θ₀ x j i))
    (hVint : ∀ j i, Integrable (fun x => psiDot ψ θ₀ x j i) P)
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ => ψ θ j x) Θ)
    (ψddot : Ω → ℝ) (hψddot_meas : Measurable ψddot) (hψddot_int : Integrable ψddot P)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hcons : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :
    Tendsto (fun n => μ.real {ξ | ∀ x : EuclideanSpace ℝ (Fin k), x ≠ 0 →
        ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
            (empVmat ψ (θ_hat n (fun i : Fin n => X i.val ξ)) n
              (fun i : Fin n => X i.val ξ)) x⟫ < 0}) atTop (𝓝 1) := by
  have hbad := empirical_hessian_negdef_bad P Θ hΘ_open ψ θ₀ hc hVneg hVmeas hVint hC2
    ψddot hψddot_meas hψddot_int hρ hball hdom θ_hat μ X hX_meas hX_indep hX_id hX_law hcons
  apply TendstoInnerProbOne.tendsto_measureReal
  refine tendstoInnerProbOne_of_good μ (fun _ => Set.univ) _ _ ?_ ?_ hbad
  · intro n ξ hξ
    have hnot := hξ.2
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hnot
    intro x hx
    have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    have hsq : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos hxpos 2
    exact lt_of_le_of_lt (hnot x) (by linarith [mul_pos hc hsq])
  · exact ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ, fun _ _ h => h, by simp⟩

/-! ### Roots can be chosen to be local maxima (vdV Theorem 5.42) -/

/-- **Classical Z-estimator roots as local maxima — vdV Theorem 5.42, final assertion**
(§*5.6, book p.69).

Under the conditions of Theorem 5.41, if `ψ_θ = ṁ_θ` is the gradient of some function `m_θ`
(`hgrad`: `∇_θ m_θ(x) = ψ_θ(x)`, encoded as `HasFDerivAt (m · x) (innerSL ℝ (psiVec ψ θ x))`)
and `θ₀` is a point of local maximum of `θ ↦ P(m_θ − m_{θ₀})` (`hmax`, difference form,
avoiding global integrability of `m`), then the consistent sequence of roots `θ̂ₙ` can be
chosen to be **local maxima** of `θ ↦ ℙₙm_θ`:

* `∀ j, ℙₙψ_{θ̂ₙ, j} = 0` with probability → 1 (roots), and `θ̂ₙ →ₚ θ₀` (consistency);
* `θ̂ₙ` is a local maximum of `θ ↦ ℙₙm_θ` with probability → 1.

The theorem combines the consistent roots from `classical_zEstimator_root_exists_consistent`
with `V_negdef_of_localmax`, `empirical_hessian_negdef_wp1`, and
`isLocalMax_of_negdef_hessian` to obtain local maxima. -/
theorem classical_zEstimator_localmax_roots
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ_open : IsOpen Θ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ ∈ Θ)
    (hψ_meas : ∀ θ j, Measurable (ψ θ j))
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ => ψ θ j x) Θ)
    (hPθ₀_zero : ∀ j, ∫ x, ψ θ₀ j x ∂P = 0)
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P)
    (hVint : ∀ j i, Integrable (fun x => psiDot ψ θ₀ x j i) P)
    (hV : IsUnit (Vmat P ψ θ₀).det)
    (ψddot : Ω → ℝ) (hψddot_meas : Measurable ψddot) (hψddot_int : Integrable ψddot P)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (m : EuclideanSpace ℝ (Fin k) → Ω → ℝ) (hm_meas : ∀ θ, Measurable (m θ))
    (hgrad : ∀ θ ∈ Θ, ∀ x, HasFDerivAt (fun θ' => m θ' x) (innerSL ℝ (psiVec ψ θ x)) θ)
    (hmax : IsLocalMax (fun θ => ∫ x, (m θ x - m θ₀ x) ∂P) θ₀) :
    ∃ θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k),
      TendstoInnerProbOne μ (fun n => {ξ | ∀ j,
          empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) j) n
            (fun i : Fin n => X i.val ξ) = 0})
      ∧ TendstoInProbZero (fun _ : ℕ => μ)
          (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
      ∧ TendstoInnerProbOne μ (fun n => {ξ |
          IsLocalMax (fun θ => empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ))
            (θ_hat n (fun i : Fin n => X i.val ξ))}) := by
  classical
  -- **(1)** vdV 5.42 (i)+(ii): a consistent sequence of roots.
  obtain ⟨-, θ_hat, hroot, hcons⟩ :=
    classical_zEstimator_root_exists_consistent P Θ hΘ_open ψ θ₀ hθ₀ hψ_meas hC2 hPθ₀_zero
      hψ_L2 hVint hV ψddot hψddot_meas hψddot_int hρ hball hdom μ X hX_meas hX_indep hX_id
      hX_law
  refine ⟨θ_hat, hroot, hcons, ?_⟩
  have hρ4 : (0 : ℝ) < ρ / 4 := by linarith
  -- Derived regularity: measurability of the Jacobian entries and `P`-integrability of `ψ_{θ₀}`
  -- (the latter from `P‖ψ_{θ₀}‖² < ∞`, coordinate by coordinate).
  have hVmeas := psiDot_measurable ψ θ₀ Θ hΘ_open hθ₀ hψ_meas hC2
  have hψint : ∀ j, Integrable (ψ θ₀ j) P := by
    intro j
    have hmem : MemLp (fun x => ψ θ₀ j x) 2 P := by
      refine MemLp.of_le hψ_L2 ((hψ_meas θ₀ j).aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      have := coord_abs_le_norm (psiVec ψ θ₀ x) j
      simpa [psiVec, Real.norm_eq_abs] using this
    exact hmem.integrable (by norm_num)
  -- **(2)** The pointwise second-order Taylor expansion of `m` with cubic remainder.
  have hpt2 := pointwise_taylor2_m m ψ θ₀ Θ ψddot hρ hΘ_open hball hC2 hdom hgrad
  -- **(3)** `V = Pψ̇_{θ₀} = Pm̈_{θ₀}` is symmetric (equality of mixed partials).
  have hVsymm := Vmat_isHermitian_of_grad P m ψ Θ hΘ_open hC2 hgrad θ₀ hθ₀
  -- **(4)** The population criterion has a second-order expansion with Hessian `V`.
  have hpop := population_taylor2_m P m ψ θ₀ ψddot
    (fun θ hθ x => hpt2 θ₀ (Metric.mem_closedBall_self hρ4.le) θ hθ x)
    hm_meas hψint hVint hψddot_int
  have hTaylorPop : Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ => (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
            (Vmat P ψ θ₀) (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2) := by
    set Cp : ℝ := |(k : ℝ) / 2 * ∫ x, ψddot x ∂P| with hCp
    have hCp0 : 0 ≤ Cp := abs_nonneg _
    rw [Asymptotics.isLittleO_iff]
    intro c' hc'
    rw [Metric.eventually_nhds_iff]
    refine ⟨min (ρ / 4) (c' / (Cp + 1)), lt_min hρ4 (by positivity), fun {θ} hθ => ?_⟩
    have hmem : θ ∈ Metric.closedBall θ₀ (ρ / 4) :=
      Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le hθ (min_le_left _ _)))
    have hb := hpop θ hmem
    have hlin : ∑ j, (∫ x, ψ θ₀ j x ∂P) * (θ - θ₀) j = 0 := by
      simp [hPθ₀_zero]
    rw [hlin, sub_zero, ← inner_toEuclidCLM_quad] at hb
    have hn : ‖θ - θ₀‖ = dist θ θ₀ := (dist_eq_norm _ _).symm
    have hle1 : (k : ℝ) / 2 * (∫ x, ψddot x ∂P) * ‖θ - θ₀‖ ^ 3
        ≤ Cp * ‖θ - θ₀‖ ^ 3 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have hsmall : ‖θ - θ₀‖ ≤ c' / (Cp + 1) := by
      rw [hn]; exact le_of_lt (lt_of_lt_of_le hθ (min_le_right _ _))
    have hstep : Cp * ‖θ - θ₀‖ ^ 3 ≤ c' * ‖θ - θ₀‖ ^ 2 := by
      have h1 : Cp * ‖θ - θ₀‖ ≤ c' := by
        calc Cp * ‖θ - θ₀‖ ≤ Cp * (c' / (Cp + 1)) :=
              mul_le_mul_of_nonneg_left hsmall hCp0
          _ ≤ c' := by
              rw [mul_div_assoc'] at *
              rw [div_le_iff₀ (by positivity)]
              nlinarith
      nlinarith [sq_nonneg ‖θ - θ₀‖, h1, norm_nonneg (θ - θ₀)]
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _)]
    calc |(∫ x, (m θ x - m θ₀ x) ∂P)
            - 1 / 2 * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
                (Vmat P ψ θ₀) (θ - θ₀)⟫|
        ≤ (k : ℝ) / 2 * (∫ x, ψddot x ∂P) * ‖θ - θ₀‖ ^ 3 := hb
      _ ≤ c' * ‖θ - θ₀‖ ^ 2 := le_trans hle1 hstep
  -- **(5)** `V` is negative definite with a uniform constant.
  obtain ⟨c, hc, hVneg⟩ := V_negdef_of_localmax P m ψ θ₀ hVsymm hmax hTaylorPop hV
  -- **(6)** The empirical Hessian at `θ̂ₙ` is uniformly negative
  -- definite off an event of vanishing outer measure.
  have hbad := empirical_hessian_negdef_bad P Θ hΘ_open ψ θ₀ hc hVneg hVmeas hVint hC2 ψddot
    hψddot_meas hψddot_int hρ hball hdom θ_hat μ X hX_meas hX_indep hX_id hX_law hcons
  have hcons4 := hcons (ρ / 4) hρ4
  -- **(7)** Assemble: off the union of the two bad events, and on the root event, `θ̂ₙ` is a
  -- critical point of `ℙₙm` with negative-definite Hessian, hence a local maximum.
  set A : ℕ → Set Ξ := fun n => {ξ | ∀ j,
    empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) j) n
      (fun i : Fin n => X i.val ξ) = 0} with hA_def
  set B : ℕ → Set Ξ := fun n =>
    {ξ | ¬ ∀ x : EuclideanSpace ℝ (Fin k),
        ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
            (empVmat ψ (θ_hat n (fun i : Fin n => X i.val ξ)) n
              (fun i : Fin n => X i.val ξ)) x⟫ ≤ - (c / 2) * ‖x‖ ^ 2}
      ∪ {ξ | ρ / 4 ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} with hB_def
  have hB0 : Tendsto (fun n => μ.real (B n)) atTop (𝓝 0) := by
    have hsum := hbad.add hcons4
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun n => measureReal_nonneg)
      (Eventually.of_forall fun n => ?_)
    rw [hB_def]
    exact measureReal_union_le _ _
  refine tendstoInnerProbOne_of_good μ A B _ ?_ hroot hB0
  intro n ξ hξ
  obtain ⟨hrootξ, hbadξ⟩ := hξ
  rw [hA_def] at hrootξ
  rw [hB_def] at hbadξ
  simp only [Set.mem_compl_iff, Set.mem_union, not_or, Set.mem_setOf_eq, not_not,
    not_le] at hbadξ
  obtain ⟨hneg, htb⟩ := hbadξ
  simp only [Set.mem_setOf_eq] at hrootξ
  set t : EuclideanSpace ℝ (Fin k) := θ_hat n (fun i : Fin n => X i.val ξ) with ht_def
  set Xs : Fin n → Ω := fun i : Fin n => X i.val ξ with hXs_def
  have htmem : t ∈ Metric.closedBall θ₀ (ρ / 4) :=
    Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact htb.le)
  -- The empirical criterion expands to second order at `t` with Hessian `ℙₙψ̇_t` and no
  -- linear term (the root condition).
  have hemp := empirical_taylor2_m m ψ θ₀ ψddot hpt2 n Xs
  have hTaylorEmp : Asymptotics.IsLittleO (𝓝 t)
      (fun θ => empiricalAvg (m θ) n Xs - empiricalAvg (m t) n Xs
        - (1 / 2) * ⟪θ - t, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
            (empVmat ψ t n Xs) (θ - t)⟫)
      (fun θ => ‖θ - t‖ ^ 2) := by
    set Ce : ℝ := |(k : ℝ) / 2 * empiricalAvg ψddot n Xs| with hCe
    have hCe0 : 0 ≤ Ce := abs_nonneg _
    rw [Asymptotics.isLittleO_iff]
    intro c' hc'
    rw [Metric.eventually_nhds_iff]
    have hgap : 0 < ρ / 4 - ‖t - θ₀‖ := by linarith
    refine ⟨min (ρ / 4 - ‖t - θ₀‖) (c' / (Ce + 1)), lt_min hgap (by positivity),
      fun {θ} hθ => ?_⟩
    have hdt : dist θ t < ρ / 4 - ‖t - θ₀‖ := lt_of_lt_of_le hθ (min_le_left _ _)
    have hmem : θ ∈ Metric.closedBall θ₀ (ρ / 4) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hsplit : θ - θ₀ = (θ - t) + (t - θ₀) := by abel
      have : ‖θ - θ₀‖ ≤ ‖θ - t‖ + ‖t - θ₀‖ := by rw [hsplit]; exact norm_add_le _ _
      have hdn : ‖θ - t‖ = dist θ t := (dist_eq_norm _ _).symm
      rw [hdn] at this
      linarith
    have hb := hemp t htmem θ hmem
    have hlin : ∑ j, empiricalAvg (ψ t j) n Xs * (θ - t) j = 0 := by
      simp [hrootξ]
    rw [hlin, sub_zero, ← inner_toEuclidCLM_quad] at hb
    have hle1 : (k : ℝ) / 2 * empiricalAvg ψddot n Xs * ‖θ - t‖ ^ 3
        ≤ Ce * ‖θ - t‖ ^ 3 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have hsmall : ‖θ - t‖ ≤ c' / (Ce + 1) := by
      rw [show ‖θ - t‖ = dist θ t from (dist_eq_norm _ _).symm]
      exact le_of_lt (lt_of_lt_of_le hθ (min_le_right _ _))
    have hstep : Ce * ‖θ - t‖ ^ 3 ≤ c' * ‖θ - t‖ ^ 2 := by
      have h1 : Ce * ‖θ - t‖ ≤ c' := by
        calc Ce * ‖θ - t‖ ≤ Ce * (c' / (Ce + 1)) := mul_le_mul_of_nonneg_left hsmall hCe0
          _ ≤ c' := by
              rw [mul_div_assoc'] at *
              rw [div_le_iff₀ (by positivity)]
              nlinarith
      nlinarith [sq_nonneg ‖θ - t‖, h1, norm_nonneg (θ - t)]
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _)]
    calc |empiricalAvg (m θ) n Xs - empiricalAvg (m t) n Xs
            - 1 / 2 * ⟪θ - t, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
                (empVmat ψ t n Xs) (θ - t)⟫|
        ≤ (k : ℝ) / 2 * empiricalAvg ψddot n Xs * ‖θ - t‖ ^ 3 := hb
      _ ≤ c' * ‖θ - t‖ ^ 2 := le_trans hle1 hstep
  exact isLocalMax_of_negdef_hessian (fun θ => empiricalAvg (m θ) n Xs) t
    (empVmat ψ t n Xs) (by linarith : (0 : ℝ) < c / 2) hneg hTaylorEmp

/-- **Outer-measure form of classical Z-estimator roots as local maxima.**

The inner-probability statement `classical_zEstimator_localmax_roots` implies this
outer-measure limit. No measurability of the selected roots or of the target root and
local-maximum events is assumed. -/
theorem classical_zEstimator_localmax_roots_outer
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ_open : IsOpen Θ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ ∈ Θ)
    (hψ_meas : ∀ θ j, Measurable (ψ θ j))
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ => ψ θ j x) Θ)
    (hPθ₀_zero : ∀ j, ∫ x, ψ θ₀ j x ∂P = 0)
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P)
    (hVint : ∀ j i, Integrable (fun x => psiDot ψ θ₀ x j i) P)
    (hV : IsUnit (Vmat P ψ θ₀).det)
    (ψddot : Ω → ℝ) (hψddot_meas : Measurable ψddot) (hψddot_int : Integrable ψddot P)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (m : EuclideanSpace ℝ (Fin k) → Ω → ℝ) (hm_meas : ∀ θ, Measurable (m θ))
    (hgrad : ∀ θ ∈ Θ, ∀ x, HasFDerivAt (fun θ' => m θ' x) (innerSL ℝ (psiVec ψ θ x)) θ)
    (hmax : IsLocalMax (fun θ => ∫ x, (m θ x - m θ₀ x) ∂P) θ₀) :
    ∃ θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k),
      Filter.Tendsto (fun n => μ.real {ξ | ∀ j,
          empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) j) n
            (fun i : Fin n => X i.val ξ) = 0}) Filter.atTop (𝓝 1)
      ∧ TendstoInProbZero (fun _ : ℕ => μ)
          (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
      ∧ Filter.Tendsto (fun n => μ.real {ξ |
          IsLocalMax (fun θ => empiricalAvg (m θ) n (fun i : Fin n => X i.val ξ))
            (θ_hat n (fun i : Fin n => X i.val ξ))}) Filter.atTop (𝓝 1) := by
  obtain ⟨θ_hat, hroot, hcons, hmaxima⟩ :=
    classical_zEstimator_localmax_roots P Θ hΘ_open ψ θ₀ hθ₀ hψ_meas hC2 hPθ₀_zero
      hψ_L2 hVint hV ψddot hψddot_meas hψddot_int hρ hball hdom μ X hX_meas hX_indep hX_id
      hX_law m hm_meas hgrad hmax
  exact ⟨θ_hat, hroot.tendsto_measureReal, hcons, hmaxima.tendsto_measureReal⟩

end AsymptoticStatistics.ClassicalZEstimator
