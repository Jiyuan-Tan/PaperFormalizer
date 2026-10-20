module
public import StatLean.AsymptoticStatistics.ClassicalZEstimator.TaylorDomination
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ZEstimatorNormality
public import StatLean.AsymptoticStatistics.ForMathlib.SecondOrderCalculus
public import StatLean.AsymptoticStatistics.ForMathlib.IidWLLN
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

@[expose] public section

/-!
# Existence and consistency of classical Z-estimator roots (vdV Theorem 5.42 (i)+(ii))

Under the classical conditions of vdV §*5.6 (book pp. 68–69), the
smoothness conditions of Theorem 5.41 **ensure the existence** of solutions of the
estimating equation `ℙₙψ_θ = 0`, and — provided some consistent estimator sequence exists —
allow one to **select a consistent sequence of roots**:

* the probability that `ℙₙψ_θ = 0` has at least one root tends to `1`;
* there exists a sequence of roots `θ̂ₙ` with `θ̂ₙ →ₚ θ₀`.

## Proof route

The proof uses a quantitative near-linearity event on a closed ball. The empirical map
`Ψₙ` differs from the affine map with linear part `ℙₙψ̇_{θ₀}` by at most
`(ℙₙψ̈) · r · ‖θ − θ'‖`. Together with entrywise convergence of the empirical Jacobian,
this gives `ApproximatesLinearOn Ψₙ V (closedBall θ₀ r) c`. Quantitative surjectivity then
places a zero of `Ψₙ` in the ball whenever `c < ‖V⁻¹‖⁻¹` and
`‖Ψₙθ₀‖ ≤ (‖V⁻¹‖⁻¹ − c)·r`.

The empirical quantities `ℙₙψ̈`, `ℙₙψ̇_{θ₀}`, and `ℙₙψ_{θ₀}` are averages of finitely many
integrable functions. A finite union bound and the weak law give probability tending to one
for the near-linearity event. Diagonalizing over radii tending to zero produces a consistent
sequence of roots.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Topology RealInnerProductSpace Matrix NNReal

namespace AsymptoticStatistics.ClassicalZEstimator

open AsymptoticStatistics.EmpiricalProcess

/-! ### Setup — bundled population / empirical estimating maps. -/

/-- **Population estimating map `Ψ(θ) = Pψ_θ`.** The `k` population estimating equations
`θ ↦ (∫ ψ_{θ,j} ∂P)ⱼ` bundled into a single `EuclideanSpace ℝ (Fin k)` point. vdV's `Ψ`
(book p.68); `θ₀` is a zero of `Ψ` under `Pψ_{θ₀} = 0`. -/
noncomputable def popEstimatingMap {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun j => ∫ x, ψ θ j x ∂P)

/-- **Empirical estimating map `Ψₙ(θ) = ℙₙψ_θ`.** The `k` empirical estimating equations
`θ ↦ (ℙₙψ_{θ,j})ⱼ` bundled into `EuclideanSpace ℝ (Fin k)`. vdV's `Ψₙ` (book p.68);
`empEstimatingMap ψ θ n Xs = 0` iff `∀ j, ℙₙψ_{θ,j} = 0`, i.e. `θ` is a root. -/
noncomputable def empEstimatingMap {k : ℕ} {Ω : Type*}
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ) (Xs : Fin n → Ω) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun j => empiricalAvg (ψ θ j) n Xs)

/-- Coordinates of `empEstimatingMap` are the scalar empirical averages. -/
@[simp] lemma empEstimatingMap_apply {k : ℕ} {Ω : Type*}
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ) (Xs : Fin n → Ω) (j : Fin k) :
    empEstimatingMap ψ θ n Xs j = empiricalAvg (ψ θ j) n Xs := rfl

/-- A coordinate of a Euclidean vector is dominated by its norm. -/
theorem abs_coord_le_norm {k : ℕ} (w : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    |w i| ≤ ‖w‖ := by
  rw [EuclideanSpace.norm_eq, show |w i| = Real.sqrt (|w i| ^ 2) from
    (Real.sqrt_sq (abs_nonneg _)).symm]
  refine Real.sqrt_le_sqrt ?_
  simpa [Real.norm_eq_abs] using
    Finset.single_le_sum (f := fun j => |w j| ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-! ### Empirical mean-value bound with the frozen Jacobian `ψ̇_{θ₀}`

The Taylor estimate at `θ₀` alone gives an `r²` bound after subtracting two instances;
the following mean-value estimate is instead proportional to `‖θ − θ'‖`. -/

/-- **Pointwise mean-value bound against the frozen Jacobian.** For `θ, θ'` in the ball
`‖· − θ₀‖ ≤ ρ`, the increment of `ψ_{·,j}(x)` differs from its linearisation *at `θ₀`* by at
most `ψ̈(x)·ρ·‖θ − θ'‖`:

    `|ψ_{θ,j}(x) − ψ_{θ',j}(x) − ∑ᵢ ψ̇_{θ₀}(x)ⱼᵢ (θ − θ')ᵢ| ≤ ψ̈(x) ρ ‖θ − θ'‖`.

Mean-value inequality applied to `z ↦ ψ_{z,j}(x) − Dψ_{θ₀,j}(x) z`, whose derivative is
`Dψ_{z,j}(x) − Dψ_{θ₀,j}(x)`, of norm `≤ ψ̈(x)‖z − θ₀‖ ≤ ψ̈(x)ρ` by the operator-norm
Lipschitz estimate `fderiv_lipschitz_opNorm`. -/
theorem pointwise_meanValue_bound {k : ℕ} {Ω : Type*}
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (Θ : Set (EuclideanSpace ℝ (Fin k)))
    (ψddot : Ω → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hΘ_open : IsOpen Θ)
    (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ' => ψ θ' j x) Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x) :
    ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ θ' ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      |ψ θ j x - ψ θ' j x - ∑ i, psiDot ψ θ₀ x j i * (θ - θ') i|
        ≤ ψddot x * ρ * ‖θ - θ'‖ := by
  classical
  intro θ hθ θ' hθ' j x
  set φ : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ := fderiv ℝ (fun θ'' => ψ θ'' j x) θ₀ with hφ
  -- The coordinate sum is exactly `φ` applied to the increment.
  have hdec : ∑ i, (θ - θ') i • EuclideanSpace.single i (1 : ℝ) = (θ - θ') := by
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr (θ - θ')
  have hsum : ∑ i, psiDot ψ θ₀ x j i * (θ - θ') i = φ (θ - θ') := by
    conv_rhs => rw [← hdec]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    simp [psiDot, hφ, mul_comm]
  rw [hsum]
  -- The corrected map `g z = ψ_{z,j}(x) − φ z` has small derivative on the ball.
  have hdiffAt : ∀ z ∈ Metric.closedBall θ₀ ρ,
      DifferentiableAt ℝ (fun θ'' => ψ θ'' j x) z := fun z hz =>
    ((hC2 j x).differentiableOn (by norm_num)).differentiableAt (hΘ_open.mem_nhds (hball hz))
  have hgfd : ∀ z ∈ Metric.closedBall θ₀ ρ,
      HasFDerivAt (fun z' => ψ z' j x - φ z')
        (fderiv ℝ (fun θ'' => ψ θ'' j x) z - φ) z := fun z hz =>
    (hdiffAt z hz).hasFDerivAt.sub φ.hasFDerivAt
  have hbnd : ∀ z ∈ Metric.closedBall θ₀ ρ,
      ‖fderiv ℝ (fun z' => ψ z' j x - φ z') z‖ ≤ ψddot x * ρ := by
    intro z hz
    rw [(hgfd z hz).fderiv]
    have hop := fderiv_lipschitz_opNorm ψ θ₀ Θ ψddot hΘ_open hball hC2 hdom z hz θ₀
      (Metric.mem_closedBall_self hρ.le) j x
    refine hop.trans (mul_le_mul_of_nonneg_left ?_ ?_)
    · simpa [dist_eq_norm] using Metric.mem_closedBall.mp hz
    · exact le_trans (norm_nonneg _) (hdom θ₀ (Metric.mem_closedBall_self hρ.le) j x)
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hgfd z hz).differentiableAt) hbnd (convex_closedBall θ₀ ρ) hθ' hθ
  -- `g θ − g θ' = ψ_θ − ψ_{θ'} − φ(θ − θ')`.
  have hrw : (fun z' => ψ z' j x - φ z') θ - (fun z' => ψ z' j x - φ z') θ'
      = ψ θ j x - ψ θ' j x - φ (θ - θ') := by
    simp only [map_sub]; ring
  rw [hrw, Real.norm_eq_abs] at hmv
  exact hmv

/-- **Empirical mean-value bound.** Averaging the pointwise bound over a sample
`Xs : Fin n → Ω` gives, on `closedBall θ₀ ρ`,

    `|ℙₙψ_{θ,j} − ℙₙψ_{θ',j} − ∑ᵢ (ℙₙψ̇_{θ₀})ⱼᵢ (θ − θ')ᵢ| ≤ (ℙₙψ̈) ρ ‖θ − θ'‖`,

i.e. `Ψₙ` is within `(ℙₙψ̈)·ρ·‖θ − θ'‖` of the affine map with linear part `ℙₙψ̇_{θ₀}`.
The Taylor bound `empirical_taylor_random` is specialized to `θ' = θ₀` and cannot produce a bound
proportional to `‖θ − θ'‖`. -/
theorem empirical_meanValue_bound {k : ℕ} {Ω : Type*}
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (ψddot : Ω → ℝ) {ρ : ℝ}
    (hbound : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ θ' ∈ Metric.closedBall θ₀ ρ,
      ∀ (j : Fin k) (x : Ω),
        |ψ θ j x - ψ θ' j x - ∑ i, psiDot ψ θ₀ x j i * (θ - θ') i|
          ≤ ψddot x * ρ * ‖θ - θ'‖)
    (n : ℕ) (Xs : Fin n → Ω) :
    ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ θ' ∈ Metric.closedBall θ₀ ρ, ∀ j : Fin k,
      |empiricalAvg (ψ θ j) n Xs - empiricalAvg (ψ θ' j) n Xs
          - ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (θ - θ') i|
        ≤ empiricalAvg ψddot n Xs * ρ * ‖θ - θ'‖ := by
  classical
  intro θ hθ θ' hθ' j
  -- Step 1: the empirical residual is the sample average of the pointwise residuals.
  have hrw : empiricalAvg (ψ θ j) n Xs - empiricalAvg (ψ θ' j) n Xs
      - ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (θ - θ') i
      = (n : ℝ)⁻¹ * ∑ l, (ψ θ j (Xs l) - ψ θ' j (Xs l)
          - ∑ i, psiDot ψ θ₀ (Xs l) j i * (θ - θ') i) := by
    have hA : empiricalAvg (ψ θ j) n Xs - empiricalAvg (ψ θ' j) n Xs
        = (n : ℝ)⁻¹ * ∑ l, (ψ θ j (Xs l) - ψ θ' j (Xs l)) := by
      simp only [empiricalAvg, Finset.sum_sub_distrib, mul_sub]
    have hC : ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (θ - θ') i
        = (n : ℝ)⁻¹ * ∑ l, ∑ i, psiDot ψ θ₀ (Xs l) j i * (θ - θ') i := by
      calc ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (θ - θ') i
          = ∑ i, (n : ℝ)⁻¹ * ∑ l, psiDot ψ θ₀ (Xs l) j i * (θ - θ') i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [empiricalAvg]
            rw [mul_assoc, Finset.sum_mul]
        _ = (n : ℝ)⁻¹ * ∑ i, ∑ l, psiDot ψ θ₀ (Xs l) j i * (θ - θ') i := by
            rw [← Finset.mul_sum]
        _ = (n : ℝ)⁻¹ * ∑ l, ∑ i, psiDot ψ θ₀ (Xs l) j i * (θ - θ') i := by
            rw [Finset.sum_comm]
    rw [hA, hC, ← mul_sub, ← Finset.sum_sub_distrib]
  -- Step 2: average the pointwise mean-value bound.
  have hstep : |∑ l, (ψ θ j (Xs l) - ψ θ' j (Xs l)
      - ∑ i, psiDot ψ θ₀ (Xs l) j i * (θ - θ') i)|
      ≤ ∑ l, (ψddot (Xs l) * ρ * ‖θ - θ'‖) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun l _ => hbound θ hθ θ' hθ' j (Xs l))
  have hfinal : ∑ l, (ψddot (Xs l) * ρ * ‖θ - θ'‖)
      = (∑ l, ψddot (Xs l)) * (ρ * ‖θ - θ'‖) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
  calc (n : ℝ)⁻¹ * |∑ l, (ψ θ j (Xs l) - ψ θ' j (Xs l)
        - ∑ i, psiDot ψ θ₀ (Xs l) j i * (θ - θ') i)|
      ≤ (n : ℝ)⁻¹ * ∑ l, (ψddot (Xs l) * ρ * ‖θ - θ'‖) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = empiricalAvg ψddot n Xs * ρ * ‖θ - θ'‖ := by
        rw [hfinal]
        simp only [empiricalAvg]
        ring

/-! ### Packaging `Ψₙ` as an `ApproximatesLinearOn` of the population Jacobian. -/

/-- **`Ψₙ` approximates the linear map of `A` on `closedBall θ₀ r`.** Combining the empirical
mean-value bound, which gives a coordinatewise `a·‖θ − θ'‖` residual against the *empirical*
Jacobian `ℙₙψ̇_{θ₀}`) with entrywise closeness `|(ℙₙψ̇_{θ₀})ⱼᵢ − Aⱼᵢ| ≤ b` of that Jacobian to
a fixed matrix `A` (in the application `A = V = Pψ̇_{θ₀}`), the bundled map `Ψₙ` satisfies

    `‖Ψₙθ − Ψₙθ' − A(θ − θ')‖ ≤ (k·a + k²·b)·‖θ − θ'‖`   on `closedBall θ₀ r`,

which is exactly `ApproximatesLinearOn Ψₙ A (closedBall θ₀ r) (k·a + k²·b)`. The `k` / `k²`
constants come from the crude coordinate bound `‖w‖ ≤ ∑ⱼ |wⱼ|`
(`euclidean_norm_le_sum_abs`) and `|wᵢ| ≤ ‖w‖`. -/
theorem approximatesLinearOn_empEstimatingMap {k : ℕ} {Ω : Type*}
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) {r : ℝ}
    (A : Matrix (Fin k) (Fin k) ℝ) {a b : ℝ} (hb : 0 ≤ b)
    (n : ℕ) (Xs : Fin n → Ω)
    (hmv : ∀ θ ∈ Metric.closedBall θ₀ r, ∀ θ' ∈ Metric.closedBall θ₀ r, ∀ j : Fin k,
      |empiricalAvg (ψ θ j) n Xs - empiricalAvg (ψ θ' j) n Xs
          - ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (θ - θ') i|
        ≤ a * ‖θ - θ'‖)
    (hVclose : ∀ j i : Fin k,
      |empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs - A j i| ≤ b) :
    ApproximatesLinearOn (fun θ => empEstimatingMap ψ θ n Xs)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) A) (Metric.closedBall θ₀ r)
      (Real.toNNReal ((k : ℝ) * a + (k : ℝ) ^ 2 * b)) := by
  classical
  intro θ hθ θ' hθ'
  have hnn : (0 : ℝ) ≤ ‖θ - θ'‖ := norm_nonneg _
  -- Coordinates of the residual vector.
  have hcoord : ∀ j : Fin k,
      ((fun θ => empEstimatingMap ψ θ n Xs) θ - (fun θ => empEstimatingMap ψ θ n Xs) θ'
        - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) A (θ - θ')) j
      = empiricalAvg (ψ θ j) n Xs - empiricalAvg (ψ θ' j) n Xs
        - ∑ i, A j i * (θ - θ') i := by
    intro j
    simp [empEstimatingMap, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
  -- Each coordinate: mean-value residual + Jacobian mismatch.
  have hj : ∀ j : Fin k,
      |empiricalAvg (ψ θ j) n Xs - empiricalAvg (ψ θ' j) n Xs
          - ∑ i, A j i * (θ - θ') i|
        ≤ a * ‖θ - θ'‖ + (k : ℝ) * b * ‖θ - θ'‖ := by
    intro j
    have hsplit : empiricalAvg (ψ θ j) n Xs - empiricalAvg (ψ θ' j) n Xs
          - ∑ i, A j i * (θ - θ') i
        = (empiricalAvg (ψ θ j) n Xs - empiricalAvg (ψ θ' j) n Xs
            - ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (θ - θ') i)
          + ∑ i, (empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs - A j i) * (θ - θ') i := by
      have hexp : ∑ i, (empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs - A j i) * (θ - θ') i
          = ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (θ - θ') i
            - ∑ i, A j i * (θ - θ') i := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hexp]; ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add (hmv θ hθ θ' hθ' j) ?_)
    calc |∑ i, (empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs - A j i) * (θ - θ') i|
        ≤ ∑ i, |(empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs - A j i) * (θ - θ') i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin k, b * ‖θ - θ'‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hVclose j i) (abs_coord_le_norm _ i) (abs_nonneg _) hb
      _ = (k : ℝ) * b * ‖θ - θ'‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  -- Sum the coordinates.
  have hcast : ((Real.toNNReal ((k : ℝ) * a + (k : ℝ) ^ 2 * b) : ℝ≥0) : ℝ)
      ≥ (k : ℝ) * a + (k : ℝ) ^ 2 * b := Real.le_coe_toNNReal _
  calc ‖(fun θ => empEstimatingMap ψ θ n Xs) θ - (fun θ => empEstimatingMap ψ θ n Xs) θ'
        - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) A (θ - θ')‖
      ≤ ∑ j, |((fun θ => empEstimatingMap ψ θ n Xs) θ
          - (fun θ => empEstimatingMap ψ θ n Xs) θ'
          - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) A (θ - θ')) j| :=
        euclidean_norm_le_sum_abs _
    _ ≤ ∑ _j : Fin k, (a * ‖θ - θ'‖ + (k : ℝ) * b * ‖θ - θ'‖) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [hcoord j]
        exact hj j
    _ = ((k : ℝ) * a + (k : ℝ) ^ 2 * b) * ‖θ - θ'‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ ((Real.toNNReal ((k : ℝ) * a + (k : ℝ) ^ 2 * b) : ℝ≥0) : ℝ) * ‖θ - θ'‖ :=
        mul_le_mul_of_nonneg_right hcast hnn

/-! ### A root of `Ψₙ` in a closed ball from quantitative surjectivity -/

/-- **Existence of a root of `Ψₙ` in `closedBall θ₀ r`.** If the empirical estimating map
`Ψₙ = ℙₙψ_·` approximates an invertible linear map `V'` on `closedBall θ₀ r` with constant
`c`, and `Ψₙθ₀` is small compared with `(‖V'⁻¹‖⁻¹ − c)·r`, then `Ψₙ` has a zero in that ball:

    `∃ θ ∈ closedBall θ₀ r, ∀ j, ℙₙψ_{θ,j} = 0`.

The good event uses the quantitative near-linearity supplied by the classical smoothness
conditions via
`approximatesLinearOn_empEstimatingMap`. The root is then produced by Mathlib's
`ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse` (the contraction half of the
inverse function theorem), applied with the nonlinear right inverse `V'.toNonlinearRightInverse`
whose norm constant is `‖V'.symm‖₊`. -/
theorem root_in_ball_of_approximatesLinearOn {k : ℕ} {Ω : Type*}
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) {r : ℝ} (hr : 0 ≤ r)
    (V' : EuclideanSpace ℝ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin k)) {c : ℝ≥0}
    (n : ℕ) (Xs : Fin n → Ω)
    (hALO : ApproximatesLinearOn (fun θ => empEstimatingMap ψ θ n Xs)
      (V' : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
      (Metric.closedBall θ₀ r) c)
    (hsmall : ‖empEstimatingMap ψ θ₀ n Xs‖
      ≤ ((‖(V'.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))‖₊ : ℝ)⁻¹ - c)
        * r) :
    ∃ θ ∈ Metric.closedBall θ₀ r, ∀ j : Fin k, empiricalAvg (ψ θ j) n Xs = 0 := by
  have hsurj := hALO.surjOn_closedBall_of_nonlinearRightInverse
    V'.toNonlinearRightInverse hr (Set.Subset.rfl)
  -- `0` lies in the image ball: `dist 0 (Ψₙ θ₀) = ‖Ψₙ θ₀‖ ≤ (‖V'⁻¹‖⁻¹ − c)·r`.
  have h0 : (0 : EuclideanSpace ℝ (Fin k)) ∈ Metric.closedBall
      ((fun θ => empEstimatingMap ψ θ n Xs) θ₀)
      (((V'.toNonlinearRightInverse.nnnorm : ℝ)⁻¹ - c) * r) := by
    rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg]
    exact hsmall
  obtain ⟨θ, hθmem, hθ⟩ := hsurj h0
  refine ⟨θ, hθmem, fun j => ?_⟩
  have := congrArg (fun v : EuclideanSpace ℝ (Fin k) => v j) hθ
  simpa [empEstimatingMap] using this

/-! ### The empirical good event has probability tending to one -/

set_option linter.unusedFintypeInType false in
/-- **Finite family of empirical averages: union bound over the WLLN.** For a finite
family `g : ι → Ω → ℝ` of measurable integrable functions, the probability that *some*
empirical average deviates from its mean by `ε` tends to `0`. Finite union bound over
`iid_lln_in_prob_seq` (`ForMathlib/IidWLLN.lean`). No measurability of the event is needed:
`measureReal_iUnion_fintype_le` is an outer-measure bound. -/
theorem finite_empiricalAvg_bad_prob_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] (g : ι → Ω → ℝ)
    (hg_meas : ∀ a, Measurable (g a)) (hg_int : ∀ a, Integrable (g a) P)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => μ.real {ξ | ∃ a : ι,
        ε ≤ |empiricalAvg (g a) n (fun i : Fin n => X i.val ξ) - ∫ x, g a x ∂P|})
      atTop (𝓝 0) := by
  classical
  have hone : ∀ a : ι, Tendsto (fun n => μ.real {ξ |
      ε ≤ |empiricalAvg (g a) n (fun i : Fin n => X i.val ξ) - ∫ x, g a x ∂P|})
      atTop (𝓝 0) := by
    intro a
    have h := AsymptoticStatistics.iid_lln_in_prob_seq P (g a) (hg_meas a) (hg_int a)
      μ X hX_meas hX_indep hX_id hX_law ε hε
    simpa [Real.norm_eq_abs] using h
  have hsum : Tendsto (fun n => ∑ a : ι, μ.real {ξ |
      ε ≤ |empiricalAvg (g a) n (fun i : Fin n => X i.val ξ) - ∫ x, g a x ∂P|})
      atTop (𝓝 0) := by
    simpa using tendsto_finset_sum (Finset.univ : Finset ι) fun a _ => hone a
  refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) hsum
  have hset : {ξ | ∃ a : ι,
      ε ≤ |empiricalAvg (g a) n (fun i : Fin n => X i.val ξ) - ∫ x, g a x ∂P|}
      = ⋃ a : ι, {ξ |
        ε ≤ |empiricalAvg (g a) n (fun i : Fin n => X i.val ξ) - ∫ x, g a x ∂P|} := by
    ext ξ; simp
  rw [hset]
  exact measureReal_iUnion_fintype_le _

/-- **The empirical good event has probability `→ 1`.** Applying the preceding finite-family bound to the three
families of empirical averages the `ApproximatesLinearOn` route needs — `ℙₙψ̈`, the Jacobian
entries `ℙₙψ̇_{θ₀,ⱼᵢ}`, and the estimating functions `ℙₙψ_{θ₀,j}` at the truth — the good
event

    `Aₙ,ε = {|ℙₙψ̈ − Pψ̈| < ε} ∩ {∀ j i, |(ℙₙψ̇_{θ₀})ⱼᵢ − Vⱼᵢ| < ε}
              ∩ {∀ j, |ℙₙψ_{θ₀,j}| < ε}`

has `μ.real Aₙ,ε → 1` for every fixed `ε > 0`. All three are ordinary scalar WLLN statements.
The complementary bad-event form is returned
alongside because the consistency half needs `μ.real Aᶜ → 0`, which does **not** follow from
`μ.real A → 1` without measurability (`μ.real` is an outer measure, D-2). -/
theorem empirical_goodEvent_prob_tendsto_one {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (ψddot : Ω → ℝ)
    (hψddot_meas : Measurable ψddot) (hψddot_int : Integrable ψddot P)
    (hpsiDot_meas : ∀ j i, Measurable (fun x => psiDot ψ θ₀ x j i))
    (hVint : ∀ j i, Integrable (fun x => psiDot ψ θ₀ x j i) P)
    (hψ_meas : ∀ j, Measurable (ψ θ₀ j)) (hψ_int : ∀ j, Integrable (ψ θ₀ j) P)
    (hPθ₀_zero : ∀ j, ∫ x, ψ θ₀ j x ∂P = 0)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => μ.real {ξ |
        ¬ (|empiricalAvg ψddot n (fun i : Fin n => X i.val ξ) - ∫ x, ψddot x ∂P| < ε
          ∧ (∀ j i : Fin k, |empiricalAvg (fun x => psiDot ψ θ₀ x j i) n
              (fun i : Fin n => X i.val ξ) - Vmat P ψ θ₀ j i| < ε)
          ∧ (∀ j : Fin k, |empiricalAvg (ψ θ₀ j) n (fun i : Fin n => X i.val ξ)| < ε))})
      atTop (𝓝 0) := by
  classical
  -- The finite index family: `ψ̈`, the `k²` Jacobian entries, the `k` estimating functions.
  set ι : Type := Unit ⊕ (Fin k × Fin k) ⊕ Fin k with hι
  set g : ι → Ω → ℝ := fun a => match a with
    | .inl _ => ψddot
    | .inr (.inl p) => fun x => psiDot ψ θ₀ x p.1 p.2
    | .inr (.inr j) => ψ θ₀ j with hg
  have hg_meas : ∀ a, Measurable (g a) := by
    rintro (_ | ⟨p⟩ | j)
    · exact hψddot_meas
    · exact hpsiDot_meas _ _
    · exact hψ_meas _
  have hg_int : ∀ a, Integrable (g a) P := by
    rintro (_ | ⟨p⟩ | j)
    · exact hψddot_int
    · exact hVint _ _
    · exact hψ_int _
  have hbad := finite_empiricalAvg_bad_prob_tendsto_zero P g hg_meas hg_int μ X hX_meas
    hX_indep hX_id hX_law hε
  refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) hbad
  refine measureReal_mono ?_ (by finiteness)
  intro ξ hξ
  simp only [Set.mem_setOf_eq, not_and_or, not_lt, not_forall] at hξ
  rcases hξ with h | h | h
  · exact ⟨.inl (), h⟩
  · obtain ⟨j, i, hji⟩ := h
    exact ⟨.inr (.inl (j, i)), by simpa [g, Vmat] using hji⟩
  · obtain ⟨j, hj⟩ := h
    refine ⟨.inr (.inr j), ?_⟩
    simpa [g, hPθ₀_zero j] using hj

/-! ### Diagonal δ-extraction -/

/-- **Diagonal δ-extraction.** From the per-`δ` convergence `P(K n δ) → 1`,
extract a single sequence `δₙ ↓ 0` (all positive, `≤ δ₀`) along which `P(K n δₙ) → 1`.
Wraps `ForMathlib.exists_seq_tendsto_zero_of_forall_tendsto` with `p n δ := μ.real (K n δ)`
(`≤ 1` as a probability). vdV p.69 "there exists `δₙ ↓ 0` such that `P(Kₙ,δₙ) → 1`." -/
theorem diagonal_delta_extraction {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (K : ℕ → ℝ → Set Ξ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hK : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → Tendsto (fun n => μ.real (K n δ)) atTop (𝓝 1)) :
    ∃ δseq : ℕ → ℝ, (∀ n, 0 < δseq n) ∧ (∀ n, δseq n ≤ δ₀) ∧ Tendsto δseq atTop (𝓝 0)
      ∧ Tendsto (fun n => μ.real (K n (δseq n))) atTop (𝓝 1) := by
  -- The `ForMathlib` diagonal brick demands the `n`-limit for **every** `δ > 0`, whereas `hK`
  -- only supplies it for `δ ≤ δ₀`.  Feed it the *clamped* family `p n δ = μ(Kₙ, min δ δ₀)`,
  -- whose sections do converge for every `δ > 0` because `0 < min δ δ₀ ≤ δ₀`.
  obtain ⟨δ', hδ'pos, hδ'zero, hδ'lim⟩ :=
    AsymptoticStatistics.exists_seq_tendsto_zero_of_forall_tendsto
      (fun n δ => μ.real (K n (min δ δ₀)))
      (fun _ _ => measureReal_le_one)
      (fun δ hδ => hK (min δ δ₀) (lt_min hδ hδ₀) (min_le_right _ _))
  -- The clamp is absorbed: `δseq n := min (δ' n) δ₀` is exactly the argument at which the
  -- brick's conclusion already evaluates `K n`.
  refine ⟨fun n => min (δ' n) δ₀, fun n => lt_min (hδ'pos n) hδ₀,
    fun n => min_le_right _ _, ?_, hδ'lim⟩
  exact squeeze_zero (fun n => (lt_min (hδ'pos n) hδ₀).le) (fun n => min_le_left _ _) hδ'zero

/-! ### Existence and consistency of roots (vdV Theorem 5.42 (i)+(ii)) -/

/-- **Classical Z-estimator root existence and consistency — vdV Theorem 5.42 (i)+(ii)**
(§*5.6, book p.68-69).

Under the conditions of Theorem 5.41 (classical smoothness: `θ ↦ ψ_θ(x)` twice continuously
differentiable, `Pψ_{θ₀} = 0`, `P‖ψ_{θ₀}‖² < ∞`, `V = Pψ̇_{θ₀}` nonsingular, second-order
partials dominated by an integrable `ψ̈`):

* the probability that the equation `ℙₙψ_θ = 0` has at least one root in `Θ` tends to `1`;
* there exists a sequence of roots `θ̂ₙ` (measurable-selection-free, part of the conclusion)
  with `θ̂ₙ →ₚ θ₀`.

The proof combines `empirical_meanValue_bound`, `approximatesLinearOn_empEstimatingMap`,
`root_in_ball_of_approximatesLinearOn`, `empirical_goodEvent_prob_tendsto_one`, and
`diagonal_delta_extraction`. The estimator `θ̂ₙ` is **existentially** produced, without a
`Measurable θ̂` claim: `μ.real` is total on arbitrary sets, matching
vdV's "clairvoyant statistician" caveat, book p.69). -/
theorem classical_zEstimator_root_exists_consistent
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
    (hX_law : μ.map (X 0) = P) :
    TendstoInnerProbOne μ (fun n => {ξ | ∃ θ ∈ Θ, ∀ j,
        empiricalAvg (ψ θ j) n (fun i : Fin n => X i.val ξ) = 0})
    ∧ ∃ θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k),
        TendstoInnerProbOne μ (fun n => {ξ | ∀ j,
            empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) j) n
              (fun i : Fin n => X i.val ξ) = 0})
        ∧ TendstoInProbZero (fun _ : ℕ => μ)
            (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) := by
  classical
  have hunivR : μ.real (Set.univ : Set Ξ) = 1 := by simp
  -- ### Degenerate case `k = 0`: no estimating equations, `Θ ∋ θ₀` is the only witness needed.
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    refine ⟨?_, ⟨fun _ _ => θ₀, ?_, ?_⟩⟩
    · refine ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ, fun _ ξ _ => ?_, ?_⟩
      · exact ⟨θ₀, hθ₀, fun j => j.elim0⟩
      · simp only [hunivR]
        exact tendsto_const_nhds
    · refine ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ, fun _ _ _ j => j.elim0, ?_⟩
      simp only [hunivR]
      exact tendsto_const_nhds
    · intro ε hε
      refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_)
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      simp [hε.not_ge]
  -- ### Main case `k ≥ 1`.
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hψddot_nonneg : ∀ x, 0 ≤ ψddot x := fun x =>
    le_trans (norm_nonneg _) (hdom θ₀ (Metric.mem_closedBall_self hρ.le) ⟨0, hk⟩ x)
  set D : ℝ := ∫ x, ψddot x ∂P with hD
  have hD0 : 0 ≤ D := integral_nonneg hψddot_nonneg
  set Bc : ℝ := D + 1 with hBc
  have hBc0 : 0 < Bc := by rw [hBc]; linarith
  -- Integrability / measurability side conditions for the WLLN family.
  have hpsiDot_meas : ∀ j i, Measurable (fun x => psiDot ψ θ₀ x j i) :=
    psiDot_measurable ψ θ₀ Θ hΘ_open hθ₀ hψ_meas hC2
  have hψ_int : ∀ j : Fin k, Integrable (ψ θ₀ j) P := by
    intro j
    have hmem : MemLp (ψ θ₀ j) 2 P := by
      refine hψ_L2.mono ((hψ_meas θ₀ j).aestronglyMeasurable) ?_
      filter_upwards with x
      simpa [Real.norm_eq_abs, psiVec] using abs_coord_le_norm (psiVec ψ θ₀ x) j
    exact hmem.integrable (by norm_num)
  -- ### The invertible linear model `V'` of the population Jacobian `V = Pψ̇_{θ₀}`.
  obtain ⟨u, hu⟩ := ((Matrix.isUnit_iff_isUnit_det _).mpr hV).map
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k))
  set V' : EuclideanSpace ℝ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin k) :=
    ContinuousLinearEquiv.unitsEquiv ℝ _ u with hV'def
  have hV'coe : (V' : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀) := by
    ext x
    rw [← hu, hV'def]
    simp [ContinuousLinearEquiv.unitsEquiv_apply]
  set Nv : ℝ :=
    (‖(V'.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))‖₊ : ℝ) with hNv
  have hNv0 : 0 < Nv := by
    by_contra hcon
    push_neg at hcon
    have hz : Nv = 0 := le_antisymm hcon (by rw [hNv]; positivity)
    set v : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single (⟨0, hk⟩ : Fin k) (1 : ℝ) with hv
    have hvn : ‖v‖ = 1 := by rw [hv, PiLp.norm_single]; simp
    have hle := (V'.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)).le_opNorm
      (V' v)
    rw [ContinuousLinearEquiv.coe_coe, V'.symm_apply_apply, hvn] at hle
    rw [show ‖(V'.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))‖ = Nv from
      by rw [hNv, coe_nnnorm], hz, zero_mul] at hle
    linarith
  -- ### Radius bound and the `ε` tolerance attached to a radius.
  set epsOf : ℝ → ℝ := fun r =>
    min 1 (min (Nv⁻¹ / (4 * (k : ℝ) ^ 2)) (Nv⁻¹ * r / (4 * (k : ℝ)))) with heps
  have heps_pos : ∀ r : ℝ, 0 < r → 0 < epsOf r := by
    intro r hr
    refine lt_min one_pos (lt_min (div_pos (inv_pos.mpr hNv0) (by positivity)) ?_)
    exact div_pos (mul_pos (inv_pos.mpr hNv0) hr) (by positivity)
  set r₀ : ℝ := min ρ (Nv⁻¹ / (4 * (k : ℝ) * Bc)) with hr₀def
  have hr₀0 : 0 < r₀ :=
    lt_min hρ (div_pos (inv_pos.mpr hNv0) (by positivity))
  -- ### Deterministic core: on the good bounds, `Ψₙ` has a root in `closedBall θ₀ r`.
  have hcore : ∀ (r : ℝ), 0 < r → r ≤ r₀ → ∀ (n : ℕ) (Xs : Fin n → Ω),
      |empiricalAvg ψddot n Xs - D| < epsOf r →
      (∀ j i : Fin k,
        |empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs - Vmat P ψ θ₀ j i| < epsOf r) →
      (∀ j : Fin k, |empiricalAvg (ψ θ₀ j) n Xs| < epsOf r) →
      ∃ θ ∈ Metric.closedBall θ₀ r, ∀ j : Fin k, empiricalAvg (ψ θ j) n Xs = 0 := by
    intro r hr hrr₀ n Xs hg1 hg2 hg3
    have hepsr := heps_pos r hr
    set W : ℝ := empiricalAvg ψddot n Xs with hW
    have hW0 : 0 ≤ W := by
      rw [hW, empiricalAvg]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => hψddot_nonneg _)
    have hWB : W ≤ Bc := by
      have h1 := (abs_lt.mp hg1).2
      have h2 : epsOf r ≤ 1 := min_le_left _ _
      rw [hBc]; linarith
    -- (a) `Ψₙ` approximates `V` on the ball, with constant `k·W·r + k²·ε`.
    have hsubball : Metric.closedBall θ₀ r ⊆ Metric.closedBall θ₀ ρ :=
      Metric.closedBall_subset_closedBall (hrr₀.trans (min_le_left _ _))
    have hmv := empirical_meanValue_bound ψ θ₀ ψddot
      (pointwise_meanValue_bound ψ θ₀ Θ ψddot hr hΘ_open (hsubball.trans hball) hC2
        (fun z hz => hdom z (hsubball hz))) n Xs
    have hALO0 := approximatesLinearOn_empEstimatingMap ψ θ₀ (Vmat P ψ θ₀)
      (a := W * r) (b := epsOf r) hepsr.le n Xs hmv (fun j i => (hg2 j i).le)
    have hALO : ApproximatesLinearOn (fun θ => empEstimatingMap ψ θ n Xs)
        (V' : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
        (Metric.closedBall θ₀ r)
        (Real.toNNReal ((k : ℝ) * (W * r) + (k : ℝ) ^ 2 * epsOf r)) := by
      rw [hV'coe]; exact hALO0
    -- (b) the constant is `≤ Nv⁻¹ / 2`.
    have hc_nonneg : (0 : ℝ) ≤ (k : ℝ) * (W * r) + (k : ℝ) ^ 2 * epsOf r := by
      have h1 : (0 : ℝ) ≤ (k : ℝ) * (W * r) :=
        mul_nonneg hkR.le (mul_nonneg hW0 hr.le)
      have h2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 * epsOf r := mul_nonneg (by positivity) hepsr.le
      linarith
    have hcval : ((Real.toNNReal ((k : ℝ) * (W * r) + (k : ℝ) ^ 2 * epsOf r) : ℝ≥0) : ℝ)
        = (k : ℝ) * (W * r) + (k : ℝ) ^ 2 * epsOf r := Real.coe_toNNReal _ hc_nonneg
    have hpart1 : (k : ℝ) * (W * r) ≤ Nv⁻¹ / 4 := by
      have hrle : r ≤ Nv⁻¹ / (4 * (k : ℝ) * Bc) := hrr₀.trans (min_le_right _ _)
      have h1 : (k : ℝ) * (W * r) ≤ (k : ℝ) * (Bc * r) := by
        refine mul_le_mul_of_nonneg_left ?_ hkR.le
        exact mul_le_mul_of_nonneg_right hWB hr.le
      refine h1.trans ?_
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (k : ℝ) * Bc)] at hrle
      nlinarith [hrle, hkR, hBc0]
    have hpart2 : (k : ℝ) ^ 2 * epsOf r ≤ Nv⁻¹ / 4 := by
      have h1 : epsOf r ≤ Nv⁻¹ / (4 * (k : ℝ) ^ 2) :=
        (min_le_right _ _).trans (min_le_left _ _)
      have h2 : (k : ℝ) ^ 2 * epsOf r ≤ (k : ℝ) ^ 2 * (Nv⁻¹ / (4 * (k : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      refine h2.trans (le_of_eq ?_)
      field_simp
    -- (c) `‖Ψₙ θ₀‖ ≤ Nv⁻¹ · r / 4`.
    have hsmall0 : ‖empEstimatingMap ψ θ₀ n Xs‖ ≤ (k : ℝ) * epsOf r := by
      refine (euclidean_norm_le_sum_abs _).trans ?_
      calc ∑ j, |empEstimatingMap ψ θ₀ n Xs j| ≤ ∑ _j : Fin k, epsOf r := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [empEstimatingMap_apply]
            exact (hg3 j).le
        _ = (k : ℝ) * epsOf r := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsmall1 : (k : ℝ) * epsOf r ≤ Nv⁻¹ * r / 4 := by
      have h1 : epsOf r ≤ Nv⁻¹ * r / (4 * (k : ℝ)) :=
        (min_le_right _ _).trans (min_le_right _ _)
      have h2 : (k : ℝ) * epsOf r ≤ (k : ℝ) * (Nv⁻¹ * r / (4 * (k : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 hkR.le
      refine h2.trans (le_of_eq ?_)
      field_simp
    have hsmall : ‖empEstimatingMap ψ θ₀ n Xs‖
        ≤ (Nv⁻¹ - ((Real.toNNReal ((k : ℝ) * (W * r) + (k : ℝ) ^ 2 * epsOf r) : ℝ≥0) : ℝ)) * r := by
      refine (hsmall0.trans hsmall1).trans ?_
      rw [hcval]
      have hNvi : 0 < Nv⁻¹ := inv_pos.mpr hNv0
      nlinarith [hpart1, hpart2, hr, hNvi]
    exact root_in_ball_of_approximatesLinearOn ψ θ₀ hr.le V' n Xs hALO hsmall
  -- ### The bad event and its vanishing probability.
  set Bad : ℕ → ℝ → Set Ξ := fun n r => {ξ |
      ¬ (|empiricalAvg ψddot n (fun i : Fin n => X i.val ξ) - ∫ x, ψddot x ∂P| < epsOf r
        ∧ (∀ j i : Fin k, |empiricalAvg (fun x => psiDot ψ θ₀ x j i) n
            (fun i : Fin n => X i.val ξ) - Vmat P ψ θ₀ j i| < epsOf r)
        ∧ (∀ j : Fin k, |empiricalAvg (ψ θ₀ j) n (fun i : Fin n => X i.val ξ)| < epsOf r))}
    with hBadDef
  have hemp_meas : ∀ (n : ℕ) (g : Ω → ℝ), Measurable g →
      Measurable (fun ξ : Ξ => empiricalAvg g n (fun i : Fin n => X i.val ξ)) := by
    intro n g hg
    unfold empiricalAvg
    exact measurable_const.mul
      (Finset.measurable_sum Finset.univ (fun i _ => hg.comp (hX_meas i.val)))
  have hBad_meas : ∀ (n : ℕ) (r : ℝ), MeasurableSet (Bad n r) := by
    intro n r
    rw [hBadDef]
    apply MeasurableSet.compl
    refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_lt
        ((hemp_meas n ψddot hψddot_meas).sub measurable_const).abs measurable_const
    · have hI : MeasurableSet (⋂ j : Fin k, ⋂ i : Fin k, {ξ : Ξ |
          |empiricalAvg (fun x => psiDot ψ θ₀ x j i) n
            (fun l : Fin n => X l.val ξ) - Vmat P ψ θ₀ j i| < epsOf r}) := by
        refine MeasurableSet.iInter fun j => ?_
        refine MeasurableSet.iInter fun i => ?_
        exact measurableSet_lt
          ((hemp_meas n (fun x => psiDot ψ θ₀ x j i) (hpsiDot_meas j i)).sub
            measurable_const).abs measurable_const
      refine Eq.mpr (congrArg MeasurableSet ?_) hI
      ext ξ
      change (∀ j i : Fin k, |empiricalAvg (fun x => psiDot ψ θ₀ x j i) n
        (fun l : Fin n => X l.val ξ) - Vmat P ψ θ₀ j i| < epsOf r) ↔ _
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
    · have hI : MeasurableSet (⋂ j : Fin k, {ξ : Ξ |
          |empiricalAvg (ψ θ₀ j) n (fun l : Fin n => X l.val ξ)| < epsOf r}) := by
        refine MeasurableSet.iInter fun j => ?_
        exact measurableSet_lt (hemp_meas n (ψ θ₀ j) (hψ_meas θ₀ j)).abs measurable_const
      refine Eq.mpr (congrArg MeasurableSet ?_) hI
      ext ξ
      change (∀ j : Fin k,
        |empiricalAvg (ψ θ₀ j) n (fun l : Fin n => X l.val ξ)| < epsOf r) ↔ _
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
  have hbad : ∀ r : ℝ, 0 < r → Tendsto (fun n => μ.real (Bad n r)) atTop (𝓝 0) := by
    intro r hr
    exact empirical_goodEvent_prob_tendsto_one P ψ θ₀ ψddot hψddot_meas hψddot_int
      hpsiDot_meas hVint (fun j => hψ_meas θ₀ j) hψ_int hPθ₀_zero μ X hX_meas hX_indep
      hX_id hX_law (heps_pos r hr)
  -- Off the bad event, the deterministic core applies.
  have hroot_of_notBad : ∀ (r : ℝ), 0 < r → r ≤ r₀ → ∀ (n : ℕ) (ξ : Ξ), ξ ∉ Bad n r →
      ∃ θ ∈ Metric.closedBall θ₀ r, ∀ j : Fin k,
        empiricalAvg (ψ θ j) n (fun i : Fin n => X i.val ξ) = 0 := by
    intro r hr hrr₀ n ξ hξ
    rw [hBadDef] at hξ
    simp only [Set.mem_setOf_eq, not_not] at hξ
    exact hcore r hr hrr₀ n _ hξ.1 hξ.2.1 hξ.2.2
  -- The measurable complement of a vanishing bad event is an inner witness of probability one.
  have hinner_one : ∀ (S : ℕ → Set Ξ) (r : ℕ → ℝ),
      (∀ n, (Bad n (r n))ᶜ ⊆ S n) → Tendsto (fun n => μ.real (Bad n (r n))) atTop (𝓝 0) →
      TendstoInnerProbOne μ S := by
    intro S r hsub hlim
    refine ⟨fun n => (Bad n (r n))ᶜ, fun n => (hBad_meas n (r n)).compl, hsub, ?_⟩
    have hcomp : Tendsto (fun n => (1 : ℝ) - μ.real (Bad n (r n))) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hlim
    convert hcomp using 1
    ext n
    rw [measureReal_compl (hBad_meas n (r n)), hunivR]
  -- ### First conjunct: a root exists in `Θ` with probability `→ 1`.
  have hfirst : TendstoInnerProbOne μ (fun n => {ξ | ∃ θ ∈ Θ, ∀ j,
      empiricalAvg (ψ θ j) n (fun i : Fin n => X i.val ξ) = 0}) := by
    refine hinner_one _ (fun _ => r₀) (fun n ξ hξ => ?_) (hbad r₀ hr₀0)
    obtain ⟨θ, hθmem, hθ⟩ := hroot_of_notBad r₀ hr₀0 le_rfl n ξ hξ
    exact ⟨θ, hball (Metric.closedBall_subset_closedBall (min_le_left _ _) hθmem), hθ⟩
  refine ⟨hfirst, ?_⟩
  -- ### Second conjunct: diagonalise over radii `rₘ ↓ 0`.
  obtain ⟨δ', hδ'pos, hδ'zero, hδ'lim⟩ :=
    AsymptoticStatistics.exists_seq_tendsto_zero_of_forall_tendsto
      (fun n r => 1 - μ.real (Bad n (min r r₀)))
      (fun n r => by
        change (1 : ℝ) - μ.real (Bad n (min r r₀)) ≤ 1
        linarith [measureReal_nonneg (μ := μ) (s := Bad n (min r r₀))])
      (fun r hr => by simpa using tendsto_const_nhds.sub (hbad (min r r₀) (lt_min hr hr₀0)))
  set rseq : ℕ → ℝ := fun n => min (δ' n) r₀ with hrseq
  have hrseq_pos : ∀ n, 0 < rseq n := fun n => lt_min (hδ'pos n) hr₀0
  have hrseq_le : ∀ n, rseq n ≤ r₀ := fun n => min_le_right _ _
  have hrseq_zero : Tendsto rseq atTop (𝓝 0) :=
    squeeze_zero (fun n => (hrseq_pos n).le) (fun n => min_le_left _ _) hδ'zero
  have hbaddiag : Tendsto (fun n => μ.real (Bad n (rseq n))) atTop (𝓝 0) := by
    have h : Tendsto (fun n => (1 : ℝ) - (1 - μ.real (Bad n (min (δ' n) r₀)))) atTop
        (𝓝 ((1 : ℝ) - 1)) := tendsto_const_nhds.sub hδ'lim
    simpa [hrseq] using h
  -- The (non-measurable, D-2) root selection.
  set θhat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k) := fun n Xs =>
    if h : ∃ θ ∈ Metric.closedBall θ₀ (rseq n), ∀ j : Fin k, empiricalAvg (ψ θ j) n Xs = 0
      then h.choose else θ₀ with hθhat
  have hθhat_spec : ∀ (n : ℕ) (Xs : Fin n → Ω),
      (∃ θ ∈ Metric.closedBall θ₀ (rseq n), ∀ j : Fin k, empiricalAvg (ψ θ j) n Xs = 0) →
      θhat n Xs ∈ Metric.closedBall θ₀ (rseq n)
        ∧ ∀ j : Fin k, empiricalAvg (ψ (θhat n Xs) j) n Xs = 0 := by
    intro n Xs h
    rw [hθhat]
    simp only [dif_pos h]
    exact h.choose_spec
  refine ⟨θhat, ?_, ?_⟩
  · refine hinner_one _ rseq (fun n ξ hξ => ?_) hbaddiag
    exact (hθhat_spec n _
      (hroot_of_notBad (rseq n) (hrseq_pos n) (hrseq_le n) n ξ hξ)).2
  · intro ε hε
    refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ hbaddiag
    have hev : ∀ᶠ n in atTop, rseq n < ε := by
      have := Metric.tendsto_atTop.mp hrseq_zero ε hε
      obtain ⟨N, hN⟩ := this
      filter_upwards [eventually_ge_atTop N] with n hn
      have := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_pos (hrseq_pos n)] at this
      exact this
    filter_upwards [hev] with n hn
    refine measureReal_mono (fun ξ hξ => ?_) (by finiteness)
    by_contra hcon
    obtain ⟨hmem, -⟩ :=
      hθhat_spec n _ (hroot_of_notBad (rseq n) (hrseq_pos n) (hrseq_le n) n ξ hcon)
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    simp only [Set.mem_setOf_eq] at hξ
    linarith

/-- **Outer-measure form of classical Z-estimator root existence and consistency.**

The inner-probability statement `classical_zEstimator_root_exists_consistent` implies this
outer-measure limit. No measurability of the selected roots or of the target root events is
assumed. -/
theorem classical_zEstimator_root_exists_consistent_outer
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
    (hX_law : μ.map (X 0) = P) :
    Filter.Tendsto (fun n => μ.real {ξ | ∃ θ ∈ Θ, ∀ j,
        empiricalAvg (ψ θ j) n (fun i : Fin n => X i.val ξ) = 0}) Filter.atTop (𝓝 1)
    ∧ ∃ θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k),
        Filter.Tendsto (fun n => μ.real {ξ | ∀ j,
            empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) j) n
              (fun i : Fin n => X i.val ξ) = 0}) Filter.atTop (𝓝 1)
        ∧ TendstoInProbZero (fun _ : ℕ => μ)
            (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) := by
  obtain ⟨hexists, θ_hat, hroot, hcons⟩ :=
    classical_zEstimator_root_exists_consistent P Θ hΘ_open ψ θ₀ hθ₀ hψ_meas hC2 hPθ₀_zero
      hψ_L2 hVint hV ψddot hψddot_meas hψddot_int hρ hball hdom μ X hX_meas hX_indep hX_id
      hX_law
  exact ⟨hexists.tendsto_measureReal, θ_hat, hroot.tendsto_measureReal, hcons⟩

end AsymptoticStatistics.ClassicalZEstimator
