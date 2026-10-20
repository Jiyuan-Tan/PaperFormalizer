module
public import StatLean.AsymptoticStatistics.ClassicalZEstimator.Witness

@[expose] public section

/-!
# A nonlinear example for the classical Z-estimator theorems

This file gives a concrete nonlinear instance of vdV Theorems 5.41 and 5.42. It reuses
the one-dimensional standard-normal model, i.i.d. sample, and sample-mean estimator from
`ClassicalZEstimator.Witness`, but replaces the affine estimating function by

`npsi θ x = (x - θ 0) * (1 + (θ 0)^2)`.

Its second parameter derivative is genuinely nonzero and is dominated on the unit ball by
the integrable function `2 * |x| + 6`.  Thus the witness exercises the classical second-order
domination hypothesis rather than satisfying it only through a vanishing derivative.  The
last three theorems apply the general results to this example. The two conclusions associated
with Theorem 5.42 are stated using inner probability, so their events have measurable inner
approximations whose probabilities tend to one.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open AsymptoticStatistics AsymptoticStatistics.EmpiricalProcess
open scoped Matrix

namespace AsymptoticStatistics.ClassicalZEstimator.NonlinearWitness

open Witness

/-! ## 1. Nonlinear score and criterion -/

/-- The nonlinear estimating function
`npsi θ _ x = (x - θ 0) * (1 + (θ 0)^2)`.

It is total for every parameter and observation;
the sole equation index is ignored because `Fin 1` has only one coordinate. -/
noncomputable def npsi : E1 → Fin 1 → ℝ → ℝ :=
  fun θ _ x => (x - θ 0) * (1 + (θ 0) ^ 2)

/-- The nonnegative domination envelope `npsiDdot x = 2 * |x| + 6` for the nonlinear score.

This concrete envelope satisfies vdV's second-derivative domination condition. It is total,
measurable, integrable under `wP`, and remains at least
`6` even when `x = 0`. -/
noncomputable def npsiDdot : ℝ → ℝ := fun x => 2 * |x| + 6

/-- The criterion
`nm θ x = x*(θ 0) + x*(θ 0)^3/3 - (θ 0)^2/2 - (θ 0)^4/4`, whose parameter
gradient is `npsi`.

This polynomial primitive realizes the local-maximum assertion of vdV Theorem 5.42. It is
total for all real observations and parameters;
division is only by the fixed nonzero numerals `2`, `3`, and `4`. -/
noncomputable def nm : E1 → ℝ → ℝ := fun θ x =>
  x * θ 0 + x * (θ 0) ^ 3 / 3 - (θ 0) ^ 2 / 2 - (θ 0) ^ 4 / 4

/-! ## 2. First and second derivatives -/

/-- The exact first Fréchet derivative of the nonlinear score.  Its scalar coefficient is
`2*x*(θ 0) - 1 - 3*(θ 0)^2` and its direction is the coordinate functional `L1`.

This identity supplies the differentiability assumption of the classical theorems. -/
lemma n_hasFDerivAt_npsi (x : ℝ) (j : Fin 1) (θ : E1) :
    HasFDerivAt (fun θ' : E1 => npsi θ' j x)
      ((2 * x * θ 0 - 1 - 3 * (θ 0) ^ 2) • L1) θ := by
  have hg : HasDerivAt (fun t : ℝ => (x - t) * (1 + t ^ 2))
      (2 * x * θ 0 - 1 - 3 * (θ 0) ^ 2) (θ 0) := by
    convert! ((hasDerivAt_const (θ 0) x).sub (hasDerivAt_id (θ 0))).mul
      ((hasDerivAt_const (θ 0) 1).add ((hasDerivAt_id (θ 0)).pow 2)) using 1
    all_goals
      simp [id_eq]
      ring
  simpa only [npsi, Function.comp_apply, L1_apply] using!
    hg.comp_hasFDerivAt θ L1.hasFDerivAt

/-- The nonlinear score is twice continuously differentiable on the full parameter space.

The open parameter set in this example is the full space `univ`. -/
lemma n_hC2 (j : Fin 1) (x : ℝ) :
    ContDiffOn ℝ 2 (fun θ : E1 => npsi θ j x) (Set.univ : Set E1) := by
  apply ContDiff.contDiffOn
  unfold npsi
  fun_prop

/-- Pointwise formula for the second iterated Fréchet derivative:
`D² npsi(θ,x)[v₀,v₁] = (2*x - 6*(θ 0)) * (v₀ 0) * (v₁ 0)`.

The arguments are represented as a `Fin 2 → E1` family. -/
lemma n_iteratedFDeriv_two_apply (θ : E1) (j : Fin 1) (x : ℝ) (v : Fin 2 → E1) :
    iteratedFDeriv ℝ 2 (fun θ' : E1 => npsi θ' j x) θ v =
      (2 * x - 6 * θ 0) * (v 0) 0 * (v 1) 0 := by
  have hf : (fderiv ℝ fun θ' : E1 => npsi θ' j x) =
      fun θ' => (2 * x * θ' 0 - 1 - 3 * (θ' 0) ^ 2) • L1 :=
    funext fun θ' => (n_hasFDerivAt_npsi x j θ').fderiv
  have hg : HasDerivAt (fun t : ℝ => 2 * x * t - 1 - 3 * t ^ 2)
      (2 * x - 6 * θ 0) (θ 0) := by
    convert! (((hasDerivAt_const (θ 0) (2 * x)).mul (hasDerivAt_id (θ 0))).sub
      (hasDerivAt_const (θ 0) 1)).sub
      ((hasDerivAt_const (θ 0) 3).mul ((hasDerivAt_id (θ 0)).pow 2)) using 1
    all_goals
      simp [id_eq]
      ring
  have hscalar : HasFDerivAt (fun θ' : E1 =>
      2 * x * θ' 0 - 1 - 3 * (θ' 0) ^ 2) ((2 * x - 6 * θ 0) • L1) θ := by
    simpa only [Function.comp_apply, L1_apply] using!
      hg.comp_hasFDerivAt θ L1.hasFDerivAt
  have hcoeff : HasFDerivAt (fun θ' : E1 =>
      (2 * x * θ' 0 - 1 - 3 * (θ' 0) ^ 2) • L1)
      (((2 * x - 6 * θ 0) • L1).smulRight L1) θ :=
    hscalar.smul_const L1
  rw [iteratedFDeriv_two_apply, hf, hcoeff.fderiv]
  rfl

/-- Operator-norm bound for the nonlinear score's second derivative.

This converts the coordinatewise formula into the operator-norm bound used by the
domination hypothesis. -/
lemma n_iteratedFDeriv_two_norm_le (θ : E1) (j : Fin 1) (x : ℝ) :
    ‖iteratedFDeriv ℝ 2 (fun θ' : E1 => npsi θ' j x) θ‖ ≤ |2 * x - 6 * θ 0| := by
  apply ContinuousMultilinearMap.opNorm_le_bound (abs_nonneg _)
  intro v
  rw [n_iteratedFDeriv_two_apply, Real.norm_eq_abs]
  simp only [abs_mul]
  rw [← norm_E1 (v 0), ← norm_E1 (v 1), Fin.prod_univ_two]
  ring_nf
  exact le_refl (|x * 2 - θ 0 * 6| * ‖v 0‖ * ‖v 1‖)

/-- The second derivative used by the witness is genuinely nonzero: at `θ = 0` and `x = 1`
it is a nonzero continuous bilinear map.

Thus the example genuinely uses a nonzero second derivative. -/
lemma n_second_derivative_nonzero :
    iteratedFDeriv ℝ 2 (fun θ : E1 => npsi θ (0 : Fin 1) 1) (0 : E1) ≠ 0 := by
  intro hzero
  let v : Fin 2 → E1 := fun _ => EuclideanSpace.single 0 (1 : ℝ)
  have happ : iteratedFDeriv ℝ 2 (fun θ : E1 => npsi θ (0 : Fin 1) 1)
      (0 : E1) v = (0 : ℝ) := by
    rw [hzero]
    rfl
  rw [n_iteratedFDeriv_two_apply] at happ
  norm_num [v, EuclideanSpace.single] at happ

/-- On the closed unit ball around zero, `npsiDdot` dominates the full operator norm of the
second derivative.

The domination holds on the closed unit ball required by `hdom`. -/
lemma n_hdom (θ : E1)
    -- Restriction to the neighborhood on which the domination bound is asserted.
    (_hθ : θ ∈ Metric.closedBall (0 : E1) 1) (j : Fin 1) (x : ℝ) :
    ‖iteratedFDeriv ℝ 2 (fun θ' : E1 => npsi θ' j x) θ‖ ≤ npsiDdot x := by
  have hθnorm : ‖θ‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using _hθ
  have hθcoord : |θ 0| ≤ 1 := by
    rw [← norm_E1]
    exact hθnorm
  calc
    ‖iteratedFDeriv ℝ 2 (fun θ' : E1 => npsi θ' j x) θ‖
        ≤ |2 * x - 6 * θ 0| := n_iteratedFDeriv_two_norm_le θ j x
    _ ≤ |2 * x| + |6 * θ 0| := abs_sub _ _
    _ = 2 * |x| + 6 * |θ 0| := by norm_num [abs_mul]
    _ ≤ 2 * |x| + 6 := by nlinarith
    _ = npsiDdot x := rfl

/-! ## 3. Classical setup hypotheses -/

/-- The nonlinear estimating functions are measurable in the observation for every fixed
parameter and coordinate.

This verifies the measurability assumption for the example. -/
lemma n_hpsi_meas : ∀ (θ : E1) (j : Fin 1), Measurable (npsi θ j) := by
  intro θ j
  unfold npsi
  fun_prop

/-- At the true parameter `θ₀ = 0`, the nonlinear score equals the identity and has mean zero
under the standard Gaussian witness law.

This verifies `Pψ_{θ₀}=0` for the example. -/
lemma n_hPθ₀_zero (j : Fin 1) : ∫ x, npsi (0 : E1) j x ∂wP = 0 := by
  simpa [npsi, wpsi] using w_hPθ₀_zero j

/-- The bundled nonlinear score at `θ₀ = 0` lies in `L²(wP)`.

At zero it reduces to the identity score. -/
lemma n_hpsi_L2 : MemLp (psiVec npsi (0 : E1)) 2 wP := by
  have hvec : psiVec npsi (0 : E1) = psiVec wpsi (0 : E1) := by
    funext x
    ext j
    simp [psiVec, npsi, wpsi]
  rw [hvec]
  exact w_hψ_L2

/-- The entrywise Jacobian at `θ₀ = 0` is the constant `-1` matrix entry.

This derivative identity supplies the calculation of `V`. -/
lemma n_psiDot_zero (x : ℝ) (j i : Fin 1) : psiDot npsi (0 : E1) x j i = -1 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simp only [psiDot, Matrix.of_apply, (n_hasFDerivAt_npsi x j 0).fderiv]
  simp [L1, EuclideanSpace.proj]

/-- The population Jacobian of the nonlinear witness at zero is the `1 × 1` matrix `(-1)`.

This is the value of vdV's `V = Pψ̇_{θ₀}` in the example. -/
lemma n_Vmat : Vmat wP npsi (0 : E1) = Matrix.of fun _ _ : Fin 1 => (-1 : ℝ) := by
  ext j i
  simp [Vmat, n_psiDot_zero]

/-- The nonlinear witness's Jacobian entries at zero are integrable under `wP`.

The entries are constant and hence integrable. -/
lemma n_hVint (j i : Fin 1) :
    Integrable (fun x => psiDot npsi (0 : E1) x j i) wP := by
  simp only [n_psiDot_zero]
  exact integrable_const _

/-- The nonlinear witness's population Jacobian is nonsingular.

In one dimension its determinant is the unit `-1`. -/
lemma n_hV : IsUnit (Vmat wP npsi (0 : E1)).det := by
  rw [n_Vmat, Matrix.det_fin_one]
  simp

/-- The nonlinear domination envelope is measurable.

This establishes the required regularity of the envelope. -/
lemma n_hpsiDdot_meas : Measurable npsiDdot := by
  unfold npsiDdot
  fun_prop

/-- The nonlinear domination envelope is integrable under the standard Gaussian law.

Integrability follows from the finite first absolute moment of the standard Gaussian law. -/
lemma n_hpsiDdot_int : Integrable npsiDdot wP := by
  unfold npsiDdot
  exact (w_integrable_id.abs.const_mul 2).add (integrable_const (6 : ℝ))

/-! ## 4. Exact sample root -/

/-- The reused sample mean is an exact root of the nonlinear empirical estimating equation
for every sample size and every sample.

This includes `n = 0`, where `empiricalAvg` is defined to be zero because
`(0 : ℝ)⁻¹ = 0`. -/
lemma n_hroot (n : ℕ) (xs : Fin n → ℝ) (j : Fin 1) :
    empiricalAvg (npsi (wthetahat n xs) j) n xs = 0 := by
  have hfun : npsi (wthetahat n xs) j = fun x =>
      (1 + (wthetahat n xs 0) ^ 2) * wpsi (wthetahat n xs) j x := by
    funext x
    simp only [npsi, wpsi]
    ring
  rw [hfun, empiricalAvg_smul, w_hroot]
  simp

/-! ## 5. Criterion and local maximum -/

/-- The nonlinear criterion is measurable in the observation for every fixed parameter.

This verifies criterion measurability in Theorem 5.42. -/
lemma n_hm_meas (θ : E1) : Measurable (nm θ) := by
  unfold nm
  fun_prop

/-- The Fréchet derivative of the nonlinear criterion is the inner-product functional induced
by the nonlinear score.

The parameter domain is `univ`, so membership introduces no additional regularity
assumption. -/
lemma n_hgrad (θ : E1)
    -- Membership in the full parameter space.
    (_hθ : θ ∈ (Set.univ : Set E1)) (x : ℝ) :
    HasFDerivAt (fun θ' : E1 => nm θ' x) (innerSL ℝ (psiVec npsi θ x)) θ := by
  have hg : HasDerivAt (fun t : ℝ =>
      x * t + x * t ^ 3 / 3 - t ^ 2 / 2 - t ^ 4 / 4)
      ((x - θ 0) * (1 + (θ 0) ^ 2)) (θ 0) := by
    convert! ((((hasDerivAt_const (θ 0) x).mul (hasDerivAt_id (θ 0))).add
      (((hasDerivAt_const (θ 0) x).mul ((hasDerivAt_id (θ 0)).pow 3)).div_const 3)).sub
      (((hasDerivAt_id (θ 0)).pow 2).div_const 2)).sub
      (((hasDerivAt_id (θ 0)).pow 4).div_const 4) using 1
    all_goals
      simp [id_eq]
      ring
  have hnm : HasFDerivAt (fun θ' : E1 => nm θ' x)
      (((x - θ 0) * (1 + (θ 0) ^ 2)) • L1) θ := by
    simpa only [nm, Function.comp_apply, L1_apply] using!
      hg.comp_hasFDerivAt θ L1.hasFDerivAt
  refine hnm.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, L1_apply,
    innerSL_E1]
  rfl

/-- The population criterion difference is
`-((θ 0)^2)/2 - ((θ 0)^4)/4`.

This exact identity yields the centered difference used in the local-maximum premise. -/
lemma n_criterion (θ : E1) :
    ∫ x, (nm θ x - nm (0 : E1) x) ∂wP = -((θ 0) ^ 2 / 2) - (θ 0) ^ 4 / 4 := by
  have hfun : (fun x : ℝ => nm θ x - nm (0 : E1) x) = fun x : ℝ =>
      x * (θ 0 + (θ 0) ^ 3 / 3) - ((θ 0) ^ 2 / 2 + (θ 0) ^ 4 / 4) := by
    funext x
    simp only [nm, PiLp.zero_apply, mul_zero, zero_pow (by norm_num : 3 ≠ 0),
      zero_div, add_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero,
      zero_pow (by norm_num : 4 ≠ 0)]
    ring
  rw [hfun]
  have hidx : Integrable (fun x : ℝ => x) wP := w_integrable_id
  rw [integral_sub (hidx.mul_const _) (integrable_const _)]
  have hid : ∫ x : ℝ, x * (θ 0 + (θ 0) ^ 3 / 3) ∂wP = 0 := by
    rw [integral_mul_const]
    unfold wP
    simp [ProbabilityTheory.integral_id_gaussianReal]
  rw [hid, integral_const]
  simp
  ring

/-- Zero is a local maximum of the nonlinear population criterion difference.

The global inequality supplied by `n_criterion` implies vdV Theorem 5.42's
local-maximum premise. -/
lemma n_hmax :
    IsLocalMax (fun θ : E1 => ∫ x, (nm θ x - nm (0 : E1) x) ∂wP) 0 := by
  refine Eventually.of_forall fun θ => ?_
  dsimp only
  rw [n_criterion θ, n_criterion (0 : E1)]
  simp only [PiLp.zero_apply, zero_pow (by norm_num : 2 ≠ 0), zero_div, neg_zero,
    zero_pow (by norm_num : 4 ≠ 0), sub_zero]
  nlinarith [sq_nonneg (θ 0), sq_nonneg ((θ 0) ^ 2)]

/-! ## Applications of the nonlinear example -/

/-- **Asymptotic normality for the nonlinear score.**

The proof applies
`classical_zEstimator_normality_of_exact_root` to the concrete nonlinear score,
standard-normal sample, and exact sample-mean roots. In particular, the example exercises
the second-derivative domination condition with a nonzero second derivative. -/
theorem nonlinear_witness_normality :
    TendstoInProbZero (fun _ : ℕ => wmu) (fun n ξ =>
        Real.sqrt n • ((wthetahat n fun i : Fin n => wX i.val ξ) - (0 : E1))
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 1) (Vmat wP npsi 0)⁻¹
              (empiricalProcessVec wP npsi 0 n fun i : Fin n => wX i.val ξ))
    ∧ WeakConverges
        (fun n => wmu.map fun ξ =>
          Real.sqrt n • ((wthetahat n fun i : Fin n => wX i.val ξ) - (0 : E1)))
        (multivariateGaussian 0
          ((Vmat wP npsi 0)⁻¹ * psiCov wP npsi 0 * ((Vmat wP npsi 0)⁻¹)ᵀ)) := by
  exact classical_zEstimator_normality_of_exact_root wP Set.univ w_hΘ_open npsi 0 w_hθ₀
    n_hpsi_meas n_hC2 n_hPθ₀_zero n_hpsi_L2 n_hVint n_hV npsiDdot n_hpsiDdot_meas
    n_hpsiDdot_int (by norm_num : (0 : ℝ) < 1) (Set.subset_univ _) n_hdom wthetahat wmu wX
    w_hX_meas w_hX_indep w_hX_id w_hX_law w_hθhat_meas n_hroot w_hcons

/-- **Root existence and consistency for the nonlinear score.**

Both root
events carry measurable inner witnesses of probability tending to one, and the selected
root sequence is consistent. -/
theorem nonlinear_witness_root_exists_consistent :
    TendstoInnerProbOne wmu (fun n => {ξ | ∃ θ ∈ (Set.univ : Set E1), ∀ j,
        empiricalAvg (npsi θ j) n (fun i : Fin n => wX i.val ξ) = 0})
    ∧ ∃ θ_hat : ∀ n, (Fin n → ℝ) → E1,
        TendstoInnerProbOne wmu (fun n => {ξ | ∀ j,
            empiricalAvg (npsi (θ_hat n fun i : Fin n => wX i.val ξ) j) n
              (fun i : Fin n => wX i.val ξ) = 0})
        ∧ TendstoInProbZero (fun _ : ℕ => wmu)
            (fun n ξ => (θ_hat n fun i : Fin n => wX i.val ξ) - (0 : E1)) := by
  exact classical_zEstimator_root_exists_consistent wP Set.univ w_hΘ_open npsi 0 w_hθ₀
    n_hpsi_meas n_hC2 n_hPθ₀_zero n_hpsi_L2 n_hVint n_hV npsiDdot n_hpsiDdot_meas
    n_hpsiDdot_int (by norm_num : (0 : ℝ) < 1) (Set.subset_univ _) n_hdom wmu wX
    w_hX_meas w_hX_indep w_hX_id w_hX_law

/-- **Local-maximizing roots for the nonlinear criterion.**

The result states the strengthened inner-probability root and local-maximum events together
with consistency, using `nm` as a primitive of the genuinely nonlinear score. -/
theorem nonlinear_witness_localmax_roots :
    ∃ θ_hat : ∀ n, (Fin n → ℝ) → E1,
      TendstoInnerProbOne wmu (fun n => {ξ | ∀ j,
          empiricalAvg (npsi (θ_hat n fun i : Fin n => wX i.val ξ) j) n
            (fun i : Fin n => wX i.val ξ) = 0})
      ∧ TendstoInProbZero (fun _ : ℕ => wmu)
          (fun n ξ => (θ_hat n fun i : Fin n => wX i.val ξ) - (0 : E1))
      ∧ TendstoInnerProbOne wmu (fun n => {ξ |
          IsLocalMax (fun θ => empiricalAvg (nm θ) n fun i : Fin n => wX i.val ξ)
            (θ_hat n fun i : Fin n => wX i.val ξ)}) := by
  exact classical_zEstimator_localmax_roots wP Set.univ w_hΘ_open npsi 0 w_hθ₀ n_hpsi_meas
    n_hC2 n_hPθ₀_zero n_hpsi_L2 n_hVint n_hV npsiDdot n_hpsiDdot_meas n_hpsiDdot_int
    (by norm_num : (0 : ℝ) < 1) (Set.subset_univ _) n_hdom wmu wX w_hX_meas w_hX_indep
    w_hX_id w_hX_law nm n_hm_meas n_hgrad n_hmax

end AsymptoticStatistics.ClassicalZEstimator.NonlinearWitness
