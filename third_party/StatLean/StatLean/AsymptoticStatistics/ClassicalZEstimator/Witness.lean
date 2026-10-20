module
public import StatLean.AsymptoticStatistics.ClassicalZEstimator.AsymptoticNormality
public import StatLean.AsymptoticStatistics.ClassicalZEstimator.RootExistence
public import StatLean.AsymptoticStatistics.ClassicalZEstimator.GradientLocalMax
public import StatLean.AsymptoticStatistics.ForMathlib.IidWLLN
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

/-!
# A normal-location example for classical Z-estimators (vdV 5.41 / 5.42)

This file verifies the assumptions of three classical Z-estimator results in a concrete
one-dimensional normal-location model:

* `classical_zEstimator_normality` (vdV Theorem 5.41, book p.68),
* `classical_zEstimator_root_exists_consistent` (vdV Theorem 5.42 (i)+(ii), p.68-69),
* `classical_zEstimator_localmax_roots` (vdV Theorem 5.42 final assertion, p.69).

The example simultaneously satisfies the smoothness, second-order domination,
`Pψ_{θ₀} = 0`, nonsingularity, i.i.d., consistency, and local-maximum assumptions.

## The one-dimensional normal location model

`k = 1`, `Ω = ℝ`, `P = N(0,1)`, `Θ = univ`, `θ₀ = 0`, and

* `ψ_θ(x) = x − θ₀'`   (the location score; `θ₀'` is the single coordinate `θ 0`),
* `m_θ(x) = −(x − θ 0)²/2`   (the log-likelihood up to an additive constant, `∇_θ m = ψ`),
* `ψ̈ ≡ 0`   (`ψ` is affine in `θ`, so all second derivatives vanish identically),
* sample space `Ξ = (ℕ → ℝ)` with `μ = ⨂ N(0,1)` and `X i ω = ω i` (coordinate maps),
* `θ̂ₙ = X̄ₙ` (the sample mean), which is an *exact* root of `ℙₙψ_θ = 0` and is consistent
  by the weak law (`iid_lln_in_prob_seq`).

The bookkeeping then reads `V = Pψ̇_{θ₀} = (−1)`, `det V = −1` (a unit), `Pψ_{θ₀} = 0`,
`P‖ψ_{θ₀}‖² = 1 < ∞`, and `θ ↦ P(m_θ − m_{θ₀}) = −(θ 0)²/2` has a (global, hence local)
maximum at `θ₀ = 0`. All of this is machine-checked below.

-/

open MeasureTheory Filter Topology ProbabilityTheory
open AsymptoticStatistics AsymptoticStatistics.EmpiricalProcess
open scoped Matrix

namespace AsymptoticStatistics.ClassicalZEstimator.Witness

/-! ## 1. The model -/

/-- The parameter space of the example: `ℝ` represented as `EuclideanSpace ℝ (Fin 1)`. -/
abbrev E1 := EuclideanSpace ℝ (Fin 1)

/-- The witness law `P = N(0,1)` on `Ω = ℝ`. -/
noncomputable def wP : Measure ℝ := ProbabilityTheory.gaussianReal 0 1

instance : IsProbabilityMeasure wP := by unfold wP; infer_instance

/-- The witness estimating function `ψ_θ(x) = x − θ 0`: the score of the normal location
family. There is a single estimating equation (`j : Fin 1` is ignored). -/
noncomputable def wpsi : E1 → Fin 1 → ℝ → ℝ := fun θ _ x => x - θ 0

/-- The witness criterion function `m_θ(x) = −(x − θ 0)²/2`, i.e. the `N(θ,1)`
log-likelihood up to an additive constant. Its gradient in `θ` is `wpsi`. -/
noncomputable def wm : E1 → ℝ → ℝ := fun θ x => -((x - θ 0) ^ 2 / 2)

/-- The coordinate functional `θ ↦ θ 0` as a continuous linear map. Having it as a bundled
CLM is what makes the derivative computations below one-liners. -/
noncomputable def L1 : E1 →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 1)

@[simp] lemma L1_apply (θ : E1) : L1 θ = θ 0 := rfl

/-- The Euclidean norm on `EuclideanSpace ℝ (Fin 1)` is the absolute value of the single
coordinate. -/
lemma norm_E1 (v : E1) : ‖v‖ = |v 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

/-- The real inner product on `EuclideanSpace ℝ (Fin 1)` is the product of coordinates. -/
lemma innerSL_E1 (a v : E1) : (innerSL ℝ a) v = a 0 * v 0 := by
  simp only [innerSL_apply_apply, PiLp.inner_apply, Fin.sum_univ_one]
  exact mul_comm _ _

/-- The single coordinate of the bundled witness score vector. -/
@[simp] lemma psiVec_witness_apply (θ : E1) (x : ℝ) (j : Fin 1) :
    psiVec wpsi θ x j = x - θ 0 := rfl

/-! ## 2. Derivatives of the witness `ψ` -/

/-- `θ ↦ ψ_θ(x)` is affine with (constant) Fréchet derivative `−L1`. -/
lemma hasFDerivAt_wpsi (x : ℝ) (j : Fin 1) (θ : E1) :
    HasFDerivAt (fun θ' : E1 => wpsi θ' j x) (-L1) θ := by
  have h : HasFDerivAt (fun θ' : E1 => x - L1 θ') (0 - L1) θ :=
    (hasFDerivAt_const x θ).sub L1.hasFDerivAt
  simpa [wpsi] using h

lemma fderiv_wpsi (x : ℝ) (j : Fin 1) :
    (fderiv ℝ fun θ' : E1 => wpsi θ' j x) = fun _ => -L1 :=
  funext fun θ => (hasFDerivAt_wpsi x j θ).fderiv

/-- **`ψ̇_θ(x) = (−1)`.** The `1 × 1` Jacobian of the witness estimating function is the
constant matrix `−1`, at every `θ` and every `x`. -/
lemma psiDot_witness (θ : E1) (x : ℝ) (j i : Fin 1) : psiDot wpsi θ x j i = -1 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simp only [psiDot, Matrix.of_apply, (hasFDerivAt_wpsi x j θ).fderiv]
  simp [L1, EuclideanSpace.proj]

/-- **`V = Pψ̇_{θ₀} = (−1)`.** -/
lemma Vmat_witness : Vmat wP wpsi (0 : E1) = Matrix.of fun _ _ : Fin 1 => (-1 : ℝ) := by
  ext j i
  simp [Vmat, psiDot_witness]

/-! ## 3. The setup hypotheses of vdV 5.41 / 5.42, discharged -/

lemma w_hΘ_open : IsOpen (Set.univ : Set E1) := isOpen_univ

lemma w_hθ₀ : (0 : E1) ∈ (Set.univ : Set E1) := Set.mem_univ _

lemma w_hψ_meas : ∀ (θ : E1) (j : Fin 1), Measurable (wpsi θ j) :=
  fun _ _ => measurable_id.sub measurable_const

/-- **`hC2`: `θ ↦ ψ_θ(x)` is `C²`** (indeed `C^∞`; it is affine). -/
lemma w_hC2 (j : Fin 1) (x : ℝ) :
    ContDiffOn ℝ 2 (fun θ : E1 => wpsi θ j x) (Set.univ : Set E1) := by
  have h : ContDiff ℝ 2 (fun θ : E1 => wpsi θ j x) := by
    simpa [wpsi] using (contDiff_const (c := x) (n := (2 : ℕ)) (E := E1)).sub L1.contDiff
  exact h.contDiffOn

/-- **`hPθ₀_zero`: `Pψ_{θ₀} = ∫ x dN(0,1) = 0`.** -/
lemma w_hPθ₀_zero (j : Fin 1) : ∫ x, wpsi (0 : E1) j x ∂wP = 0 := by
  simp only [wpsi]
  have : ((0 : E1) 0) = 0 := by simp
  simp only [this, sub_zero]
  unfold wP
  simp [ProbabilityTheory.integral_id_gaussianReal]

lemma w_memLp_id : MemLp (id : ℝ → ℝ) 2 wP := by
  unfold wP
  exact ProbabilityTheory.memLp_id_gaussianReal' 2 (by simp)

lemma w_integrable_id : Integrable (id : ℝ → ℝ) wP := by
  have h : MemLp (id : ℝ → ℝ) 1 wP := by
    unfold wP; exact ProbabilityTheory.memLp_id_gaussianReal' 1 (by simp)
  exact h.integrable le_rfl

lemma w_psiVec_measurable : Measurable (psiVec wpsi (0 : E1)) := by
  have h : Measurable fun x : ℝ => (fun _ : Fin 1 => wpsi (0 : E1) 0 x) :=
    measurable_pi_iff.mpr fun _ => measurable_id.sub measurable_const
  exact (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable.comp h

/-- **`hψ_L2`: `P‖ψ_{θ₀}‖² = ∫ x² dN(0,1) = 1 < ∞`.** -/
lemma w_hψ_L2 : MemLp (psiVec wpsi (0 : E1)) 2 wP := by
  refine MemLp.of_le w_memLp_id w_psiVec_measurable.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_E1]
  simp [psiVec, wpsi, Real.norm_eq_abs]

/-- **`hVint`: the Jacobian entries are `P`-integrable** (they are the constant `−1`). -/
lemma w_hVint (j i : Fin 1) : Integrable (fun x => psiDot wpsi (0 : E1) x j i) wP := by
  simp only [psiDot_witness]
  exact integrable_const _

/-- **`hV`: `V = (−1)` is nonsingular**, `det V = −1`. -/
lemma w_hV : IsUnit (Vmat wP wpsi (0 : E1)).det := by
  rw [Vmat_witness, Matrix.det_fin_one]
  simp

/-- **`hdom`: the second derivatives vanish identically**, so `ψ̈ ≡ 0` dominates them.
`θ ↦ ψ_θ(x)` is affine, hence `fderiv` is constant and the second iterated derivative is
`0` at every point. -/
lemma w_hdom (θ : E1) (_hθ : θ ∈ Metric.closedBall (0 : E1) 1) (j : Fin 1) (x : ℝ) :
    ‖iteratedFDeriv ℝ 2 (fun θ' : E1 => wpsi θ' j x) θ‖ ≤ (fun _ : ℝ => (0 : ℝ)) x := by
  rw [← norm_iteratedFDeriv_fderiv, fderiv_wpsi x j,
    iteratedFDeriv_const_of_ne (by norm_num)]
  simp

/-! ## 4. The i.i.d. encoding -/

/-- The canonical i.i.d. sample space: `ℕ`-indexed sequences of reals carrying the infinite
product of `N(0,1)`. -/
noncomputable def wmu : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => wP

instance : IsProbabilityMeasure wmu := by unfold wmu; infer_instance

/-- The observations: the coordinate projections. -/
def wX : ℕ → (ℕ → ℝ) → ℝ := fun i ω => ω i

lemma w_hX_meas (i : ℕ) : Measurable (wX i) := measurable_pi_apply i

lemma w_hX_indep : ProbabilityTheory.iIndepFun wX wmu := by
  have h := ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : ℕ => wP) (X := fun _ : ℕ => (id : ℝ → ℝ)) fun _ => measurable_id
  simpa [wX, wmu] using! h

lemma w_hX_law' (i : ℕ) : wmu.map (wX i) = wP :=
  Measure.infinitePi_map_eval (fun _ : ℕ => wP) i

lemma w_hX_law : wmu.map (wX 0) = wP := w_hX_law' 0

lemma w_hX_id (i : ℕ) : ProbabilityTheory.IdentDistrib (wX i) (wX 0) wmu wmu :=
  ⟨(w_hX_meas i).aemeasurable, (w_hX_meas 0).aemeasurable, by
    rw [w_hX_law' i, w_hX_law' 0]⟩

/-! ## 5. The estimator: the sample mean is an exact root, and is consistent -/

/-- The witness estimator `θ̂ₙ = X̄ₙ`, packaged into `EuclideanSpace ℝ (Fin 1)`. -/
noncomputable def wthetahat : ∀ n, (Fin n → ℝ) → E1 :=
  fun n xs => (WithLp.equiv 2 (Fin 1 → ℝ)).symm fun _ => empiricalAvg id n xs

@[simp] lemma wthetahat_apply (n : ℕ) (xs : Fin n → ℝ) :
    wthetahat n xs 0 = empiricalAvg id n xs := rfl

/-- **`hroot`: the sample mean is an *exact* root of `ℙₙψ_θ = 0`** for every `n` and every
sample (`ℙₙ(x − θ) = 0 ⟺ θ = x̄`). For `n = 0` both sides are `0` by Lean's `(0:ℝ)⁻¹ = 0`
convention. -/
lemma w_hroot (n : ℕ) (xs : Fin n → ℝ) (j : Fin 1) :
    empiricalAvg (wpsi (wthetahat n xs) j) n xs = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [empiricalAvg]
  · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp only [empiricalAvg, wpsi, wthetahat_apply, id_eq, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

lemma w_hθhat_meas (n : ℕ) :
    Measurable fun ξ : ℕ → ℝ => wthetahat n fun i : Fin n => wX i.val ξ := by
  have hr : Measurable fun ξ : ℕ → ℝ => empiricalAvg id n fun i : Fin n => wX i.val ξ := by
    simp only [empiricalAvg, id_eq]
    exact measurable_const.mul
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply (i : ℕ))
  exact (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable.comp
    (measurable_pi_iff.mpr fun _ => hr)

/-- **`hcons`: the sample mean is consistent**, by the weak law of large numbers
(`iid_lln_in_prob_seq`) together with `∫ x dN(0,1) = 0`. -/
lemma w_hcons :
    TendstoInProbZero (fun _ : ℕ => wmu)
      fun n ξ => (wthetahat n fun i : Fin n => wX i.val ξ) - (0 : E1) := by
  have hlln := iid_lln_in_prob_seq wP id measurable_id w_integrable_id wmu wX w_hX_meas
    w_hX_indep w_hX_id w_hX_law
  have hint : ∫ x, (id : ℝ → ℝ) x ∂wP = 0 := by
    unfold wP; simp [ProbabilityTheory.integral_id_gaussianReal]
  rw [hint] at hlln
  intro ε hε
  have hset : ∀ n : ℕ,
      {ξ : ℕ → ℝ | ε ≤ ‖(wthetahat n fun i : Fin n => wX i.val ξ) - (0 : E1)‖}
        = {ξ : ℕ → ℝ | ε ≤ ‖(empiricalAvg id n fun i : Fin n => wX i.val ξ) - 0‖} := by
    intro n
    ext ξ
    simp only [Set.mem_setOf_eq, sub_zero, norm_E1, wthetahat_apply, Real.norm_eq_abs]
  simp only [hset]
  exact hlln ε hε

/-! ## 6. The gradient / local-max structure of vdV 5.42's final assertion -/

lemma w_hm_meas (θ : E1) : Measurable (wm θ) := by
  unfold wm
  fun_prop

/-- **`hgrad`: `ψ_θ = ∇_θ m_θ`.** -/
lemma w_hgrad (θ : E1) (_hθ : θ ∈ (Set.univ : Set E1)) (x : ℝ) :
    HasFDerivAt (fun θ' : E1 => wm θ' x) (innerSL ℝ (psiVec wpsi θ x)) θ := by
  have hu : HasFDerivAt (fun θ' : E1 => x - L1 θ') (-L1) θ := by
    simpa using! (hasFDerivAt_const x θ).sub L1.hasFDerivAt
  have hfun : (fun θ' : E1 => wm θ' x)
      = (-(1 : ℝ) / 2) • fun θ' : E1 => (x - L1 θ') * (x - L1 θ') := by
    funext θ'; simp only [wm, L1_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hfun]
  have h1 : HasFDerivAt (fun θ' : E1 => (x - L1 θ') * (x - L1 θ'))
      ((x - L1 θ) • (-L1) + (x - L1 θ) • (-L1)) θ := hu.mul hu
  refine (h1.const_smul (-(1 : ℝ) / 2)).congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, smul_eq_mul,
    innerSL_E1, psiVec_witness_apply, L1_apply]
  ring

/-- **`hmax`: `θ ↦ P(m_θ − m_{θ₀}) = −(θ 0)²/2`**, which has a global (hence local) maximum
at `θ₀ = 0`. -/
lemma w_criterion (θ : E1) : ∫ x, (wm θ x - wm (0 : E1) x) ∂wP = -((θ 0) ^ 2 / 2) := by
  have h0 : ((0 : E1) 0) = 0 := by simp
  have hfun : (fun x : ℝ => wm θ x - wm (0 : E1) x)
      = fun x : ℝ => x * (θ 0) - (θ 0) ^ 2 / 2 := by
    funext x; simp only [wm, h0, sub_zero]; ring
  rw [hfun]
  have hidx : Integrable (fun x : ℝ => x) wP := w_integrable_id
  rw [integral_sub (hidx.mul_const _) (integrable_const _)]
  have hid : ∫ x : ℝ, x * (θ 0) ∂wP = 0 := by
    rw [integral_mul_const]
    unfold wP
    simp [ProbabilityTheory.integral_id_gaussianReal]
  rw [hid, integral_const]
  simp

lemma w_hmax : IsLocalMax (fun θ : E1 => ∫ x, (wm θ x - wm (0 : E1) x) ∂wP) 0 := by
  refine Eventually.of_forall fun θ => ?_
  dsimp only
  rw [w_criterion θ, w_criterion (0 : E1)]
  have h0 : ((0 : E1) 0) = 0 := by simp
  rw [h0]
  nlinarith [sq_nonneg (θ 0)]

/-! ## 7. Applications of the general theorems

Each of the following applies a general classical Z-estimator theorem to the normal-location
example.
-/

/-- **Normal-location instance of vdV Theorem 5.41** (`classical_zEstimator_normality`).

The assumptions are satisfied by the one-dimensional normal-location model with the sample
mean as estimator, and the conclusion therefore
holds for it: `√n·X̄ₙ` admits vdV's linear representation and converges weakly to the
Gaussian limit with covariance `V⁻¹ P[ψψᵀ] V⁻ᵀ`. -/
theorem classical_zEstimator_hypotheses_satisfiable :
    TendstoInProbZero (fun _ : ℕ => wmu) (fun n ξ =>
        Real.sqrt n • ((wthetahat n fun i : Fin n => wX i.val ξ) - (0 : E1))
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 1) (Vmat wP wpsi 0)⁻¹
              (empiricalProcessVec wP wpsi 0 n fun i : Fin n => wX i.val ξ))
    ∧ WeakConverges
        (fun n => wmu.map fun ξ =>
          Real.sqrt n • ((wthetahat n fun i : Fin n => wX i.val ξ) - (0 : E1)))
        (multivariateGaussian 0
          ((Vmat wP wpsi 0)⁻¹ * psiCov wP wpsi 0 * ((Vmat wP wpsi 0)⁻¹)ᵀ)) :=
  classical_zEstimator_normality_of_exact_root wP Set.univ w_hΘ_open wpsi 0 w_hθ₀ w_hψ_meas w_hC2
    w_hPθ₀_zero w_hψ_L2 w_hVint w_hV (fun _ => 0) measurable_const (integrable_const _)
    (by norm_num : (0:ℝ) < 1) (Set.subset_univ _) w_hdom wthetahat wmu wX w_hX_meas
    w_hX_indep w_hX_id w_hX_law w_hθhat_meas w_hroot w_hcons

/-- **Normal-location root existence and consistency for vdV Theorem 5.42 (i)+(ii)**
(`classical_zEstimator_root_exists_consistent`). -/
theorem classical_zEstimator_root_hypotheses_satisfiable :
    Filter.Tendsto (fun n => wmu.real {ξ | ∃ θ ∈ (Set.univ : Set E1), ∀ j,
        empiricalAvg (wpsi θ j) n (fun i : Fin n => wX i.val ξ) = 0}) Filter.atTop (𝓝 1)
    ∧ ∃ θ_hat : ∀ n, (Fin n → ℝ) → E1,
        Filter.Tendsto (fun n => wmu.real {ξ | ∀ j,
            empiricalAvg (wpsi (θ_hat n fun i : Fin n => wX i.val ξ) j) n
              (fun i : Fin n => wX i.val ξ) = 0}) Filter.atTop (𝓝 1)
        ∧ TendstoInProbZero (fun _ : ℕ => wmu)
            (fun n ξ => (θ_hat n fun i : Fin n => wX i.val ξ) - (0 : E1)) :=
  classical_zEstimator_root_exists_consistent_outer wP Set.univ w_hΘ_open wpsi 0 w_hθ₀ w_hψ_meas
    w_hC2 w_hPθ₀_zero w_hψ_L2 w_hVint w_hV (fun _ => 0) measurable_const (integrable_const _)
    (by norm_num : (0:ℝ) < 1) (Set.subset_univ _) w_hdom wmu wX w_hX_meas w_hX_indep
    w_hX_id w_hX_law

/-- **Normal-location local-maximizing roots for vdV Theorem 5.42, final assertion**
(`classical_zEstimator_localmax_roots`). -/
theorem classical_zEstimator_localmax_hypotheses_satisfiable :
    ∃ θ_hat : ∀ n, (Fin n → ℝ) → E1,
      Filter.Tendsto (fun n => wmu.real {ξ | ∀ j,
          empiricalAvg (wpsi (θ_hat n fun i : Fin n => wX i.val ξ) j) n
            (fun i : Fin n => wX i.val ξ) = 0}) Filter.atTop (𝓝 1)
      ∧ TendstoInProbZero (fun _ : ℕ => wmu)
          (fun n ξ => (θ_hat n fun i : Fin n => wX i.val ξ) - (0 : E1))
      ∧ Filter.Tendsto (fun n => wmu.real {ξ |
          IsLocalMax (fun θ => empiricalAvg (wm θ) n fun i : Fin n => wX i.val ξ)
            (θ_hat n fun i : Fin n => wX i.val ξ)}) Filter.atTop (𝓝 1) :=
  classical_zEstimator_localmax_roots_outer wP Set.univ w_hΘ_open wpsi 0 w_hθ₀ w_hψ_meas w_hC2
    w_hPθ₀_zero w_hψ_L2 w_hVint w_hV (fun _ => 0) measurable_const (integrable_const _)
    (by norm_num : (0:ℝ) < 1) (Set.subset_univ _) w_hdom wmu wX w_hX_meas w_hX_indep
    w_hX_id w_hX_law wm w_hm_meas w_hgrad w_hmax

end AsymptoticStatistics.ClassicalZEstimator.Witness
