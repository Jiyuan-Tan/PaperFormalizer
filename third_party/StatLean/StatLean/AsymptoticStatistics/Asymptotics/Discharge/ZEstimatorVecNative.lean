module
public import StatLean.AsymptoticStatistics.Core.EfficiencyOperationalVec
public import StatLean.AsymptoticStatistics.ForMathlib.IidWLLN
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScoreVec
public import StatLean.AsymptoticStatistics.ParametricFamily.BartlettIdentity
public import StatLean.AsymptoticStatistics.Operators.InformationLoss
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# Multivariate Taylor expansion for Z-estimators

This smooth conditional theorem takes a vector estimating equation, a matrix
Bartlett identity, and a matrix Taylor remainder. It derives
`sqrt n * I * (thetaHat - theta0) = G_n score + o_P(1)` and applies the inverse
of the full information matrix. Thus it supports non-diagonal information and
has influence `I^-1 score = candidateVecEIF`.

The matrix Taylor and Bartlett assumptions are stronger than the proper-submodel
hypotheses of van der Vaart, Theorem 25.77. References: van der Vaart, §25.5,
Theorem 25.54 (vector form), and §25.4, Lemma 25.25.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVecNative

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec

variable {Ω : Type} [MeasurableSpace Ω]
variable {d : ℕ}

/-! ### Evaluation of a matrix of `L²` derivatives -/

/-- Sample-point action of the `d × d` matrix of `L²(P)`-derivatives
`M = ∂_θ ℓ̃` on a Euclidean vector `v`: the vector whose `j`-th coordinate is
`∑ₖ (M j k)(x) · vₖ`, i.e. `(∂_θ ℓ̃)(x) · v`.

This is the matrix generalization of the scalar product `ℓ̇(x) · (θ̂ − θ₀)`
appearing in the scalar DQM-Taylor remainder (`score_l2_taylor` in
`Discharge/ZEstimator.lean`). -/
noncomputable def scoreDerivApply
    {P : Measure Ω} [IsProbabilityMeasure P]
    (M : Matrix (Fin d) (Fin d) (Lp ℝ 2 P)) (x : Ω)
    (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm
    (fun j => ∑ k, ((M j k : Ω → ℝ) x) * v k)

/-! ### Strong regularity hypotheses -/

/-- Native vector strong-regularity bundle for a generic Taylor/Z-estimator
route. It carries the vector and matrix inputs used by the full `d x d`
identity:

* `hPD` — positive-definiteness of the efficient information matrix `Ĩ`;
* `score_eq_vec` — the vector estimating equation
  `√n · 𝕡_n ℓ̃_{θ̂_n} = o_P` in `EuclideanSpace ℝ (Fin d)`;
* `matrix_bartlett` — the matrix Bartlett identity `E_P[∂_θℓ̃] = −Ĩ` (entrywise);
* `matrix_taylor` — the matrix DQM-Taylor remainder (vector lift of the scalar
  `score_l2_taylor`).

The score-derivative matrix
`score_l_dot : Matrix (Fin d) (Fin d) (Lp Real 2 P)` has
`(j, k)` entry `∂_{θ_k} ℓ̃_j`.

Reference for the Taylor pattern: vdV §25.5 thm:25.54 (vector form); §25.4
lem:25.25 supplies the efficient-influence construction. These conditions differ
from the approximately-least-favorable MLE hypotheses of Theorem 25.77. -/
structure ZEstimatorTaylorCoreNative_vec
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (e : Fin d → Θ)
    (estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (score_func_seq : ∀ n, (Fin n → Ω) → (Ω → EuclideanSpace ℝ (Fin d)))
    (score_l_dot : Matrix (Fin d) (Fin d) (Lp ℝ 2 P))
    (θ₀ : EuclideanSpace ℝ (Fin d)) : Prop where
  /-- The efficient information matrix is positive-definite, so its full
  inverse is defined. Reference: vdV §25.4, Lemma 25.25. -/
  hPD : (efficientInformationMatrix S_θ T_nuis e).PosDef
  /-- Generic Taylor-core input, patterned on vdV §25.5 thm:25.54 hyp 4: the
  supplied vector estimator solves the estimating equation up to `o_P(n^{-1/2})`:
  `√n · 𝕡_n ℓ̃_{θ̂_n(X)} = o_P(1)` under `Pⁿ`, i.e. for every `ε > 0` the
  `Pⁿ`-probability that the Euclidean norm of
  `(√n)⁻¹ · Σᵢ ℓ̃_{θ̂_n(X)}(Xᵢ)` exceeds `ε` tends to `0`. Vector lift of the
  scalar `ZEstimatorTaylorCore.score_eq`. -/
  score_eq_vec : ∀ ε > 0, Tendsto
    (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        ε ≤ ‖(Real.sqrt n)⁻¹ • (∑ i, score_func_seq n X (X i))‖})
    atTop (𝓝 0)
  /-- Generic Taylor-core input (vdV §25.4 matrix Bartlett identity): the expectation of the
  `θ`-derivative of the efficient score is `−Ĩ`, entrywise
  `E_P[∂_{θ_k} ℓ̃_j] = −Ĩ_{jk}`. It is deliberately a supplied field here;
  separate infrastructure can derive it from suitable submodels, but this
  generic bundle does not perform that derivation and does not encode 25.77. -/
  matrix_bartlett : ∀ j k,
    ∫ ω, ((score_l_dot j k : Ω → ℝ)) ω ∂P
      = - efficientInformationMatrix S_θ T_nuis e j k
  /-- Constitutive (vdV §7.2 Thm 7.2 + Lem 7.6, matrix DQM-in-`θ` Taylor
  identity): the empirical `L²` Taylor remainder of the vector efficient score
  vanishes faster than `1/n` under `Pⁿ`:
  `Σᵢ ‖ℓ̃_{θ̂_n}(Xᵢ) − ℓ̃(Xᵢ) − (∂_θ ℓ̃)(Xᵢ)·(θ̂_n − θ₀)‖²  = o_P(1)`.
  Vector/matrix lift of the scalar `score_l2_taylor`. -/
  matrix_taylor : ∀ ε > 0, Tendsto
    (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        ε ≤ ∑ i, ‖score_func_seq n X (X i)
              - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
              - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀)‖ ^ 2})
    atTop (𝓝 0)

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
variable {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
variable [T_nuis.HasOrthogonalProjection] {e : Fin d → Θ}
variable {estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
variable {score_func_seq : ∀ n, (Fin n → Ω) → (Ω → EuclideanSpace ℝ (Fin d))}
variable {score_l_dot : Matrix (Fin d) (Fin d) (Lp ℝ 2 P)}
variable {θ₀ : EuclideanSpace ℝ (Fin d)}

/-! ### `Lp.coeFn` / finite-sum a.e. helper -/

omit [IsProbabilityMeasure P] in
/-- `Lp.coeFn` commutes with finite `Finset.sum`, `a.e.` Mathlib provides
`Lp.coeFn_add` / `Lp.coeFn_zero` for the measure-`Lp` but no finite-sum version
(the `lp`-space `coeFn_sum` is the sequence-space analogue); this is the
`Finset.induction` lift. Mirrors
`ForMathlib.Probability.IsonormalProcess.coeFn_lp_finset_sum`. -/
private lemma Lp_coeFn_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Lp ℝ 2 P) :
    (⇑(∑ k ∈ s, f k) : Ω → ℝ) =ᵐ[P] fun x => ∑ k ∈ s, (f k : Ω → ℝ) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P)] with x hx
    simp only [Finset.sum_empty]
    rw [hx]; rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ k ∈ s, f k), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

/-! ### Euclidean and matrix norm lemmas -/

/-- A single coordinate of a Euclidean vector is bounded by its norm.
(Local re-derivation of the private `ZEstimatorVec.abs_coord_le_norm`.) -/
private lemma coord_abs_le_norm (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    |x j| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (abs_nonneg (x.ofLp j))]
  apply Real.sqrt_le_sqrt
  rw [sq_abs]
  exact (Finset.single_le_sum (f := fun i => ‖x.ofLp i‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ j)).trans_eq'
    (by rw [Real.norm_eq_abs, sq_abs])

/-- **Frobenius operator bound.** For a `d × d` real matrix `A`, the Euclidean
operator action `Matrix.toEuclideanCLM A` is bounded by the Frobenius norm:
`‖toEuclideanCLM A v‖ ≤ √(∑_{j,k} A_{jk}²) · ‖v‖`. Proved by per-row
Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`). -/
private lemma norm_toEuclideanCLM_apply_le
    (A : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A v‖
      ≤ Real.sqrt (∑ j, ∑ k, (A j k) ^ 2) * ‖v‖ := by
  have hcoord : ∀ j,
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A v).ofLp j
        = ∑ k, A j k * v.ofLp k := by
    intro j
    rw [Matrix.ofLp_toEuclideanCLM]
    simp only [Matrix.mulVec, dotProduct]
  have hnv : ‖v‖ ^ 2 = ∑ k, (v.ofLp k) ^ 2 := by
    rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
    exact Finset.sum_congr rfl (fun k _ => by rw [Real.norm_eq_abs, sq_abs])
  have hnum : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A v‖ ^ 2
      = ∑ j, (∑ k, A j k * v.ofLp k) ^ 2 := by
    rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
    exact Finset.sum_congr rfl
      (fun j _ => by rw [hcoord j, Real.norm_eq_abs, sq_abs])
  have hQnn : (0 : ℝ) ≤ ∑ j, ∑ k, (A j k) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hsq : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A v‖ ^ 2
      ≤ (∑ j, ∑ k, (A j k) ^ 2) * ‖v‖ ^ 2 := by
    rw [hnum, hnv]
    calc ∑ j, (∑ k, A j k * v.ofLp k) ^ 2
        ≤ ∑ j, (∑ k, (A j k) ^ 2) * (∑ k, (v.ofLp k) ^ 2) :=
          Finset.sum_le_sum (fun j _ =>
            Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
      _ = (∑ j, ∑ k, (A j k) ^ 2) * (∑ k, (v.ofLp k) ^ 2) := by
          rw [← Finset.sum_mul]
  have hTnn : (0 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A v‖ :=
    norm_nonneg _
  have hle : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A v‖
      ≤ Real.sqrt ((∑ j, ∑ k, (A j k) ^ 2) * ‖v‖ ^ 2) := by
    rw [← Real.sqrt_sq hTnn]
    exact Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_mul hQnn, Real.sqrt_sq (norm_nonneg v)] at hle

/-! ### Centered i.i.d. `O_P(1)` by scalar Chebyshev -/

/-- **Generic centered i.i.d. `O_P(1)`.** For a mean-zero `L²(P)` function `g`,
the normalized partial sum `(√n)⁻¹ · Σᵢ g(Xᵢ)` is bounded in `Pⁿ`-probability,
uniformly in `n`. Chebyshev/variance bound; generic form of the scalar
`score_truth_sum_bddAbove_in_prob`. -/
private lemma centered_iid_sum_bddAbove
    (g : Ω → ℝ) (hg_mem : MemLp g 2 P) (hg_mean : ∫ ω, g ω ∂P = 0) :
    ∀ ε > 0, ∃ M : ℝ, ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          M ≤ |(Real.sqrt n)⁻¹ * (∑ i : Fin n, g (X i))|}
      ≤ ENNReal.ofReal ε := by
  intro ε hε
  set V : ℝ := ProbabilityTheory.variance g P with hV_def
  have hV_nn : 0 ≤ V := by
    change (0 : ℝ) ≤ (ProbabilityTheory.evariance g P).toReal
    exact ENNReal.toReal_nonneg
  refine ⟨Real.sqrt (V / ε + 1), fun n => ?_⟩
  set M : ℝ := Real.sqrt (V / ε + 1) with hM_def
  have hVε_nn : 0 ≤ V / ε + 1 := by positivity
  have hVε_pos : 0 < V / ε + 1 := by
    have : 0 ≤ V / ε := div_nonneg hV_nn hε.le
    linarith
  have hM_pos : 0 < M := Real.sqrt_pos.mpr hVε_pos
  have hM_sq : M ^ 2 = V / ε + 1 := Real.sq_sqrt hVε_nn
  have hVM : V / M ^ 2 ≤ ε := by
    rw [hM_sq]
    rcases eq_or_lt_of_le hV_nn with hV_zero | hV_pos
    · rw [← hV_zero, zero_div]; exact hε.le
    · have hVε_pos : 0 < V / ε := div_pos hV_pos hε
      have h1 : V / ε + 1 ≥ V / ε := by linarith
      have h2 : V / (V / ε + 1) ≤ V / (V / ε) :=
        div_le_div_of_nonneg_left hV_pos.le hVε_pos h1
      have h3 : V / (V / ε) = ε := by field_simp
      linarith
  by_cases hn0 : n = 0
  · subst hn0
    have h_set_empty : {X : Fin 0 → Ω |
        M ≤ |(Real.sqrt (0 : ℕ))⁻¹ * (∑ i : Fin 0, g (X i))|} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le,
        Nat.cast_zero, Real.sqrt_zero, inv_zero, mul_zero, abs_zero, Fin.sum_univ_zero]
      exact hM_pos
    rw [h_set_empty, measure_empty]; exact bot_le
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have h_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR_pos
  have h_truth_mp : ∀ i : Fin n,
      MemLp (fun X : Fin n → Ω => g (X i)) 2 (Measure.pi (fun _ : Fin n => P)) := by
    intro i
    exact hg_mem.comp_measurePreserving
      (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => P) i)
  have h_sum_mLp :
      MemLp (fun X : Fin n → Ω => ∑ i : Fin n, g (X i)) 2
        (Measure.pi (fun _ : Fin n => P)) :=
    memLp_finset_sum (Finset.univ : Finset (Fin n)) (fun i _ => h_truth_mp i)
  have h_Z_mLp :
      MemLp (fun X : Fin n → Ω =>
        (Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i)) 2
        (Measure.pi (fun _ : Fin n => P)) :=
    h_sum_mLp.const_mul _
  have h_aesm : AEStronglyMeasurable g P := hg_mem.aestronglyMeasurable
  have h_int_truth_pi : ∀ i : Fin n,
      ∫ X : Fin n → Ω, g (X i) ∂(Measure.pi (fun _ : Fin n => P)) = 0 := by
    intro i
    rw [MeasureTheory.integral_comp_eval (i := i) (μ := fun _ : Fin n => P) h_aesm,
      hg_mean]
  have h_Z_mean :
      ∫ X : Fin n → Ω, ((Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i))
        ∂(Measure.pi (fun _ : Fin n => P)) = 0 := by
    have h_int_sum :
        ∫ X : Fin n → Ω, (∑ i : Fin n, g (X i))
          ∂(Measure.pi (fun _ : Fin n => P)) = 0 := by
      rw [MeasureTheory.integral_finset_sum (Finset.univ : Finset (Fin n))
            (fun i _ => (h_truth_mp i).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2))]
      exact Finset.sum_eq_zero (fun i _ => h_int_truth_pi i)
    rw [MeasureTheory.integral_const_mul, h_int_sum, mul_zero]
  have h_Z_var :
      ProbabilityTheory.variance (fun X : Fin n → Ω =>
        (Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i))
        (Measure.pi (fun _ : Fin n => P)) = V := by
    rw [ProbabilityTheory.variance_const_mul]
    have h_var_sum :
        ProbabilityTheory.variance
          (fun X : Fin n → Ω => ∑ i : Fin n, g (X i))
          (Measure.pi (fun _ : Fin n => P))
        = ∑ _ : Fin n, V := by
      have h_pi := ProbabilityTheory.variance_sum_pi
        (μ := fun _ : Fin n => P) (X := fun _ : Fin n => g) (fun _ => hg_mem)
      have h_fun_eq :
          (∑ i : Fin n, fun ω : Fin n → Ω => g (ω i))
            = fun X : Fin n → Ω => ∑ i : Fin n, g (X i) := by
        funext X; simp [Finset.sum_apply]
      rw [h_fun_eq] at h_pi
      exact h_pi
    rw [h_var_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h_sqrt_sq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
      Real.mul_self_sqrt hnR_pos.le
    have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
    have h_inv_sq : (Real.sqrt n)⁻¹ ^ 2 = (n : ℝ)⁻¹ := by
      rw [inv_pow, sq, h_sqrt_sq]
    rw [h_inv_sq]; field_simp
  have hM_ne : M ≠ 0 := ne_of_gt hM_pos
  have h_cheb := ProbabilityTheory.meas_ge_le_variance_div_sq h_Z_mLp hM_pos
  rw [h_Z_mean, h_Z_var] at h_cheb
  have h_set_eq :
      {X : Fin n → Ω |
          M ≤ |((Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i)) - 0|}
        = {X : Fin n → Ω |
          M ≤ |(Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i)|} := by
    ext X; simp
  rw [h_set_eq] at h_cheb
  exact h_cheb.trans (ENNReal.ofReal_le_ofReal hVM)

/-- If every coordinate is strictly below `ε / √d`, the Euclidean norm is
strictly below `ε` (needs `d > 0` and `ε > 0`). Local re-derivation of the
private `ZEstimatorVec.norm_lt_of_forall_coord_lt`. -/
private lemma norm_lt_of_forall_coord_lt (x : EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (hd : 0 < d) (hε : 0 < ε) (hcov : ∀ j, |x j| < ε / Real.sqrt d) : ‖x‖ < ε := by
  rw [EuclideanSpace.norm_eq]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [show ε = Real.sqrt (ε ^ 2) by rw [Real.sqrt_sq hε.le]]
  apply Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => by positivity))
  calc ∑ i, ‖x.ofLp i‖ ^ 2 < ∑ _i : Fin d, (ε / Real.sqrt d) ^ 2 := by
        apply Finset.sum_lt_sum_of_nonempty
          (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd))
        intro i _
        rw [Real.norm_eq_abs, sq_abs]
        have hi := abs_lt.mp (hcov i)
        exact sq_lt_sq' hi.1 hi.2
    _ = ε ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          div_pow, Real.sq_sqrt hdR.le]
        field_simp

/-! ### Entrywise law of large numbers -/

/-- **Entrywise LLN + matrix Bartlett.** For each entry `(j, k)`,
`n⁻¹ · Σᵢ (∂_θ ℓ̃)_{jk}(Xᵢ) + Ĩ_{jk} →_P 0` under `Pⁿ`. Direct from the reusable
`iid_lln_in_prob_l1` on the fixed `L²(P)` entry `score_l_dot j k`, whose mean is
`−Ĩ_{jk}` by `matrix_bartlett`. Vector lift of the scalar Step 4. -/
private lemma zEstimatorVec_step4_lln
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀) (j k : Fin d) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot j k : Ω → ℝ) (X i))
                + efficientInformationMatrix S_θ T_nuis e j k|})
      atTop (𝓝 0) := by
  have hf_int : Integrable (fun ω => (score_l_dot j k : Ω → ℝ) ω) P :=
    (Lp.memLp (score_l_dot j k)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_lln := iid_lln_in_prob_l1 (fun ω => (score_l_dot j k : Ω → ℝ) ω) hf_int
  intro ε hε
  have h_bartlett := h.matrix_bartlett j k
  have h_set_eq : ∀ n : ℕ,
      {X : Fin n → Ω |
        ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot j k : Ω → ℝ) (X i))
              + efficientInformationMatrix S_θ T_nuis e j k|}
      = {X : Fin n → Ω |
          ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot j k : Ω → ℝ) (X i))
                   - ∫ ω, (score_l_dot j k : Ω → ℝ) ω ∂P|} := by
    intro n
    ext X
    simp only [Set.mem_setOf_eq]
    rw [h_bartlett]
    constructor
    · intro hh; convert hh using 2; ring
    · intro hh; convert hh using 2; ring
  simp_rw [h_set_eq]
  exact h_lln ε hε

/-! ### Vector Taylor remainder `o_P` -/

/-- **Vector Taylor remainder `o_P`.** The normalized empirical Taylor remainder
`(√n)⁻¹ · Σᵢ rem(Xᵢ) →_P 0` in `EuclideanSpace ℝ (Fin d)`, where
`rem(Xᵢ) = ℓ̃_{θ̂}(Xᵢ) − ℓ̃(Xᵢ) − (∂_θ ℓ̃)(Xᵢ)·(θ̂ − θ₀)`. Vector lift of the
scalar Step 3: Cauchy–Schwarz `‖Σᵢ rem(Xᵢ)‖² ≤ n · Σᵢ ‖rem(Xᵢ)‖²` on
`matrix_taylor`. -/
private lemma zEstimatorVec_step3_taylor
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ ‖(Real.sqrt n)⁻¹ • (∑ i : Fin n,
                (score_func_seq n X (X i)
                  - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
                  - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀)))‖})
      atTop (𝓝 0) := by
  intro ε hε
  have h_taylor := h.matrix_taylor (ε ^ 2) (by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_taylor
  · exact Filter.Eventually.of_forall (fun _ => zero_le)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    apply measure_mono
    intro X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
    set r : Fin n → EuclideanSpace ℝ (Fin d) := fun i =>
      score_func_seq n X (X i)
        - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
        - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀) with hr
    have h_cs : (∑ i, ‖r i‖) ^ 2 ≤ ↑n * (∑ i, ‖r i‖ ^ 2) := by
      have h_apply := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : Fin n => (1 : ℝ)) (fun i => ‖r i‖)
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one] at h_apply
      exact h_apply
    have h_norm_smul : ‖(Real.sqrt n)⁻¹ • (∑ i, r i)‖
        = (Real.sqrt n)⁻¹ * ‖∑ i, r i‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hε_le : ε ≤ (Real.sqrt n)⁻¹ * ‖∑ i, r i‖ := by
      rw [← h_norm_smul]; exact hX
    have h_tri : ‖∑ i, r i‖ ≤ ∑ i, ‖r i‖ := norm_sum_le _ _
    have h1 : ε ^ 2 ≤ ((Real.sqrt n)⁻¹ * ‖∑ i, r i‖) ^ 2 := by
      nlinarith [hε_le, hε.le, norm_nonneg (∑ i, r i)]
    have h2 : ((Real.sqrt n)⁻¹ * ‖∑ i, r i‖) ^ 2 = ‖∑ i, r i‖ ^ 2 / ↑n := by
      rw [mul_pow, inv_pow, Real.sq_sqrt h_n_pos.le]; ring
    have h3 : ‖∑ i, r i‖ ^ 2 ≤ (∑ i, ‖r i‖) ^ 2 := by
      nlinarith [h_tri, norm_nonneg (∑ i, r i)]
    calc ε ^ 2
        ≤ ((Real.sqrt n)⁻¹ * ‖∑ i, r i‖) ^ 2 := h1
      _ = ‖∑ i, r i‖ ^ 2 / ↑n := h2
      _ ≤ (∑ i, ‖r i‖) ^ 2 / ↑n := by
          apply div_le_div_of_nonneg_right h3 h_n_pos.le
      _ ≤ ↑n * (∑ i, ‖r i‖ ^ 2) / ↑n := by
          apply div_le_div_of_nonneg_right h_cs h_n_pos.le
      _ = ∑ i, ‖r i‖ ^ 2 := by field_simp

/-! ### Vector empirical-process `O_P(1)` for `√n·𝕡_n ℓ̃` -/

/-- **Vector `O_P(1)` for the truth empirical process.** The normalized sum
`(√n)⁻¹ · Σᵢ ℓ̃(Xᵢ)` of the (mean-zero, `L²`) vector efficient score is bounded in
`Pⁿ`-probability, uniformly in `n`. Coordinatewise scalar Chebyshev
(`centered_iid_sum_bddAbove`) assembled over the `d` coordinates by a union bound
(`norm_lt_of_forall_coord_lt`). -/
private lemma zEstimatorVec_Sn_OP1
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (e : Fin d → Θ) :
    ∀ ε > 0, ∃ M : ℝ, ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          M ≤ ‖(Real.sqrt n)⁻¹ • (∑ i : Fin n,
            tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i))‖}
      ≤ ENNReal.ofReal ε := by
  classical
  intro ε hε
  set g : Fin d → (Ω → ℝ) := fun j =>
    ((efficientScore S_θ T_nuis (e j) : ↥(L2ZeroMean P)) : Lp ℝ 2 P) with hg
  -- Coordinate identity for the normalized sum.
  have hSn_coord : ∀ (n : ℕ) (X : Fin n → Ω) (j : Fin d),
      ((Real.sqrt n)⁻¹ • (∑ i : Fin n,
          tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i))) j
        = (Real.sqrt n)⁻¹ * (∑ i : Fin n, g j (X i)) := by
    intro n X j
    change ((Real.sqrt n)⁻¹ • (∑ i : Fin n,
          tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i))).ofLp j
        = (Real.sqrt n)⁻¹ * (∑ i : Fin n, g j (X i))
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_sum,
      Finset.sum_apply]
    rfl
  by_cases hd0 : d = 0
  · refine ⟨1, fun n => ?_⟩
    have hemp : {X : Fin n → Ω | (1 : ℝ) ≤ ‖(Real.sqrt n)⁻¹ • (∑ i : Fin n,
          tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i))‖} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have hz : ‖(Real.sqrt n)⁻¹ • (∑ i : Fin n,
          tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i))‖ = 0 := by
        subst hd0; rw [EuclideanSpace.norm_eq]; simp
      rw [hz]; norm_num
    rw [hemp, measure_empty]; exact bot_le
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hdR_ne : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
    have hsqrtd_pos : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hdpos)
    -- Per-coordinate O_P(1).
    have hcov : ∀ j : Fin d, ∃ M : ℝ, ∀ n : ℕ,
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | M ≤ |(Real.sqrt n)⁻¹ * (∑ i : Fin n, g j (X i))|}
        ≤ ENNReal.ofReal (ε / d) := by
      intro j
      have hmem : MemLp (g j) 2 P := Lp.memLp _
      have hmean : ∫ ω, g j ω ∂P = 0 :=
        (AsymptoticStatistics.Operators.InformationLoss.mem_L2ZeroMean_iff P
          ((efficientScore S_θ T_nuis (e j) : ↥(L2ZeroMean P)) : Lp ℝ 2 P)).mp
          (efficientScore S_θ T_nuis (e j)).2
      exact centered_iid_sum_bddAbove (g j) hmem hmean (ε / d) (by positivity)
    choose Mf hMf using hcov
    have hne : (Finset.univ : Finset (Fin d)).Nonempty :=
      Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hdpos)
    set C : ℝ := max ((Finset.univ : Finset (Fin d)).sup' hne Mf) 1 with hC
    have hC_pos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hCj : ∀ j, Mf j ≤ C := fun j =>
      le_trans (Finset.le_sup' Mf (Finset.mem_univ j)) (le_max_left _ _)
    have hsumbnd : (∑ _j : Fin d, ENNReal.ofReal (ε / d)) = ENNReal.ofReal ε := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast d, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [mul_comm, div_mul_cancel₀ ε hdR_ne]
    refine ⟨Real.sqrt d * C, fun n => ?_⟩
    refine le_trans (measure_mono ?_) (le_trans (measure_iUnion_fintype_le _
      (fun j => {X : Fin n → Ω |
        Mf j ≤ |(Real.sqrt n)⁻¹ * (∑ i : Fin n, g j (X i))|})) ?_)
    · intro X hX
      simp only [Set.mem_setOf_eq] at hX
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      by_contra hc
      push Not at hc
      have hall : ∀ j, |((Real.sqrt n)⁻¹ • (∑ i : Fin n,
            tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i))) j|
              < (Real.sqrt d * C) / Real.sqrt d := by
        intro j
        rw [hSn_coord n X j]
        calc |(Real.sqrt n)⁻¹ * (∑ i : Fin n, g j (X i))|
            < Mf j := hc j
          _ ≤ C := hCj j
          _ = (Real.sqrt d * C) / Real.sqrt d := by
              rw [eq_div_iff (ne_of_gt hsqrtd_pos)]; ring
      have hlt := norm_lt_of_forall_coord_lt _ (Real.sqrt d * C) hdpos
        (by positivity) hall
      exact absurd hX (not_le.mpr hlt)
    · exact le_trans (Finset.sum_le_sum (fun j _ => hMf j n)) hsumbnd.le

/-! ### Empirical Taylor algebraic identity -/

/-- Coordinate of the sample-point matrix action `scoreDerivApply` (rfl). -/
private lemma scoreDerivApply_ofLp
    (M : Matrix (Fin d) (Fin d) (Lp ℝ 2 P)) (x : Ω)
    (v : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    (scoreDerivApply M x v).ofLp j = ∑ k, (M j k : Ω → ℝ) x * v.ofLp k := rfl

/-- The **empirical Jacobian** matrix `D̂ₙ(X)_{jk} = n⁻¹ · Σᵢ (∂_θ ℓ̃)_{jk}(Xᵢ)`,
the sample mean of the score-derivative entries. By the LLN + matrix Bartlett it
converges to `−Ĩ` entrywise. -/
private noncomputable def empJacobian {n : ℕ}
    (M : Matrix (Fin d) (Fin d) (Lp ℝ 2 P)) (X : Fin n → Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun j k => (n : ℝ)⁻¹ * (∑ i : Fin n, (M j k : Ω → ℝ) (X i))

/-- **Jacobian-sum identity** (`n ≥ 1`). The normalized sum of the linearized
score-derivative action equals the empirical-Jacobian action on `Δₙ = √n·(θ̂−θ₀)`:
`(√n)⁻¹ · Σᵢ (∂_θℓ̃)(Xᵢ)·δ = toEuclideanCLM D̂ₙ(X) (√n·δ)`. The algebraic core
uses `(√n)⁻¹ = √n · n⁻¹`. -/
private lemma jacobian_sum
    (M : Matrix (Fin d) (Fin d) (Lp ℝ 2 P))
    {n : ℕ} (hn : 1 ≤ n) (X : Fin n → Ω) (δ : EuclideanSpace ℝ (Fin d)) :
    (Real.sqrt n)⁻¹ • (∑ i : Fin n, scoreDerivApply M (X i) δ)
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (empJacobian M X)
          (Real.sqrt n • δ) := by
  have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_sqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnR_pos)
  have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
  have h_sqrt_sq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnR_pos.le
  have h_inv_eq : (Real.sqrt (n : ℝ))⁻¹ = Real.sqrt n * ((n : ℝ)⁻¹) := by
    calc (Real.sqrt (n : ℝ))⁻¹
        = (Real.sqrt n)⁻¹ * 1 := by rw [mul_one]
      _ = (Real.sqrt n)⁻¹ * (Real.sqrt n * Real.sqrt n * (n : ℝ)⁻¹) := by
          rw [h_sqrt_sq, mul_inv_cancel₀ hnR_ne]
      _ = ((Real.sqrt n)⁻¹ * Real.sqrt n) * (Real.sqrt n * (n : ℝ)⁻¹) := by ring
      _ = 1 * (Real.sqrt n * (n : ℝ)⁻¹) := by rw [inv_mul_cancel₀ h_sqrt_ne]
      _ = Real.sqrt n * ((n : ℝ)⁻¹) := by rw [one_mul]
  apply (WithLp.equiv 2 (Fin d → ℝ)).injective
  funext j
  change ((Real.sqrt n)⁻¹ • (∑ i : Fin n, scoreDerivApply M (X i) δ)).ofLp j
      = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (empJacobian M X)
          (Real.sqrt n • δ)).ofLp j
  rw [Matrix.ofLp_toEuclideanCLM]
  simp only [WithLp.ofLp_smul, WithLp.ofLp_sum, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul, scoreDerivApply_ofLp, Matrix.mulVec, dotProduct, empJacobian]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [h_inv_eq]; ring

/-- **Empirical Taylor expansion** (`n ≥ 1`). The estimating function decomposes
as truth empirical process + empirical-Jacobian action + normalized remainder:
`(√n)⁻¹·Σᵢ ℓ̃_{θ̂}(Xᵢ) = (√n)⁻¹·Σᵢ ℓ̃(Xᵢ) + toEuclideanCLM D̂ₙ Δₙ + Rₙ`. -/
private lemma emp_expansion
    (_h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀)
    {n : ℕ} (hn : 1 ≤ n) (X : Fin n → Ω) :
    (Real.sqrt n)⁻¹ • (∑ i : Fin n, score_func_seq n X (X i))
      = ((Real.sqrt n)⁻¹ • (∑ i : Fin n,
            tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)))
        + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (empJacobian score_l_dot X)
            (Real.sqrt n • (estimator n X - θ₀))
        + ((Real.sqrt n)⁻¹ • (∑ i : Fin n,
            (score_func_seq n X (X i)
              - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
              - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀)))) := by
  have hsplit : ∀ i : Fin n, score_func_seq n X (X i)
      = tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
        + scoreDerivApply score_l_dot (X i) (estimator n X - θ₀)
        + (score_func_seq n X (X i)
            - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
            - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀)) := by
    intro i; abel
  rw [show (∑ i : Fin n, score_func_seq n X (X i))
        = ∑ i : Fin n, (tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
            + scoreDerivApply score_l_dot (X i) (estimator n X - θ₀)
            + (score_func_seq n X (X i)
                - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
                - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀)))
      from Finset.sum_congr rfl (fun i _ => hsplit i)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, smul_add, smul_add,
    jacobian_sum score_l_dot hn X (estimator n X - θ₀)]

/-- **Core master identity** (`n ≥ 1`). Regroups `emp_expansion` via CLM
additivity of `toEuclideanCLM`:
`toEuclideanCLM Ĩ Δₙ = toEuclideanCLM (Ĩ + D̂ₙ) Δₙ + Sₙ + Rₙ − Lₙ`,
where `Sₙ = (√n)⁻¹·Σᵢ ℓ̃(Xᵢ)`, `Lₙ = (√n)⁻¹·Σᵢ ℓ̃_{θ̂}(Xᵢ)`, `Rₙ` the remainder. -/
private lemma core_identity
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀)
    {n : ℕ} (hn : 1 ≤ n) (X : Fin n → Ω) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
        (efficientInformationMatrix S_θ T_nuis e)
        (Real.sqrt n • (estimator n X - θ₀))
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (efficientInformationMatrix S_θ T_nuis e + empJacobian score_l_dot X)
          (Real.sqrt n • (estimator n X - θ₀))
        + ((Real.sqrt n)⁻¹ • (∑ i : Fin n,
            tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)))
        + ((Real.sqrt n)⁻¹ • (∑ i : Fin n,
            (score_func_seq n X (X i)
              - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
              - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀))))
        - ((Real.sqrt n)⁻¹ • (∑ i : Fin n, score_func_seq n X (X i))) := by
  have hexp := emp_expansion h hn X
  have hadd : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
        (efficientInformationMatrix S_θ T_nuis e + empJacobian score_l_dot X)
        (Real.sqrt n • (estimator n X - θ₀))
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (efficientInformationMatrix S_θ T_nuis e)
          (Real.sqrt n • (estimator n X - θ₀))
        + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (empJacobian score_l_dot X)
          (Real.sqrt n • (estimator n X - θ₀)) := by
    rw [map_add, ContinuousLinearMap.add_apply]
  rw [hadd, hexp]
  abel

/-! ### Frobenius smallness of `Ĩ + D̂ₙ` -/

/-- **Frobenius `o_P` of `Ĩ + D̂ₙ`.** For every `δ > 0`, the `Pⁿ`-probability that
the Frobenius norm `√(Σⱼₖ (Ĩ + D̂ₙ)_{jk}²)` exceeds `δ` tends to `0`, since each
entry `(Ĩ + D̂ₙ)_{jk} →_P 0` by the entrywise LLN (`zEstimatorVec_step4_lln`). Union
bound over the `d²` entries. -/
private lemma frobenius_oP
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀) :
    ∀ δ > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | δ ≤ Real.sqrt (∑ j, ∑ k,
          ((efficientInformationMatrix S_θ T_nuis e
            + empJacobian score_l_dot X) j k) ^ 2)})
      atTop (𝓝 0) := by
  intro δ hδ
  by_cases hd0 : d = 0
  · have hemp : ∀ n : ℕ, {X : Fin n → Ω | δ ≤ Real.sqrt (∑ j, ∑ k,
        ((efficientInformationMatrix S_θ T_nuis e
          + empJacobian score_l_dot X) j k) ^ 2)} = ∅ := by
      intro n; ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      subst hd0
      simp only [Finset.univ_eq_empty, Finset.sum_empty, Real.sqrt_zero]
      exact hδ
    simp only [hemp, measure_empty]; exact tendsto_const_nhds
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hdR_ne : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
    haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hdpos
    -- Per-entry set equality: `(Ĩ + D̂ₙ)_{jk} = n⁻¹·Σ ℓ̇_{jk} + Ĩ_{jk}` (as sets).
    have hset : ∀ (p : Fin d × Fin d) (n : ℕ),
        {X : Fin n → Ω | δ / d ≤ |(efficientInformationMatrix S_θ T_nuis e
            + empJacobian score_l_dot X) p.1 p.2|}
          = {X : Fin n → Ω | δ / d ≤ |(n : ℝ)⁻¹
              * (∑ i : Fin n, (score_l_dot p.1 p.2 : Ω → ℝ) (X i))
              + efficientInformationMatrix S_θ T_nuis e p.1 p.2|} := by
      intro p n; ext X
      simp only [Set.mem_setOf_eq, Matrix.add_apply, empJacobian, add_comm]
    -- Upper bound: sum over entries of the step-4 probabilities → 0.
    have hup : Tendsto (fun n : ℕ => ∑ p : Fin d × Fin d,
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | δ / d ≤ |(efficientInformationMatrix S_θ T_nuis e
            + empJacobian score_l_dot X) p.1 p.2|})
        atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ∑ _p : Fin d × Fin d, (0 : ℝ≥0∞) by simp]
      refine tendsto_finset_sum _ (fun p _ => ?_)
      have hfun : (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | δ / d ≤ |(efficientInformationMatrix S_θ T_nuis e
              + empJacobian score_l_dot X) p.1 p.2|})
          = (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | δ / d ≤ |(n : ℝ)⁻¹
              * (∑ i : Fin n, (score_l_dot p.1 p.2 : Ω → ℝ) (X i))
              + efficientInformationMatrix S_θ T_nuis e p.1 p.2|}) := by
        funext n; rw [hset p n]
      rw [hfun]
      exact zEstimatorVec_step4_lln h p.1 p.2 (δ / d) (by positivity)
    -- Squeeze.
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · exact Filter.Eventually.of_forall (fun _ => zero_le)
    · refine Filter.Eventually.of_forall (fun n => ?_)
      refine le_trans (measure_mono ?_) (measure_iUnion_fintype_le _
        (fun p : Fin d × Fin d => {X : Fin n → Ω |
          δ / d ≤ |(efficientInformationMatrix S_θ T_nuis e
            + empJacobian score_l_dot X) p.1 p.2|}))
      intro X hX
      simp only [Set.mem_setOf_eq] at hX
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      by_contra hc
      push Not at hc
      have hδd_pos : (0 : ℝ) < δ / d := by positivity
      have hsum_lt : (∑ j, ∑ k,
          ((efficientInformationMatrix S_θ T_nuis e
            + empJacobian score_l_dot X) j k) ^ 2) < δ ^ 2 := by
        have h1 : (∑ p : Fin d × Fin d,
              ((efficientInformationMatrix S_θ T_nuis e
                + empJacobian score_l_dot X) p.1 p.2) ^ 2)
            < ∑ _p : Fin d × Fin d, (δ / d) ^ 2 := by
          refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun p _ => ?_)
          have hp := hc p
          nlinarith [hp, abs_nonneg (((efficientInformationMatrix S_θ T_nuis e
            + empJacobian score_l_dot X) p.1 p.2)),
            sq_abs (((efficientInformationMatrix S_θ T_nuis e
              + empJacobian score_l_dot X) p.1 p.2))]
        rw [Fintype.sum_prod_type] at h1
        have hconst : (∑ _p : Fin d × Fin d, (δ / (d : ℝ)) ^ 2) = δ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
            Fintype.card_fin, nsmul_eq_mul]
          have hcast : ((d * d : ℕ) : ℝ) = (d : ℝ) ^ 2 := by push_cast; ring
          rw [hcast, div_pow]
          field_simp
        rwa [hconst] at h1
      have hlt : Real.sqrt (∑ j, ∑ k,
          ((efficientInformationMatrix S_θ T_nuis e
            + empJacobian score_l_dot X) j k) ^ 2) < δ := by
        rw [show δ = Real.sqrt (δ ^ 2) from (Real.sqrt_sq hδ.le).symm]
        exact Real.sqrt_lt_sqrt
          (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
          hsum_lt
      exact absurd hX (not_le.mpr hlt)

/-! ### The rate bootstrap `√n·(θ̂−θ₀) = O_P(1)` -/

set_option maxHeartbeats 1600000 in
-- The matrix-bootstrap proof below needs 1,600,000 heartbeats; the default 200,000 times out.
/-- **Bootstrap `√n·(θ̂−θ₀) = O_P(1)` (eventual form).** For every `η > 0` there
is a bound `M` with `Pⁿ{M ≤ ‖√n·(θ̂−θ₀)‖} ≤ η` eventually. The matrix bootstrap:
from the core identity `Ĩ·Δₙ = (Ĩ+D̂ₙ)·Δₙ + Sₙ + Rₙ − Lₙ`, invertibility of `Ĩ`
(coercivity `‖Δₙ‖ ≤ C·‖Ĩ·Δₙ‖`), the Frobenius smallness of `Ĩ+D̂ₙ`, and the
`O_P(1)`/`o_P` bounds on `Sₙ, Rₙ, Lₙ`, absorb `(Ĩ+D̂ₙ)·Δₙ` on a good event to get
`‖Δₙ‖ ≤ 2C(‖Sₙ‖+‖Rₙ‖+‖Lₙ‖)`. Vector lift of the scalar Step 5. -/
private lemma zEstimatorVec_step5
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀) :
    ∀ η > 0, ∃ M : ℝ, ∀ᶠ n in atTop,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | M ≤ ‖Real.sqrt n • (estimator n X - θ₀)‖}
      ≤ ENNReal.ofReal η := by
  intro η hη
  -- Coercivity constant `C = max ‖toEuclideanCLM Ĩ⁻¹‖ 1`.
  set C : ℝ := max ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
      (efficientInformationMatrix S_θ T_nuis e)⁻¹‖ 1 with hC
  have hC_pos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCinv_le : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
      (efficientInformationMatrix S_θ T_nuis e)⁻¹‖ ≤ C := le_max_left _ _
  have hLI : ∀ w : EuclideanSpace ℝ (Fin d),
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (efficientInformationMatrix S_θ T_nuis e)⁻¹
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
            (efficientInformationMatrix S_θ T_nuis e) w) = w := by
    intro w
    have hInv : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (efficientInformationMatrix S_θ T_nuis e)⁻¹
        * Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
            (efficientInformationMatrix S_θ T_nuis e) = 1 := by
      rw [← map_mul, Matrix.nonsing_inv_mul _
        ((Matrix.isUnit_iff_isUnit_det _).mp h.hPD.isUnit), map_one]
    rw [← ContinuousLinearMap.mul_apply, hInv, ContinuousLinearMap.one_apply]
  have hcoercive : ∀ w : EuclideanSpace ℝ (Fin d),
      ‖w‖ ≤ C * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (efficientInformationMatrix S_θ T_nuis e) w‖ := by
    intro w
    calc ‖w‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
              (efficientInformationMatrix S_θ T_nuis e)⁻¹
              (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
                (efficientInformationMatrix S_θ T_nuis e) w)‖ := by rw [hLI]
      _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
              (efficientInformationMatrix S_θ T_nuis e)⁻¹‖
            * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
                (efficientInformationMatrix S_θ T_nuis e) w‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
                (efficientInformationMatrix S_θ T_nuis e) w‖ :=
          mul_le_mul_of_nonneg_right hCinv_le (norm_nonneg _)
  -- Sₙ `O_P(1)` at `η/4`.
  obtain ⟨M_S, hM_S⟩ := zEstimatorVec_Sn_OP1 S_θ T_nuis e (η / 4) (by linarith)
  set M : ℝ := 6 * C * (|M_S| + 1) with hM
  have hM_pos : 0 < M := by positivity
  have h6C_pos : (0 : ℝ) < 6 * C := by positivity
  have hM6C : M_S ≤ M / (6 * C) := by
    rw [hM, mul_comm (6 * C) (|M_S| + 1), mul_div_assoc,
      div_self (ne_of_gt h6C_pos), mul_one]
    linarith [le_abs_self M_S]
  have hτ_pos : 0 < M / (6 * C) := by positivity
  -- Three `o_P` ingredients at threshold `M/(6C)` and Frobenius smallness at `1/(2C)`.
  have hfrob := frobenius_oP h (1 / (2 * C)) (by positivity)
  have hstep3 := zEstimatorVec_step3_taylor h (M / (6 * C)) hτ_pos
  have hscore := h.score_eq_vec (M / (6 * C)) hτ_pos
  rw [ENNReal.tendsto_nhds_zero] at hfrob hstep3 hscore
  have hfrob_le := hfrob (ENNReal.ofReal (η / 4)) (by positivity)
  have hstep3_le := hstep3 (ENNReal.ofReal (η / 4)) (by positivity)
  have hscore_le := hscore (ENNReal.ofReal (η / 4)) (by positivity)
  refine ⟨M, ?_⟩
  filter_upwards [hfrob_le, hstep3_le, hscore_le, eventually_ge_atTop 1]
    with n hfr h3 hsc hn1
  -- Union-bound inclusion (n ≥ 1).
  have hincl : {X : Fin n → Ω | M ≤ ‖Real.sqrt n • (estimator n X - θ₀)‖}
      ⊆ ({X : Fin n → Ω | 1 / (2 * C) ≤ Real.sqrt (∑ j, ∑ k,
              ((efficientInformationMatrix S_θ T_nuis e
                + empJacobian score_l_dot X) j k) ^ 2)}
          ∪ {X : Fin n → Ω | M / (6 * C) ≤ ‖(Real.sqrt n)⁻¹ • (∑ i,
              tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i))‖})
        ∪ ({X : Fin n → Ω | M / (6 * C) ≤ ‖(Real.sqrt n)⁻¹ • (∑ i,
              (score_func_seq n X (X i)
                - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
                - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀)))‖}
            ∪ {X : Fin n → Ω | M / (6 * C) ≤ ‖(Real.sqrt n)⁻¹ • (∑ i,
                score_func_seq n X (X i))‖}) := by
    intro X hX
    simp only [Set.mem_setOf_eq] at hX
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra hc
    push Not at hc
    obtain ⟨⟨hcB, hcS⟩, hcR, hcL⟩ := hc
    have hci := core_identity h hn1 X
    have hΔpos : 0 < ‖Real.sqrt n • (estimator n X - θ₀)‖ :=
      lt_of_lt_of_le hM_pos hX
    -- triangle bound
    have htri : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
            (efficientInformationMatrix S_θ T_nuis e)
            (Real.sqrt n • (estimator n X - θ₀))‖
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
              (efficientInformationMatrix S_θ T_nuis e + empJacobian score_l_dot X)
              (Real.sqrt n • (estimator n X - θ₀))‖
          + ‖(Real.sqrt n)⁻¹ • (∑ i,
              tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i))‖
          + ‖(Real.sqrt n)⁻¹ • (∑ i,
              (score_func_seq n X (X i)
                - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
                - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀)))‖
          + ‖(Real.sqrt n)⁻¹ • (∑ i, score_func_seq n X (X i))‖ := by
      rw [hci]
      refine le_trans (norm_sub_le _ _) (add_le_add ?_ le_rfl)
      refine le_trans (norm_add_le _ _) (add_le_add ?_ le_rfl)
      exact norm_add_le _ _
    have hfrob_bd := norm_toEuclideanCLM_apply_le
      (efficientInformationMatrix S_θ T_nuis e + empJacobian score_l_dot X)
      (Real.sqrt n • (estimator n X - θ₀))
    have hcoerc := hcoercive (Real.sqrt n • (estimator n X - θ₀))
    -- abbreviations
    set Δ : ℝ := ‖Real.sqrt n • (estimator n X - θ₀)‖ with hΔ
    set Bn : ℝ := Real.sqrt (∑ j, ∑ k,
        ((efficientInformationMatrix S_θ T_nuis e
          + empJacobian score_l_dot X) j k) ^ 2) with hBn
    set Sn : ℝ := ‖(Real.sqrt n)⁻¹ • (∑ i,
        tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i))‖ with hSn
    set Rn : ℝ := ‖(Real.sqrt n)⁻¹ • (∑ i,
        (score_func_seq n X (X i)
          - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
          - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀)))‖ with hRn
    set Ln : ℝ := ‖(Real.sqrt n)⁻¹ • (∑ i, score_func_seq n X (X i))‖ with hLn
    -- combined: ‖Δ‖ ≤ C·Bn·Δ + C·Sn + C·Rn + C·Ln
    have hb1 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (efficientInformationMatrix S_θ T_nuis e)
          (Real.sqrt n • (estimator n X - θ₀))‖ ≤ Bn * Δ + Sn + Rn + Ln := by
      refine le_trans htri ?_
      have := hfrob_bd
      linarith [this]
    have hb2 : Δ ≤ C * Bn * Δ + C * Sn + C * Rn + C * Ln := by
      have hstep := le_trans hcoerc (mul_le_mul_of_nonneg_left hb1 hC_pos.le)
      nlinarith [hstep]
    -- convert strict bounds
    have hcB' : Bn * (2 * C) < 1 := (lt_div_iff₀ (by positivity)).mp hcB
    have hcS' : Sn * (6 * C) < M := (lt_div_iff₀ h6C_pos).mp hcS
    have hcR' : Rn * (6 * C) < M := (lt_div_iff₀ h6C_pos).mp hcR
    have hcL' : Ln * (6 * C) < M := (lt_div_iff₀ h6C_pos).mp hcL
    have hCBn_lt : C * Bn < 1 / 2 := by nlinarith [hcB', hC_pos]
    have h1 : C * Bn * Δ < (1 / 2) * Δ :=
      mul_lt_mul_of_pos_right hCBn_lt hΔpos
    have hCS_lt : C * Sn < M / 6 := by nlinarith [hcS', hC_pos]
    have hCR_lt : C * Rn < M / 6 := by nlinarith [hcR', hC_pos]
    have hCL_lt : C * Ln < M / 6 := by nlinarith [hcL', hC_pos]
    linarith [hb2, h1, hCS_lt, hCR_lt, hCL_lt, hX]
  -- Assemble the union bound on measures.
  refine le_trans (measure_mono hincl) ?_
  refine le_trans (measure_union_le _ _)
    (le_trans (add_le_add (measure_union_le _ _) (measure_union_le _ _)) ?_)
  have hSbnd : (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω | M / (6 * C) ≤ ‖(Real.sqrt n)⁻¹ • (∑ i,
        tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i))‖}
      ≤ ENNReal.ofReal (η / 4) :=
    le_trans (measure_mono (fun X hh => le_trans hM6C hh)) (hM_S n)
  have hη4_nn : (0 : ℝ) ≤ η / 4 := by linarith
  have h_sum_eps : ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4)
        + (ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4))
      = ENNReal.ofReal η := by
    rw [(ENNReal.ofReal_add hη4_nn hη4_nn).symm]
    rw [(ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ η/4 + η/4)
          (by linarith : (0:ℝ) ≤ η/4 + η/4)).symm]
    congr 1; ring
  exact le_trans (add_le_add (add_le_add hfr hSbnd) (add_le_add h3 hsc)) h_sum_eps.le

/-! ### Cross term `(Ĩ + D̂ₙ)·Δₙ →_P 0` -/

/-- **Cross term `o_P`.** `toEuclideanCLM (Ĩ + D̂ₙ) Δₙ →_P 0`: the product of the
Frobenius-`o_P` factor `√(Σ (Ĩ+D̂ₙ)²)` (`frobenius_oP`) and the `O_P(1)` factor
`‖Δₙ‖` (`zEstimatorVec_step5`), bounded by `norm_toEuclideanCLM_apply_le`. -/
private lemma crossterm_oP
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀) :
    ∀ τ > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | τ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (efficientInformationMatrix S_θ T_nuis e + empJacobian score_l_dot X)
          (Real.sqrt n • (estimator n X - θ₀))‖})
      atTop (𝓝 0) := by
  intro τ hτ
  rw [ENNReal.tendsto_nhds_zero]
  intro c hc
  by_cases hc_inf : c = ⊤
  · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
  have hcr_pos : 0 < c.toReal := ENNReal.toReal_pos hc.ne' hc_inf
  obtain ⟨M0, hM0⟩ := zEstimatorVec_step5 h (c.toReal / 2) (by positivity)
  set M : ℝ := max M0 1 with hMdef
  have hM_pos : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM_bound : ∀ᶠ n in atTop, (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω | M ≤ ‖Real.sqrt n • (estimator n X - θ₀)‖}
      ≤ ENNReal.ofReal (c.toReal / 2) := by
    filter_upwards [hM0] with n hn
    exact le_trans (measure_mono (fun X hh => le_trans (le_max_left M0 1) hh)) hn
  have hfrob := frobenius_oP h (τ / M) (by positivity)
  rw [ENNReal.tendsto_nhds_zero] at hfrob
  have hfrob' := hfrob (ENNReal.ofReal (c.toReal / 2)) (by positivity)
  filter_upwards [hM_bound, hfrob'] with n hMn hBn
  -- Union-bound inclusion.
  have hincl : {X : Fin n → Ω | τ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
        (efficientInformationMatrix S_θ T_nuis e + empJacobian score_l_dot X)
        (Real.sqrt n • (estimator n X - θ₀))‖}
      ⊆ {X : Fin n → Ω | τ / M ≤ Real.sqrt (∑ j, ∑ k,
            ((efficientInformationMatrix S_θ T_nuis e
              + empJacobian score_l_dot X) j k) ^ 2)}
        ∪ {X : Fin n → Ω | M ≤ ‖Real.sqrt n • (estimator n X - θ₀)‖} := by
    intro X hX
    simp only [Set.mem_setOf_eq] at hX
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra hcc
    push Not at hcc
    obtain ⟨hcB, hcΔ⟩ := hcc
    have hfb := norm_toEuclideanCLM_apply_le
      (efficientInformationMatrix S_θ T_nuis e + empJacobian score_l_dot X)
      (Real.sqrt n • (estimator n X - θ₀))
    have hBn_nn : (0 : ℝ) ≤ Real.sqrt (∑ j, ∑ k,
        ((efficientInformationMatrix S_θ T_nuis e
          + empJacobian score_l_dot X) j k) ^ 2) := Real.sqrt_nonneg _
    have hprod : Real.sqrt (∑ j, ∑ k,
        ((efficientInformationMatrix S_θ T_nuis e
          + empJacobian score_l_dot X) j k) ^ 2)
        * ‖Real.sqrt n • (estimator n X - θ₀)‖ < τ := by
      have := mul_lt_mul'' hcB hcΔ hBn_nn (norm_nonneg _)
      rwa [div_mul_cancel₀ τ (ne_of_gt hM_pos)] at this
    exact absurd hX (not_le.mpr (lt_of_le_of_lt hfb hprod))
  refine le_trans (measure_mono hincl) (le_trans (measure_union_le _ _) ?_)
  have hsum : ENNReal.ofReal (c.toReal / 2) + ENNReal.ofReal (c.toReal / 2) = c := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [show c.toReal / 2 + c.toReal / 2 = c.toReal by ring, ENNReal.ofReal_toReal hc_inf]
  rw [← hsum]
  exact add_le_add hBn hMn

/-! ### The `d × d` master identity -/

/-- From the native bundle,
`√n · Ĩ·(θ̂_n − θ₀) − 𝔾ₙℓ̃ = o_P` under `Pⁿ`, i.e. for every `ε > 0` the
`Pⁿ`-probability that the Euclidean norm of
`Ĩ·(√n·(θ̂_n − θ₀)) − (√n)⁻¹·Σᵢ ℓ̃(Xᵢ)` exceeds `ε` tends to `0`, where
`Ĩ = efficientInformationMatrix S_θ T_nuis e` acts as `Matrix.toEuclideanCLM Ĩ`
and `ℓ̃(x) = tupleEval P (ℓ̃(e·)) x` is the vector efficient score.

The sign agrees with the scalar master identity in
`Discharge/ZEstimator.lean`, which reads
`Ĩ·√n·(est − θ₀) − (√n)⁻¹·Σ ℓ̃ = o_P` (minus on the empirical-process term) so
that applying `Ĩ⁻¹` yields `+Ĩ⁻¹ℓ̃ = candidateVecEIF`. -/
theorem zEstimatorVec_master_identity
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
                  (efficientInformationMatrix S_θ T_nuis e)
                  (Real.sqrt n • (estimator n X - θ₀))
                - (Real.sqrt n)⁻¹
                  • (∑ i, tupleEval P
                        (fun j => efficientScore S_θ T_nuis (e j)) (X i))‖})
      atTop (𝓝 0) := by
  intro ε hε
  have hcross := crossterm_oP h (ε / 3) (by positivity)
  have hstep3 := zEstimatorVec_step3_taylor h (ε / 3) (by positivity)
  have hscore := h.score_eq_vec (ε / 3) (by positivity)
  have hupper : Tendsto
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | ε / 3 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
              (efficientInformationMatrix S_θ T_nuis e + empJacobian score_l_dot X)
              (Real.sqrt n • (estimator n X - θ₀))‖}
          + (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | ε / 3 ≤ ‖(Real.sqrt n)⁻¹ • (∑ i,
              (score_func_seq n X (X i)
                - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
                - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀)))‖}
          + (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | ε / 3 ≤ ‖(Real.sqrt n)⁻¹ • (∑ i,
              score_func_seq n X (X i))‖})
      atTop (𝓝 0) := by
    have := (hcross.add hstep3).add hscore
    simpa using this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall (fun _ => zero_le)
  · filter_upwards [eventually_ge_atTop 1] with n hn1
    have hincl : {X : Fin n → Ω |
          ε ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
                  (efficientInformationMatrix S_θ T_nuis e)
                  (Real.sqrt n • (estimator n X - θ₀))
                - (Real.sqrt n)⁻¹ • (∑ i, tupleEval P
                    (fun j => efficientScore S_θ T_nuis (e j)) (X i))‖}
        ⊆ ({X : Fin n → Ω | ε / 3 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
              (efficientInformationMatrix S_θ T_nuis e + empJacobian score_l_dot X)
              (Real.sqrt n • (estimator n X - θ₀))‖}
            ∪ {X : Fin n → Ω | ε / 3 ≤ ‖(Real.sqrt n)⁻¹ • (∑ i,
              (score_func_seq n X (X i)
                - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
                - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀)))‖})
          ∪ {X : Fin n → Ω | ε / 3 ≤ ‖(Real.sqrt n)⁻¹ • (∑ i,
              score_func_seq n X (X i))‖} := by
      intro X hX
      simp only [Set.mem_setOf_eq] at hX
      simp only [Set.mem_union, Set.mem_setOf_eq]
      by_contra hcc
      push Not at hcc
      obtain ⟨⟨hcC, hcR⟩, hcL⟩ := hcc
      have hres : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
              (efficientInformationMatrix S_θ T_nuis e)
              (Real.sqrt n • (estimator n X - θ₀))
            - (Real.sqrt n)⁻¹ • (∑ i, tupleEval P
                (fun j => efficientScore S_θ T_nuis (e j)) (X i))
          = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
              (efficientInformationMatrix S_θ T_nuis e + empJacobian score_l_dot X)
              (Real.sqrt n • (estimator n X - θ₀))
            + ((Real.sqrt n)⁻¹ • (∑ i,
                (score_func_seq n X (X i)
                  - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
                  - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀))))
            - ((Real.sqrt n)⁻¹ • (∑ i, score_func_seq n X (X i))) := by
        rw [core_identity h hn1 X]; abel
      rw [hres] at hX
      set A := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (efficientInformationMatrix S_θ T_nuis e + empJacobian score_l_dot X)
          (Real.sqrt n • (estimator n X - θ₀)) with hA
      set B := (Real.sqrt n)⁻¹ • (∑ i,
          (score_func_seq n X (X i)
            - tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)
            - scoreDerivApply score_l_dot (X i) (estimator n X - θ₀))) with hB
      set D := (Real.sqrt n)⁻¹ • (∑ i, score_func_seq n X (X i)) with hD
      have hlt : ‖A + B - D‖ < ε :=
        calc ‖A + B - D‖ ≤ ‖A + B‖ + ‖D‖ := norm_sub_le _ _
          _ ≤ ‖A‖ + ‖B‖ + ‖D‖ := add_le_add (norm_add_le _ _) le_rfl
          _ < ε := by linarith [hcC, hcR, hcL]
      exact absurd hX (not_le.mpr hlt)
    exact le_trans (measure_mono hincl)
      (le_trans (measure_union_le _ _)
        (add_le_add (measure_union_le _ _) le_rfl))

/-! ### Linear representation by applying `Ĩ⁻¹` -/

/-- Apply the continuous linear map `Matrix.toEuclideanCLM Ĩ⁻¹` to the master
identity and collapse `Ĩ⁻¹ Ĩ = 1`, obtaining the native asymptotic-linearity
residual with influence `−Ĩ⁻¹𝔾ₙℓ̃`:
`√n·(θ̂_n − θ₀) − (√n)⁻¹·Σᵢ (Ĩ⁻¹ ℓ̃)(Xᵢ) = o_P` under `Pⁿ`.

The Lipschitz bound for this map transfers the corresponding `o_P(1)`
statement in the `Measure.pi` encoding. -/
theorem zEstimatorVec_linear_representation
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ ‖Real.sqrt n • (estimator n X - θ₀)
                - (Real.sqrt n)⁻¹
                  • (∑ i, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
                        (efficientInformationMatrix S_θ T_nuis e)⁻¹
                        (tupleEval P
                          (fun j => efficientScore S_θ T_nuis (e j)) (X i)))‖})
      atTop (𝓝 0) := by
  intro ε hε
  set L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
      (efficientInformationMatrix S_θ T_nuis e)⁻¹ with hL
  have hden : (0 : ℝ) < ‖L‖ + 1 := by positivity
  have h3 := zEstimatorVec_master_identity h (ε / (‖L‖ + 1)) (div_pos hε hden)
  -- `L ∘ toEuclideanCLM Ĩ = id` (Ĩ invertible from `hPD`).
  have hLI : ∀ w : EuclideanSpace ℝ (Fin d),
      L (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (efficientInformationMatrix S_θ T_nuis e) w) = w := by
    intro w
    have hInv : L * Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (efficientInformationMatrix S_θ T_nuis e) = 1 := by
      rw [hL, ← map_mul, Matrix.nonsing_inv_mul _
        ((Matrix.isUnit_iff_isUnit_det _).mp h.hPD.isUnit), map_one]
    rw [← ContinuousLinearMap.mul_apply, hInv, ContinuousLinearMap.one_apply]
  -- Pointwise identity: the linear-representation residual is `L` applied to
  -- the information-weighted residual.
  have hpt : ∀ (n : ℕ) (X : Fin n → Ω),
      Real.sqrt n • (estimator n X - θ₀)
          - (Real.sqrt n)⁻¹ • (∑ i, L (tupleEval P
                (fun j => efficientScore S_θ T_nuis (e j)) (X i)))
        = L (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
              (efficientInformationMatrix S_θ T_nuis e)
              (Real.sqrt n • (estimator n X - θ₀))
            - (Real.sqrt n)⁻¹ • (∑ i, tupleEval P
                (fun j => efficientScore S_θ T_nuis (e j)) (X i))) := by
    intro n X
    rw [map_sub, hLI, map_smul, map_sum]
  -- Lipschitz inclusion between the corresponding exceedance sets.
  have hsub : ∀ n : ℕ,
      {X : Fin n → Ω | ε ≤ ‖Real.sqrt n • (estimator n X - θ₀)
          - (Real.sqrt n)⁻¹ • (∑ i, L (tupleEval P
                (fun j => efficientScore S_θ T_nuis (e j)) (X i)))‖}
        ⊆ {X : Fin n → Ω | ε / (‖L‖ + 1) ≤
            ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
                (efficientInformationMatrix S_θ T_nuis e)
                (Real.sqrt n • (estimator n X - θ₀))
              - (Real.sqrt n)⁻¹ • (∑ i, tupleEval P
                  (fun j => efficientScore S_θ T_nuis (e j)) (X i))‖} := by
    intro n X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    rw [hpt] at hX
    have hbound := L.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
        (efficientInformationMatrix S_θ T_nuis e)
        (Real.sqrt n • (estimator n X - θ₀))
      - (Real.sqrt n)⁻¹ • (∑ i, tupleEval P
          (fun j => efficientScore S_θ T_nuis (e j)) (X i)))
    rw [div_le_iff₀ hden]
    nlinarith [hbound, hX, norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
      (efficientInformationMatrix S_θ T_nuis e) (Real.sqrt n • (estimator n X - θ₀))
      - (Real.sqrt n)⁻¹ • (∑ i, tupleEval P
          (fun j => efficientScore S_θ T_nuis (e j)) (X i)))]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
    (Eventually.of_forall fun n => zero_le)
    (Eventually.of_forall fun n => measure_mono (hsub n))

/-! ### Sample-level influence bridge -/

/-- For `P`-almost every sample point `x`, applying `Ĩ⁻¹` as a continuous linear map
to the vector efficient score `ℓ̃(x)` yields the sample evaluation of the vector EIF:
`toEuclideanCLM Ĩ⁻¹ (ℓ̃(x)) = candidateVecEIF(x)`.

This identity is almost-everywhere rather than pointwise because `tupleEval P φ x`
(`Core/EfficiencyOperationalVec.lean`) reads the `Lp.coeFn` a.e.-representative, and
the underlying identity `⇑(∑ₖ (Ĩ⁻¹)ⱼₖ • ℓ̃ₖ) x = ∑ₖ (Ĩ⁻¹)ⱼₖ · ⇑ℓ̃ₖ x` holds only
`P`-a.e. -/
theorem native_influence_eq_candidateVecEIF
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (e : Fin d → Θ) :
    (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
        (efficientInformationMatrix S_θ T_nuis e)⁻¹
        (tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) x))
      =ᵐ[P] (fun x => tupleEval P (candidateVecEIF S_θ T_nuis e) x) := by
  classical
  -- (1) Per-coordinate a.e. representation of `candidateVecEIF j`.
  have hcoord : ∀ j : Fin d,
      (fun x => ((candidateVecEIF S_θ T_nuis e j : ↥(L2ZeroMean P)) : Lp ℝ 2 P) x)
        =ᵐ[P] (fun x => ∑ k, (efficientInformationMatrix S_θ T_nuis e)⁻¹ j k
              * ((efficientScore S_θ T_nuis (e k) : ↥(L2ZeroMean P)) : Lp ℝ 2 P) x) := by
    intro j
    have hce : ((candidateVecEIF S_θ T_nuis e j : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
        = ∑ k, (efficientInformationMatrix S_θ T_nuis e)⁻¹ j k
              • ((efficientScore S_θ T_nuis (e k) : ↥(L2ZeroMean P)) : Lp ℝ 2 P) := by
      rw [candidateVecEIF]
      simp only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul]
    rw [hce]
    refine (Lp_coeFn_finset_sum Finset.univ
      (fun k => (efficientInformationMatrix S_θ T_nuis e)⁻¹ j k
        • ((efficientScore S_θ T_nuis (e k) : ↥(L2ZeroMean P)) : Lp ℝ 2 P))).trans ?_
    -- Per-`k` `Lp.coeFn_smul` (coeFn commutes with the scalar smul, a.e.), driven by the
    -- lemma type so the coercion stays *outside* the smul.
    have hsmul : ∀ k : Fin d,
        (⇑((efficientInformationMatrix S_θ T_nuis e)⁻¹ j k
            • ((efficientScore S_θ T_nuis (e k) : ↥(L2ZeroMean P)) : Lp ℝ 2 P)) : Ω → ℝ)
          =ᵐ[P] (efficientInformationMatrix S_θ T_nuis e)⁻¹ j k
            • (⇑((efficientScore S_θ T_nuis (e k) : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) :=
      fun k => Lp.coeFn_smul _ _
    filter_upwards [ae_all_iff.mpr hsmul] with x hx
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hx k, Pi.smul_apply, smul_eq_mul]
  -- (2) Assemble the coordinate a.e. identities into the vector a.e. equality.
  have hall : ∀ᵐ x ∂P, ∀ j : Fin d,
      ((candidateVecEIF S_θ T_nuis e j : ↥(L2ZeroMean P)) : Lp ℝ 2 P) x
        = ∑ k, (efficientInformationMatrix S_θ T_nuis e)⁻¹ j k
              * ((efficientScore S_θ T_nuis (e k) : ↥(L2ZeroMean P)) : Lp ℝ 2 P) x := by
    rw [ae_all_iff]; exact hcoord
  filter_upwards [hall] with x hx
  apply (WithLp.equiv 2 (Fin d → ℝ)).injective
  funext j
  change (∑ k, (efficientInformationMatrix S_θ T_nuis e)⁻¹ j k
        * ((efficientScore S_θ T_nuis (e k) : ↥(L2ZeroMean P)) : Lp ℝ 2 P) x)
      = ((candidateVecEIF S_θ T_nuis e j : ↥(L2ZeroMean P)) : Lp ℝ 2 P) x
  exact (hx j).symm

/-! ### Smooth conditional asymptotic linearity -/

/-- From the linear representation and the sample-level bridge,
the supplied estimator is asymptotically linear at `P` with influence tuple
`candidateVecEIF S_θ T_nuis e` and vector centering `θ₀`. This is the generic
smooth conditional theorem, not Theorem 25.77. -/
theorem mle_asympLinear_of_nativeTaylorCore_vec
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀) :
    AsymptoticallyLinearAt_vec estimator P
      (candidateVecEIF S_θ T_nuis e) θ₀ := by
  intro ε hε
  refine (zEstimatorVec_linear_representation h ε hε).congr (fun n => ?_)
  refine MeasureTheory.measure_congr ?_
  rw [Filter.eventuallyEq_set]
  -- The sample-level identity is lifted through each coordinate `X i`.
  have h5 := native_influence_eq_candidateVecEIF S_θ T_nuis e
  have h_all : ∀ᵐ X ∂(Measure.pi (fun _ : Fin n => P)), ∀ i : Fin n,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (efficientInformationMatrix S_θ T_nuis e)⁻¹
          (tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i))
        = tupleEval P (candidateVecEIF S_θ T_nuis e) (X i) := by
    rw [ae_all_iff]
    intro i
    have hmp := MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => P) i
    exact h5.comp_tendsto hmp.quasiMeasurePreserving.tendsto_ae
  filter_upwards [h_all] with X hX
  have hsum : (∑ i, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
        (efficientInformationMatrix S_θ T_nuis e)⁻¹
        (tupleEval P (fun j => efficientScore S_θ T_nuis (e j)) (X i)))
      = ∑ i, tupleEval P (candidateVecEIF S_θ T_nuis e) (X i) :=
    Finset.sum_congr rfl (fun i _ => hX i)
  simp only [hsum]

/-! ### Smooth conditional efficiency theorem -/

/-- **Native generic Taylor/Z-estimator efficiency core.**

The supplied estimator `estimator` is asymptotically efficient at `P` relative to the
tangent space `T` for the vector functional `ψ` with `ψ P = θ₀`, discharged from the
native vector strong-regularity bundle `ZEstimatorTaylorCoreNative_vec` (`hPD`, the vector
estimating equation `score_eq_vec`, the supplied matrix identity `matrix_bartlett`, and the
matrix Taylor remainder `matrix_taylor`) plus the EIF-construction inputs (`h_mem`, `h_Dψ`).

This theorem applies to arbitrary non-diagonal efficient information. It does
not carry the coordinatewise `coord_eif_eq` identification; matrix coupling is
handled in `zEstimatorVec_master_identity`.

**Proof.** `eif_from_efficientScore_vec` (from `hPD`, `h_mem`, `h_Dψ`) makes `candidateVecEIF`
a vector efficient influence function for `Dψ`; the native discharge
`mle_asympLinear_of_nativeTaylorCore_vec` makes `estimator` asymptotically linear with
that influence and centering `ψ P = θ₀`;
`estimator_semiparametricallyEfficient_of_asympLinear_eif_vec` combines them.

Reference: vdV §25.5, Theorem 25.54 (smooth vector form). -/
theorem mle_semiparametricallyEfficient_of_nativeTaylorCore_vec
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀)
    {T : Submodule ℝ ↥(L2ZeroMean P)} {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h_mem : ∀ j, candidateVecEIF S_θ T_nuis e j ∈ T)
    (h_Dψ : ∀ (j : Fin d) (g : T),
      (EuclideanSpace.proj j ∘L Dψ) g
        = ⟪candidateVecEIF S_θ T_nuis e j, (g : ↥(L2ZeroMean P))⟫_ℝ)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt_vec estimator ψ P T := by
  have hEIF := eif_from_efficientScore_vec S_θ T_nuis e T Dψ h.hPD h_mem h_Dψ
  have hAL : AsymptoticallyLinearAt_vec estimator P
      (candidateVecEIF S_θ T_nuis e) (ψ P) := by
    rw [h_ψ]; exact mle_asympLinear_of_nativeTaylorCore_vec h
  exact estimator_semiparametricallyEfficient_of_asympLinear_eif_vec hEIF hAL

end AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVecNative
