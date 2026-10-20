module
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorEmpiricalReplacement
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorModelShift
public import StatLean.AsymptoticStatistics.Asymptotics.ZEstimatorVec
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScoreVec

@[expose] public section

/-!
# Raw moving-bias expansion for native vector Z-estimators

Native finite-dimensional counterpart of the covariantly corrected form of vdV
Theorem 25.59.  With

`B_n = sqrt n * P_{thetaHat,eta} scoreHat`,

solving the estimating equation gives the positive correction `+ I^-1 B_n`.
The literal display on vdV p. 395 omits the information inverse; it is recovered
only after the separate `d = 1`, `I = 1` specialization.

The hypotheses contain no Bartlett identity, no no-bias condition, no Taylor
remainder, and no asymptotic-linearity field.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasExpansionVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimator
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorModelShift
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec

-- The random-index replacement carrier is universe-zero.
variable {Omega : Type} [MeasurableSpace Omega]

private lemma tendstoInProbZero_of_norm_le_three {Omega' : ℕ → Type*}
    [∀ n, MeasurableSpace (Omega' n)]
    {P' : ∀ n, Measure (Omega' n)} [∀ n, IsProbabilityMeasure (P' n)]
    {G A B C : ∀ n, Omega' n → EuclideanSpace ℝ (Fin d)} {c : ℝ} (hc : 0 < c)
    (hA : TendstoInProbZero P' A) (hB : TendstoInProbZero P' B) (hC : TendstoInProbZero P' C)
    (hle : ∀ n omega, ‖G n omega‖ ≤ c * (‖A n omega‖ + ‖B n omega‖ + ‖C n omega‖)) :
    TendstoInProbZero P' G := by
  intro epsilon hepsilon
  have hlevel : 0 < epsilon / (3 * c) := by positivity
  have hsum := (hA _ hlevel).add ((hB _ hlevel).add (hC _ hlevel))
  refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) (by simpa using hsum)
  refine (measureReal_mono (fun omega homega => ?_)).trans <| (measureReal_union_le
    {omega | epsilon/(3*c) ≤ ‖A n omega‖} ({omega | epsilon/(3*c) ≤ ‖B n omega‖} ∪
      {omega | epsilon/(3*c) ≤ ‖C n omega‖})).trans (add_le_add_right (measureReal_union_le
        {omega | epsilon/(3*c) ≤ ‖B n omega‖} {omega | epsilon/(3*c) ≤ ‖C n omega‖}) _)
  simp only [Set.mem_setOf_eq, Set.mem_union] at homega ⊢
  by_contra hall
  push Not at hall
  have hbound := hle n omega
  field_simp [ne_of_gt hc] at hall
  nlinarith [norm_nonneg (A n omega), norm_nonneg (B n omega), norm_nonneg (C n omega)]

private lemma Lp_coeFn_finset_sum {P : Measure Omega} {iota : Type*}
    (s : Finset iota) (f : iota → Lp ℝ 2 P) :
    (⇑(∑ k ∈ s, f k) : Omega → ℝ) =ᵐ[P] fun x => ∑ k ∈ s, (f k : Omega → ℝ) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P)] with x hx
    simpa only [Finset.sum_empty] using! hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]; filter_upwards [Lp.coeFn_add (f a) (∑ k ∈ s, f k), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

private lemma tupleEval_matrix_smul_ae {d : ℕ} {P : Measure Omega} [IsProbabilityMeasure P]
    (A : Matrix (Fin d) (Fin d) ℝ) (phi : Fin d → ↥(L2ZeroMean P)) :
    (fun x => tupleEval P (fun j => ∑ k, A j k • phi k) x) =ᵐ[P] fun x =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) A (tupleEval P phi x) := by
  classical
  have hcoord : ∀ j : Fin d, (fun x =>
      (((∑ k, A j k • phi k : ↥(L2ZeroMean P)) : Lp ℝ 2 P) x)) =ᵐ[P]
      fun x => ∑ k, A j k * (phi k : Lp ℝ 2 P) x := by
    intro j
    rw [show ((∑ k, A j k • phi k : ↥(L2ZeroMean P)) : Lp ℝ 2 P) =
      ∑ k, A j k • (phi k : Lp ℝ 2 P) by simp only
        [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul]]
    refine (Lp_coeFn_finset_sum Finset.univ (fun k => A j k • (phi k : Lp ℝ 2 P))).trans ?_
    filter_upwards [ae_all_iff.mpr fun k => Lp.coeFn_smul (A j k) (phi k : Lp ℝ 2 P)] with x hx
    exact Finset.sum_congr rfl fun k _ => by simpa only [Pi.smul_apply, smul_eq_mul] using hx k
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  exact (WithLp.equiv 2 (Fin d → ℝ)).injective (funext fun j => hx j)

private lemma norm_fin_one (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]

private lemma tupleEval_fin_one_apply {P : Measure Omega} [IsProbabilityMeasure P]
    (phi : Fin 1 → ↥(L2ZeroMean P)) (x : Omega) : tupleEval P phi x 0 = (phi 0 : Lp ℝ 2 P) x := rfl

/-- Minimal native hypotheses for the corrected raw moving-bias expansion of
vdV Theorem 25.59.

The fixed score is a tuple in `L2ZeroMean P`; `tupleEval` is its native
Euclidean-valued representative. The bundle collects the empirical replacement
and Hellinger transport conditions and contains no conclusion-bearing field.
-/
structure RawMovingBiasExpansionHyp_vec
    {d : Nat} (P : Measure Omega) [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d))
    (theta0 : EuclideanSpace Real (Fin d))
    (scoreHat : forall n,
      (Fin n -> Omega) -> Omega -> EuclideanSpace Real (Fin d))
    (score0 : Fin d -> ↥(L2ZeroMean P))
    (F : Fin d -> Set (Omega -> Real))
    (I : Matrix (Fin d) (Fin d) Real) : Prop where
  /-- Constitutive (vdV §25.8, Theorem 25.59): the estimator solves
  the ordinary native estimating equation up to `o_P(n⁻¹/²)`. -/
  score_eq : TendstoInProbZero
    (fun n : Nat => Measure.pi (fun _ : Fin n => P))
    (fun n X => (Real.sqrt n)⁻¹ • ∑ i : Fin n, scoreHat n X (X i))
  /-- Constitutive (vdV Lemma 19.24 as used in §25.8): the
  coordinatewise empirical-score replacement inputs. -/
  B0 : RandomIndexScoreReplacementHyp_vec P d scoreHat (tupleEval P score0) F
  /-- Constitutive (vdV §25.8, DQM plus condition (25.53)): native
  Hellinger/QMD transport along the moving-parameter model. -/
  hTransport : HellingerScoreTransportHypVec P M estimator theta0 scoreHat
    (tupleEval P score0)
  /-- Constitutive (vdV §25.8): the native score/path cross moment
  is the information matrix used to solve the estimating equation. -/
  hCross : qmdCrossMoment P M (tupleEval P score0) = I
  /-- Constitutive (vdV §25.8): positive-definite, hence invertible,
  information matrix. -/
  hPD : I.PosDef

/-- Rate-free native corrected form of vdV Theorem 25.59.

The residual is normalized by `1 + ‖Delta_n‖`.  Both the empirical influence
term and raw moving bias are acted on by the same matrix inverse, with positive
bias correction after the residual is rearranged. -/
theorem normalizedMovingBias_expansion_vec
    {d : Nat} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
    {theta0 : EuclideanSpace Real (Fin d)}
    {scoreHat : forall n,
      (Fin n -> Omega) -> Omega -> EuclideanSpace Real (Fin d)}
    {score0 : Fin d -> ↥(L2ZeroMean P)}
    {I : Matrix (Fin d) (Fin d) Real}
    (score_eq : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X => (Real.sqrt n)⁻¹ • ∑ i : Fin n, scoreHat n X (X i)))
    (scoreHat_integrable_truth : forall n X, Integrable (scoreHat n X) P)
    (score0_memLp : MemLp (tupleEval P score0) 2 P)
    (score0_coord_memLp : forall j,
      MemLp (fun x => (score0 j : Lp Real 2 P) x) 2 P)
    (hReplacement : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        (Real.sqrt n)⁻¹ •
            (∑ i : Fin n, (scoreHat n X (X i) - tupleEval P score0 (X i)))
          - Real.sqrt n •
              (∫ x, (scoreHat n X x - tupleEval P score0 x) ∂P)))
    (hShift : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        let delta := estimator n X - theta0
        if delta = 0 then 0 else
          ‖delta‖⁻¹ •
            (((∫ omega, scoreHat n X omega ∂(M.curve delta)) -
                ∫ omega, scoreHat n X omega ∂P) -
              Matrix.toEuclideanCLM (𝕜 := Real)
                (qmdCrossMoment P M (tupleEval P score0)) delta)))
    (hCross : qmdCrossMoment P M (tupleEval P score0) = I)
    (hPD : I.PosDef) :
    TendstoInProbZero (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        let Delta := Real.sqrt n • (estimator n X - theta0)
        (1 + ‖Delta‖)⁻¹ •
          (Delta
            - Matrix.toEuclideanCLM (𝕜 := Real) I⁻¹
                ((Real.sqrt n)⁻¹ • ∑ i : Fin n, tupleEval P score0 (X i))
            - Matrix.toEuclideanCLM (𝕜 := Real) I⁻¹
                (rawMovingBias_vec M estimator theta0 scoreHat n X))) := by
  classical
  have hmean : ∫ x, tupleEval P score0 x ∂P = 0 := by
    ext j
    rw [MeasureTheory.eval_integral_piLp]
    · have hker : (score0 j : Lp ℝ 2 P) ∈ LinearMap.ker (integralL2 P).toLinearMap := (score0 j).2
      rw [LinearMap.mem_ker] at hker
      change ⟪oneL2 P, (score0 j : Lp ℝ 2 P)⟫_ℝ = 0 at hker
      rw [MeasureTheory.L2.inner_def] at hker
      have hone : ((oneL2 P : Lp ℝ 2 P) : Omega → ℝ) =ᵐ[P] fun _ => 1 :=
        MemLp.coeFn_toLp (memLp_const (1 : ℝ))
      rw [integral_congr_ae] at hker
      · simpa [tupleEval] using hker
      · filter_upwards [hone] with x hx
        change (score0 j : Lp ℝ 2 P) x * (oneL2 P : Lp ℝ 2 P) x = _
        rw [hx, mul_one]
    · exact fun j => (score0_coord_memLp j).integrable (by norm_num)
  have hB0 := hReplacement
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) I⁻¹
  have hInv : L * Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) I = 1 := by
    rw [show L = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) I⁻¹ from rfl, ← map_mul,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit), map_one]
  have hLI : ∀ w : EuclideanSpace ℝ (Fin d), L (Matrix.toEuclideanCLM (𝕜 := ℝ) I w) = w := by
    intro w; rw [← ContinuousLinearMap.mul_apply, hInv, ContinuousLinearMap.one_apply]
  refine tendstoInProbZero_of_norm_le_three (c := ‖L‖ + 1) (by positivity)
    hB0 hShift score_eq ?_
  intro n X; rw [integral_sub (scoreHat_integrable_truth n X)
    (score0_memLp.integrable (by norm_num))]
  rw [hmean, sub_zero, Finset.sum_sub_distrib]
  simp only [rawMovingBias_vec, hCross]
  let r : ℝ := Real.sqrt n; let q : ℝ := (Real.sqrt n)⁻¹
  let delta := estimator n X - theta0; let Delta := r • delta
  let sumHat := ∑ i : Fin n, scoreHat n X (X i); let sum0 := ∑ i : Fin n, tupleEval P score0 (X i)
  let pHat := ∫ x, scoreHat n X x ∂P; let pMove := ∫ x, scoreHat n X x ∂(M.curve delta)
  let A := q • (sumHat - sum0) - r • pHat
  let N := if delta=0 then 0 else ‖delta‖⁻¹ • ((pMove-pHat)-Matrix.toEuclideanCLM (𝕜 := ℝ) I delta)
  let E := q • sumHat
  change ‖(1 + ‖Delta‖)⁻¹ • (Delta - L (q • sum0) - L (r • pMove))‖ ≤
    (‖L‖ + 1) * (‖A‖ + ‖N‖ + ‖E‖)
  have halg : Delta - L (q • sum0) - L (r • pMove) =
      L (A + (r • (pHat - pMove) +
        Matrix.toEuclideanCLM (𝕜 := ℝ) I Delta) - E) := by
    simp only [A, E, map_sub, map_add, map_smul, hLI]
    module
  rw [halg]
  have hden : 0 ≤ (1 + ‖Delta‖)⁻¹ := by positivity
  have hden1 : (1 + ‖Delta‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg Delta])
  have hM : (1 + ‖Delta‖)⁻¹ *
      ‖r • (pHat-pMove) + Matrix.toEuclideanCLM (𝕜 := ℝ) I Delta‖ ≤ ‖N‖ := by
    by_cases hd : delta = 0
    · simp [N, Delta, delta, hd, pMove, pHat, M.curve_at_zero]
    · have hr : 0 ≤ r := by simp [r]
      have habs : ‖Delta‖ = r * ‖delta‖ := by simp [Delta, norm_smul, abs_of_nonneg hr]
      have hne : ‖delta‖ ≠ 0 := norm_ne_zero_iff.mpr hd
      rw [show r • (pHat - pMove) + Matrix.toEuclideanCLM (𝕜 := ℝ) I Delta =
        (-r) • ((pMove - pHat) - Matrix.toEuclideanCLM (𝕜 := ℝ) I delta) by
          simp only [Delta, map_smul]; module]
      simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hr]
      simp only [N, if_neg hd, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg delta))]
      have hcoeff : (1 + ‖Delta‖)⁻¹ * (r * ‖delta‖) ≤ 1 := by
        rw [← habs, mul_comm]
        exact mul_inv_le_one_of_le₀ (by linarith [norm_nonneg Delta]) (by positivity)
      calc
        (1 + ‖Delta‖)⁻¹ * (r * ‖pMove - pHat -
            Matrix.toEuclideanCLM (𝕜 := ℝ) I delta‖) = ((1 + ‖Delta‖)⁻¹ *
          (r * ‖delta‖)) * (‖delta‖⁻¹ * ‖pMove - pHat -
            Matrix.toEuclideanCLM (𝕜 := ℝ) I delta‖) := by field_simp [hne]
        _ ≤ 1 * (‖delta‖⁻¹ * ‖pMove - pHat -
            Matrix.toEuclideanCLM (𝕜 := ℝ) I delta‖) := mul_le_mul_of_nonneg_right hcoeff
              (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
        _ = _ := one_mul _
  calc
    _ = (1 + ‖Delta‖)⁻¹ * ‖L
        (A + (r • (pHat - pMove) +
          Matrix.toEuclideanCLM (𝕜 := ℝ) I Delta) - E)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hden]
    _ ≤ (1 + ‖Delta‖)⁻¹ * ‖L‖ *
        (‖A‖ + ‖r • (pHat - pMove) +
          Matrix.toEuclideanCLM (𝕜 := ℝ) I Delta‖ + ‖E‖) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (norm_sub_le _ _ |>.trans (add_le_add (norm_add_le _ _) le_rfl)) (norm_nonneg L))) hden
    _ ≤ (‖L‖ + 1) * (‖A‖ + ‖N‖ + ‖E‖) := by
      calc
        _ = ‖L‖ * ((1 + ‖Delta‖)⁻¹ * ‖A‖ +
            (1 + ‖Delta‖)⁻¹ * ‖r • (pHat - pMove) +
              Matrix.toEuclideanCLM (𝕜 := ℝ) I Delta‖ +
            (1 + ‖Delta‖)⁻¹ * ‖E‖) := by ring
        _ ≤ ‖L‖ * (‖A‖ + ‖N‖ + ‖E‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg L)
          exact add_le_add (add_le_add (mul_le_of_le_one_left (norm_nonneg A) hden1) hM)
            (mul_le_of_le_one_left (norm_nonneg E) hden1)
        _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_right zero_le_one

/-- Rate-free normalized expansion for the original corrected native vdV
25.59 hypothesis bundle. -/
theorem rawMovingBias_normalized_expansion_2559_vec
    {d : Nat} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
    {theta0 : EuclideanSpace Real (Fin d)}
    {scoreHat : forall n,
      (Fin n -> Omega) -> Omega -> EuclideanSpace Real (Fin d)}
    {score0 : Fin d -> ↥(L2ZeroMean P)}
    {F : Fin d -> Set (Omega -> Real)}
    {I : Matrix (Fin d) (Fin d) Real}
    -- USER-INPUT: native estimating equation, replacement, QMD transport,
    -- cross-moment identity, and positive-definite information; vdV Theorem 25.59.
    (h : RawMovingBiasExpansionHyp_vec P M estimator theta0 scoreHat score0 F I) :
    TendstoInProbZero (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        let Delta := Real.sqrt n • (estimator n X - theta0)
        (1 + ‖Delta‖)⁻¹ •
          (Delta
            - Matrix.toEuclideanCLM (𝕜 := Real) I⁻¹
                ((Real.sqrt n)⁻¹ • ∑ i : Fin n, tupleEval P score0 (X i))
            - Matrix.toEuclideanCLM (𝕜 := Real) I⁻¹
                (rawMovingBias_vec M estimator theta0 scoreHat n X))) := by
  exact normalizedMovingBias_expansion_vec h.score_eq
    h.hTransport.scoreHat_integrable_truth h.hTransport.score0_memLp
    (fun j => (h.B0.coord_hyp j).score0_memLp)
    (randomIndex_empiricalScoreReplacement_oP_vec h.B0)
    (qmdModel_modelShift_normalized_oP h.hTransport) h.hCross h.hPD

/-- Conditional ordinary native expansion obtained from the rate-free corrected vdV 25.59 form.

The influence tuple is the matrix-coupled `I⁻¹ score0`, and the bias sequence
has the positive correction `+ I⁻¹ B_n`. Root-`n` tightness is an additional
hypothesis not supplied by the stated vdV 25.59 hypotheses, so this result is a
conditional corollary rather than the unqualified book theorem. -/
theorem expansion_of_normalizedExpansion_sqrtN_tight_vec
    {d : Nat} {P : Measure Omega} [IsProbabilityMeasure P]
    {estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
    {theta0 : EuclideanSpace Real (Fin d)}
    {score0 : Fin d -> ↥(L2ZeroMean P)}
    {I : Matrix (Fin d) (Fin d) Real}
    {B : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
    (hNormalized : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        let Delta := Real.sqrt n • (estimator n X - theta0)
        (1 + ‖Delta‖)⁻¹ •
          (Delta
            - Matrix.toEuclideanCLM (𝕜 := Real) I⁻¹
                ((Real.sqrt n)⁻¹ • ∑ i : Fin n, tupleEval P score0 (X i))
            - Matrix.toEuclideanCLM (𝕜 := Real) I⁻¹ (B n X))))
    (hDelta_tight : IsBoundedInProb
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n • (estimator n X - theta0))) :
    AsymptoticallyLinearWithBiasAt_vec estimator P
      (fun j => ∑ k, I⁻¹ j k • score0 k) theta0
      (fun n X => Matrix.toEuclideanCLM (𝕜 := Real) I⁻¹ (B n X)) := by
  classical
  let Pn := fun n : ℕ => Measure.pi (fun _ : Fin n => P)
  let Delta := fun n (X : Fin n → Omega) => Real.sqrt n • (estimator n X - theta0)
  let R := fun n (X : Fin n → Omega) =>
    Delta n X - Matrix.toEuclideanCLM (𝕜 := ℝ) I⁻¹ ((Real.sqrt n)⁻¹ •
      ∑ i : Fin n, tupleEval P score0 (X i)) - Matrix.toEuclideanCLM (𝕜 := ℝ) I⁻¹
      (B n X)
  have hnorm := hNormalized
  have hfactor : IsBoundedInProb Pn (fun n X => 1 + ‖Delta n X‖) := by
    intro epsilon hepsilon
    obtain ⟨K, hK⟩ := hDelta_tight epsilon hepsilon
    refine ⟨K + 1, fun n => ?_⟩
    rw [show {X | K+1 < ‖1+‖Delta n X‖‖} = {X | K < ‖Delta n X‖} by
      ext X; simp only [Set.mem_setOf_eq, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 1+‖Delta n X‖)]
      constructor <;> intro hx <;> linarith]
    exact hK n
  have hR : TendstoInProbZero Pn R := by
    have hp := tendstoInProbZero_of_isBoundedInProb_mul hfactor hnorm
    convert hp using 1
    funext n X
    simp only [R, Delta, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : 1+‖Real.sqrt n • (estimator n X-theta0)‖ ≠ 0), one_smul]
  intro epsilon hepsilon
  rw [← ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top (Pn n) _)]
  refine (hR epsilon hepsilon).congr' ?_
  filter_upwards [] with n
  rw [measureReal_def]
  apply congrArg ENNReal.toReal
  apply measure_congr
  have hae := tupleEval_matrix_smul_ae I⁻¹ score0
  have hall : ∀ᵐ X ∂(Pn n), ∀ i : Fin n,
      tupleEval P (fun j => ∑ k, I⁻¹ j k • score0 k) (X i) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) I⁻¹ (tupleEval P score0 (X i)) := by
    rw [ae_all_iff]
    exact fun i => hae.comp_tendsto (measurePreserving_eval
      (μ := fun _ : Fin n => P) i).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hall] with X hX
  have hsum : (∑ i : Fin n, tupleEval P (fun j => ∑ k, I⁻¹ j k • score0 k) (X i)) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) I⁻¹ (∑ i : Fin n, tupleEval P score0 (X i)) := by
    rw [Finset.sum_congr rfl (fun i _ => hX i), map_sum]
  change (epsilon ≤ ‖R n X‖) = (epsilon ≤ ‖Real.sqrt n • (estimator n X-theta0) -
    (Real.sqrt n)⁻¹ • (∑ i : Fin n, tupleEval P (fun j => ∑ k, I⁻¹ j k • score0 k) (X i)) -
    Matrix.toEuclideanCLM (𝕜 := ℝ) I⁻¹ (B n X)‖)
  simp only [R, Delta]
  rw [hsum, map_smul]

/-- Conditional ordinary native expansion obtained from the original corrected
vdV 25.59 hypotheses and a supplied root-`n` tightness conclusion. -/
theorem rawMovingBias_expansion_2559_vec_of_sqrtN_tight
    {d : Nat} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
    {theta0 : EuclideanSpace Real (Fin d)}
    {scoreHat : forall n,
      (Fin n -> Omega) -> Omega -> EuclideanSpace Real (Fin d)}
    {score0 : Fin d -> ↥(L2ZeroMean P)}
    {F : Fin d -> Set (Omega -> Real)}
    {I : Matrix (Fin d) (Fin d) Real}
    (h : RawMovingBiasExpansionHyp_vec P M estimator theta0 scoreHat score0 F I)
    (hDelta_tight : IsBoundedInProb
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n • (estimator n X - theta0))) :
    AsymptoticallyLinearWithBiasAt_vec estimator P
      (fun j => ∑ k, I⁻¹ j k • score0 k) theta0
      (fun n X => Matrix.toEuclideanCLM (𝕜 := Real) I⁻¹
        (rawMovingBias_vec M estimator theta0 scoreHat n X)) := by
  exact expansion_of_normalizedExpansion_sqrtN_tight_vec
    (rawMovingBias_normalized_expansion_2559_vec h) hDelta_tight

/-- `d = 1` bridge between the native and scalar biased-linearity predicates.

The scalar `QMDPath` and native `QMDModel` encode distinct model data, so this
statement identifies only their biased-linearity predicates. Specializing
`I = 1` gives the printed vdV p. 395 `+ B_n` normalization. -/
theorem asymptoticallyLinearWithBiasAt_vec_fin_one_iff
    {P : Measure Omega} [IsProbabilityMeasure P]
    {estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin 1)}
    {score0 : Fin 1 -> ↥(L2ZeroMean P)}
    {theta0 : EuclideanSpace Real (Fin 1)}
    {bias : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin 1)} :
    AsymptoticallyLinearWithBiasAt_vec estimator P score0 theta0 bias ↔
      AsymptoticallyLinearWithBiasAt
        (fun n X => estimator n X 0) P (score0 0) (theta0 0)
        (fun n X => bias n X 0) := by
  simp only [AsymptoticallyLinearWithBiasAt_vec, AsymptoticallyLinearWithBiasAt,
    norm_fin_one, PiLp.smul_apply, PiLp.sub_apply, WithLp.ofLp_sum,
    Finset.sum_apply, tupleEval_fin_one_apply, smul_eq_mul]

/-- For `d = 1`, the native and scalar asymptotic-linearity predicates are
equivalent without additional mathematical hypotheses. -/
theorem asymptoticallyLinearAt_vec_fin_one_iff
    {P : Measure Omega} [IsProbabilityMeasure P]
    {estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin 1)}
    {score0 : Fin 1 -> ↥(L2ZeroMean P)}
    {theta0 : EuclideanSpace Real (Fin 1)} :
    AsymptoticallyLinearAt_vec estimator P score0 theta0 ↔
      AsymptoticallyLinearAt
        (fun n X => estimator n X 0) P (score0 0) (theta0 0) := by
  simp only [AsymptoticallyLinearAt_vec, AsymptoticallyLinearAt,
    norm_fin_one, PiLp.smul_apply, PiLp.sub_apply, WithLp.ofLp_sum,
    Finset.sum_apply, tupleEval_fin_one_apply, smul_eq_mul]

/-- Root-`n` tightness bootstrap from a normalized native moving-bias
expansion and the normalized no-bias condition of vdV Theorem 25.54.

The normalized no-bias condition (25.52), together with the corrected native
25.59 expansion, rules out escape of
`Delta_n = sqrt n • (thetaHat_n - theta0)`.  The finite-dimensional fixed-score
empirical sum supplies the `O_P(1)` coordinate, while `hEstimator_meas` handles
the finitely many pre-asymptotic estimator laws. -/
theorem sqrtN_tight_of_normalizedExpansion_vec
    {d : Nat} {P : Measure Omega} [IsProbabilityMeasure P]
    {estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
    {theta0 : EuclideanSpace Real (Fin d)}
    {score0 : Fin d -> ↥(L2ZeroMean P)}
    {I : Matrix (Fin d) (Fin d) Real}
    {B : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
    -- square-integrable representatives of the fixed score tuple.
    (score0_memLp : forall j,
      MemLp (fun x => (score0 j : Lp Real 2 P) x) 2 P)
    -- Finite-prefix tightness for the all-`n` `O_P(1)` predicate used here.
    (hEstimator_meas : forall n, Measurable (estimator n))
    -- DERIVED INPUT: the normalized moving-bias/Z expansion.
    (hNormalized : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        let Delta := Real.sqrt n • (estimator n X - theta0)
        (1 + ‖Delta‖)⁻¹ •
          (Delta
            - Matrix.toEuclideanCLM (𝕜 := Real) I⁻¹
                ((Real.sqrt n)⁻¹ • ∑ i : Fin n, tupleEval P score0 (X i))
            - Matrix.toEuclideanCLM (𝕜 := Real) I⁻¹ (B n X))))
    -- vdV equation (25.75), in normalized moving-bias form.
    (h52 : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        (1 + ‖Real.sqrt n • (estimator n X - theta0)‖)⁻¹ •
          B n X)) :
    IsBoundedInProb
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n • (estimator n X - theta0)) := by
  classical
  let Pn := fun n : ℕ => Measure.pi (fun _ : Fin n => P)
  let Delta := fun n (X : Fin n → Omega) => Real.sqrt n • (estimator n X - theta0)
  let S := fun n (X : Fin n → Omega) => (Real.sqrt n)⁻¹ •
    ∑ i : Fin n, tupleEval P score0 (X i)
  have hScoord : ∀ j : Fin d, IsBoundedInProb Pn (fun n X => S n X j) := by
    intro j epsilon hepsilon
    let g : Omega → ℝ := fun x => (score0 j : Lp ℝ 2 P) x
    let V := ProbabilityTheory.variance g P
    have hV : 0 ≤ V := ENNReal.toReal_nonneg
    let K := Real.sqrt (V / epsilon + 1)
    have hK : 0 < K := Real.sqrt_pos.mpr (by positivity)
    have hVK : V / K ^ 2 ≤ epsilon := by
      rw [show K ^ 2 = V / epsilon + 1 by exact Real.sq_sqrt (by positivity)]
      by_cases hV0 : V = 0
      · simp [hV0, hepsilon.le]
      · have hVp : 0 < V := lt_of_le_of_ne hV (Ne.symm hV0)
        calc
          V / (V / epsilon + 1) ≤ V / (V / epsilon) :=
            div_le_div_of_nonneg_left hVp.le (div_pos hVp hepsilon) (by linarith)
          _ = epsilon := by field_simp
    refine ⟨K, fun n => ?_⟩
    by_cases hn : n = 0
    · subst n
      have hset : {X : Fin 0 → Omega | K < ‖S 0 X j‖} = ∅ := by
        ext X
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, S,
          Nat.cast_zero, Real.sqrt_zero, inv_zero, Fin.sum_univ_zero, zero_smul,
          PiLp.zero_apply, norm_zero]
        exact not_lt_of_ge hK.le
      rw [hset, measureReal_empty]
      exact hepsilon.le
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hgmem : MemLp g 2 P := by
      simpa only [g] using score0_memLp j
    have hgi : ∀ i : Fin n, MemLp (fun X : Fin n → Omega => g (X i)) 2 (Pn n) :=
      fun i => hgmem.comp_measurePreserving
        (measurePreserving_eval (μ := fun _ : Fin n => P) i)
    have hS_eq : (fun X : Fin n → Omega => S n X j) =
        fun X => (Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i) := by
      funext X
      simp only [S, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
      rfl
    have hSmem : MemLp (fun X : Fin n → Omega => S n X j) 2 (Pn n) := by
      rw [hS_eq]
      exact (memLp_finset_sum Finset.univ (fun i _ => hgi i)).const_mul _
    have hmean : ∫ x, g x ∂P = 0 := by
      have hker : (score0 j : Lp ℝ 2 P) ∈
          LinearMap.ker (integralL2 P).toLinearMap := (score0 j).2
      rw [LinearMap.mem_ker] at hker
      change inner ℝ (oneL2 P) (score0 j : Lp ℝ 2 P) = 0 at hker
      rw [MeasureTheory.L2.inner_def] at hker
      have hone : ((oneL2 P : Lp ℝ 2 P) : Omega → ℝ) =ᵐ[P] fun _ => 1 :=
        MemLp.coeFn_toLp (memLp_const (1 : ℝ))
      rw [integral_congr_ae] at hker
      · exact hker
      · filter_upwards [hone] with x hx
        change (score0 j : Lp ℝ 2 P) x * (oneL2 P : Lp ℝ 2 P) x = _
        rw [hx, mul_one]
    have hSint : ∫ X, S n X j ∂(Pn n) = 0 := by
      have heach : ∀ i : Fin n, ∫ X : Fin n → Omega, g (X i) ∂(Pn n) = 0 := by
        intro i
        rw [show Pn n = Measure.pi (fun _ : Fin n => P) from rfl,
          integral_comp_eval (i := i) (μ := fun _ : Fin n => P)
          hgmem.aestronglyMeasurable]
        exact hmean
      rw [hS_eq]
      rw [integral_const_mul, integral_finset_sum _
        (fun i _ => (hgi i).integrable (by norm_num))]
      simp [heach]
    have hSvar : ProbabilityTheory.variance (fun X : Fin n → Omega => S n X j) (Pn n) = V := by
      rw [hS_eq]
      rw [ProbabilityTheory.variance_const_mul]
      have hp := ProbabilityTheory.variance_sum_pi
        (μ := fun _ : Fin n => P) (X := fun _ : Fin n => g)
        (fun _ => hgmem)
      have heq : (∑ i : Fin n, fun X : Fin n → Omega => g (X i)) =
          fun X => ∑ i : Fin n, g (X i) := by funext X; simp [Finset.sum_apply]
      rw [heq] at hp
      rw [hp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hsqrt : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnR.le
      rw [show (Real.sqrt n)⁻¹ ^ 2 = (n : ℝ)⁻¹ by rw [inv_pow, sq, hsqrt]]
      field_simp
      rfl
    have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hSmem hK
    rw [hSint, hSvar] at hcheb
    simp only [sub_zero] at hcheb
    rw [measureReal_def]
    calc
      ((Pn n) {X | K < ‖S n X j‖}).toReal ≤ (ENNReal.ofReal epsilon).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono (fun X hX => by
          simpa [Real.norm_eq_abs] using le_of_lt hX)).trans
            (hcheb.trans (ENNReal.ofReal_le_ofReal hVK)))
      _ = epsilon := ENNReal.toReal_ofReal hepsilon.le
  have hS : IsBoundedInProb Pn S := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · intro epsilon hepsilon
      refine ⟨0, fun n => ?_⟩
      have hz : ∀ X : Fin n → Omega, S n X = 0 := fun _ => Subsingleton.elim _ _
      simp [hz, hepsilon.le]
    · intro epsilon hepsilon
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      have hlevel : 0 < epsilon / d := div_pos hepsilon hdR
      let K : Fin d -> Real := fun j =>
        Classical.choose (hScoord j (epsilon / d) hlevel)
      have hK : forall j : Fin d, forall n,
          (Pn n).real {X | K j < ‖S n X j‖} <= epsilon / d := fun j => by
        simpa only [K] using
          Classical.choose_spec (hScoord j (epsilon / d) hlevel)
      let K' := ∑ j : Fin d, max (K j) 0
      refine ⟨K', fun n => ?_⟩
      calc
        (Pn n).real {X | K' < ‖S n X‖} ≤
            (Pn n).real (⋃ j : Fin d, {X | max (K j) 0 < ‖S n X j‖}) := by
          apply measureReal_mono (h₂ := measure_ne_top (Pn n) _)
          intro X hX
          simp only [Set.mem_iUnion, Set.mem_setOf_eq]
          by_contra hall
          push Not at hall
          have hnorm : ‖S n X‖ ≤ K' := by
            calc
              ‖S n X‖ = ‖∑ j : Fin d, PiLp.single (β := fun _ : Fin d => ℝ) 2 j (S n X j)‖ := by
                congr 1; ext j; simp
              _ ≤ ∑ j : Fin d, ‖PiLp.single (β := fun _ : Fin d => ℝ) 2 j (S n X j)‖ :=
                norm_sum_le _ _
              _ = ∑ j : Fin d, ‖S n X j‖ := by simp
              _ ≤ K' := Finset.sum_le_sum fun j _ => hall j
          exact (not_lt_of_ge hnorm) hX
        _ ≤ ∑ j : Fin d, (Pn n).real {X | max (K j) 0 < ‖S n X j‖} :=
          measureReal_iUnion_fintype_le _
        _ ≤ ∑ _j : Fin d, epsilon / d := Finset.sum_le_sum fun j _ =>
          (measureReal_mono (fun X hX => lt_of_le_of_lt (le_max_left (K j) 0) hX)).trans
            (hK j n)
        _ = epsilon := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) I⁻¹
  let T := fun n (X : Fin n → Omega) => L (S n X)
  have hT : IsBoundedInProb Pn T := by
    intro epsilon hepsilon
    obtain ⟨K, hK⟩ := hS epsilon hepsilon
    refine ⟨‖L‖ * max K 0, fun n => (measureReal_mono (fun X hX => ?_)).trans (hK n)⟩
    simp only [Set.mem_setOf_eq, T] at hX ⊢
    by_contra hsmall
    have hSn : ‖S n X‖ ≤ max K 0 := (not_lt.mp hsmall).trans (le_max_left K 0)
    exact (not_lt_of_ge ((L.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hSn (norm_nonneg L)))) hX
  let rho := fun n (X : Fin n → Omega) => (1 + ‖Delta n X‖)⁻¹
  let R := fun n (X : Fin n → Omega) =>
    rho n X • (Delta n X - T n X - L (B n X))
  have hR : TendstoInProbZero Pn R := by
    simpa [Pn, Delta, S, T, L, rho, R] using hNormalized
  have hzero : TendstoInProbZero Pn (fun n X => (0 : EuclideanSpace ℝ (Fin d))) := by
    intro a ha
    simpa only [norm_zero, not_le.mpr ha, Set.setOf_false, measureReal_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hE : TendstoInProbZero Pn
      (fun n X => R n X + L (rho n X • B n X)) := by
    refine tendstoInProbZero_of_norm_le_three (c := ‖L‖ + 1) (by positivity)
      hR (by simpa [Pn, Delta, rho] using h52) hzero ?_
    intro n X
    have hL := L.le_opNorm (rho n X • B n X)
    calc
      ‖R n X + L (rho n X • B n X)‖ ≤
          ‖R n X‖ + ‖L (rho n X • B n X)‖ := norm_add_le _ _
      _ ≤ (‖L‖ + 1) *
          (‖R n X‖ + ‖rho n X • B n X‖ + ‖(0 : EuclideanSpace ℝ (Fin d))‖) := by
        simp only [norm_zero, add_zero]
        nlinarith [hL, norm_nonneg (R n X), norm_nonneg (rho n X • B n X), norm_nonneg L]
  intro epsilon hepsilon
  obtain ⟨K, hK⟩ := hT (epsilon / 2) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp <|
    (hE (1 / 2) (by norm_num)).eventually (Iio_mem_nhds (by positivity : 0 < epsilon / 2))
  let Dpre := fun n (X : Fin n → Omega) => if n < N then Delta n X else 0
  have hDpre0 : TendstoInProbZero Pn Dpre := by
    intro a ha
    apply (tendsto_congr' (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)).2 tendsto_const_nhds
    have hset : {X : Fin n → Omega | a ≤ ‖Dpre n X‖} = ∅ := by
      ext X; simp [Dpre, not_lt.mpr hn, not_le.mpr ha]
    rw [hset, measureReal_empty]
  have hDpre_meas : ∀ n, Measurable (Dpre n) := by
    intro n
    by_cases hn : n < N
    · simpa [Dpre, hn, Delta] using!
        ((hEstimator_meas n).sub_const theta0).const_smul (Real.sqrt n)
    · simp [Dpre, hn]
  obtain ⟨M0, hM0⟩ := hDpre0.isBoundedInProb hDpre_meas epsilon hepsilon
  refine ⟨max M0 (2 * max K 0 + 1), fun n => ?_⟩
  by_cases hn : n < N
  · refine (measureReal_mono (fun X hX => ?_)).trans (hM0 n)
    simp only [Set.mem_setOf_eq] at hX ⊢
    change M0 < ‖if n < N then Delta n X else 0‖
    rw [if_pos hn]
    exact lt_of_le_of_lt (le_max_left M0 _) hX
  have hsub : {X : Fin n → Omega | max M0 (2 * max K 0 + 1) < ‖Delta n X‖} ⊆
      {X | K < ‖T n X‖} ∪ {X | 1 / 2 ≤ ‖R n X + L (rho n X • B n X)‖} := by
    intro X hX
    by_cases hTX : K < ‖T n X‖
    · exact Or.inl hTX
    · refine Or.inr ?_
      simp only [Set.mem_setOf_eq]
      rw [show R n X + L (rho n X • B n X) = rho n X • (Delta n X - T n X) by
        simp only [R, map_smul]; module, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ rho n X)]
      have htri : ‖Delta n X‖ - ‖T n X‖ ≤ ‖Delta n X - T n X‖ := by
        have ht := norm_add_le (Delta n X - T n X) (T n X)
        rw [sub_add_cancel] at ht
        linarith
      have hlarge : 2 * max K 0 + 1 < ‖Delta n X‖ :=
        lt_of_le_of_lt (le_max_right _ _) hX
      have hsmall : ‖T n X‖ ≤ max K 0 := (not_lt.mp hTX).trans (le_max_left K 0)
      simp only [rho]
      have hden : 0 < 1 + ‖Delta n X‖ := by positivity
      rw [show (1 / 2 : ℝ) = (1 + ‖Delta n X‖)⁻¹ * ((1 + ‖Delta n X‖) / 2) by
        field_simp]
      exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hden.le)
  calc
    (Pn n).real {X | max M0 (2 * max K 0 + 1) < ‖Delta n X‖} ≤
        (Pn n).real ({X | K < ‖T n X‖} ∪
          {X | 1 / 2 ≤ ‖R n X + L (rho n X • B n X)‖}) := measureReal_mono hsub
    _ ≤ (Pn n).real {X | K < ‖T n X‖} +
          (Pn n).real {X | 1 / 2 ≤ ‖R n X + L (rho n X • B n X)‖} :=
      measureReal_union_le _ _
    _ ≤ epsilon := by linarith [hK n, hN n (not_lt.mp hn)]

/-- Root-`n` tightness for the original corrected native vdV 25.54 bundle. -/
theorem rawMovingBias_sqrtN_tight_2554_vec
    {d : Nat} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
    {theta0 : EuclideanSpace Real (Fin d)}
    {scoreHat : forall n,
      (Fin n -> Omega) -> Omega -> EuclideanSpace Real (Fin d)}
    {score0 : Fin d -> ↥(L2ZeroMean P)}
    {F : Fin d -> Set (Omega -> Real)}
    {I : Matrix (Fin d) (Fin d) Real}
    -- USER-INPUT: native estimating equation, replacement, QMD transport,
    -- cross-moment identity, and positive-definite information; vdV Theorem 25.54.
    (h : RawMovingBiasExpansionHyp_vec P M estimator theta0 scoreHat score0 F I)
    -- LEAN-ONLY: estimator measurability for the finite-prefix tightness step.
    (hEstimator_meas : forall n, Measurable (estimator n))
    -- USER-INPUT: vector equation (25.52), in rate-free normalized form;
    -- vdV Theorem 25.54.
    (h52 : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        (1 + ‖Real.sqrt n • (estimator n X - theta0)‖)⁻¹ •
          rawMovingBias_vec M estimator theta0 scoreHat n X)) :
    IsBoundedInProb
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n • (estimator n X - theta0)) := by
  exact sqrtN_tight_of_normalizedExpansion_vec
    (fun j => (h.B0.coord_hyp j).score0_memLp) hEstimator_meas
    (rawMovingBias_normalized_expansion_2559_vec h) h52

/-- Native vector vdV Theorem 25.54 assembled from its raw no-bias condition.

The normalized equation (25.52) first bootstraps root-`n` tightness, then the
same tightness removes the self-normalizer and yields vanishing raw moving
bias.  The corrected vector 25.59 expansion consequently collapses to the
matrix-coupled asymptotic-linear influence tuple `I⁻¹ score0`. -/
theorem asympLinear_of_normalizedExpansion_2554_vec
    {d : Nat} {P : Measure Omega} [IsProbabilityMeasure P]
    {estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
    {theta0 : EuclideanSpace Real (Fin d)}
    {score0 : Fin d -> ↥(L2ZeroMean P)}
    {I : Matrix (Fin d) (Fin d) Real}
    {B : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
    (score0_memLp : forall j,
      MemLp (fun x => (score0 j : Lp Real 2 P) x) 2 P)
    -- Finite-prefix tightness for the all-`n` `O_P(1)` predicate used here.
    (hEstimator_meas : forall n, Measurable (estimator n))
    (hNormalized : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        let Delta := Real.sqrt n • (estimator n X - theta0)
        (1 + ‖Delta‖)⁻¹ •
          (Delta
            - Matrix.toEuclideanCLM (𝕜 := Real) I⁻¹
                ((Real.sqrt n)⁻¹ • ∑ i : Fin n, tupleEval P score0 (X i))
            - Matrix.toEuclideanCLM (𝕜 := Real) I⁻¹ (B n X))))
    -- vdV equation (25.75), in normalized moving-bias form.
    (h52 : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        (1 + ‖Real.sqrt n • (estimator n X - theta0)‖)⁻¹ •
          B n X)) :
    AsymptoticallyLinearAt_vec estimator P
      (fun j => ∑ k, I⁻¹ j k • score0 k) theta0 := by
  let Pn := fun n : ℕ => Measure.pi (fun _ : Fin n => P)
  let Delta := fun n (X : Fin n → Omega) => Real.sqrt n • (estimator n X - theta0)
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) I⁻¹
  have hDelta := sqrtN_tight_of_normalizedExpansion_vec
    score0_memLp hEstimator_meas hNormalized h52
  have hfactor : IsBoundedInProb Pn (fun n X => 1 + ‖Delta n X‖) := by
    intro epsilon hepsilon
    obtain ⟨M0, hM0⟩ := hDelta epsilon hepsilon
    refine ⟨M0 + 1, fun n => ?_⟩
    rw [show {X | M0 + 1 < ‖1 + ‖Delta n X‖‖} = {X | M0 < ‖Delta n X‖} by
      ext X
      simp only [Set.mem_setOf_eq, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 1 + ‖Delta n X‖)]
      constructor <;> intro hX <;> linarith]
    exact hM0 n
  have hB0 : TendstoInProbZero Pn B := by
    have hp := tendstoInProbZero_of_isBoundedInProb_mul hfactor h52
    convert hp using 1
    funext n X
    change B n X = (1 + ‖Delta n X‖) • ((1 + ‖Delta n X‖)⁻¹ • B n X)
    rw [smul_smul, mul_inv_cancel₀ (by positivity : 1 + ‖Delta n X‖ ≠ 0), one_smul]
  have hzero : TendstoInProbZero Pn (fun n X => (0 : EuclideanSpace ℝ (Fin d))) := by
    intro a ha
    simpa only [norm_zero, not_le.mpr ha, Set.setOf_false, measureReal_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hBias : TendstoInProbZero Pn (fun n X => L (B n X)) := by
    refine tendstoInProbZero_of_norm_le_three (c := ‖L‖ + 1) (by positivity)
      hB0 hzero hzero ?_
    intro n X
    have hL := L.le_opNorm (B n X)
    simp only [norm_zero, add_zero]
    nlinarith [hL, norm_nonneg (B n X), norm_nonneg L]
  have hALB := expansion_of_normalizedExpansion_sqrtN_tight_vec hNormalized hDelta
  let A := fun n (X : Fin n → Omega) => Delta n X - (Real.sqrt n)⁻¹ •
    ∑ i : Fin n, tupleEval P (fun j => ∑ k, I⁻¹ j k • score0 k) (X i)
  have hR0 : TendstoInProbZero Pn (fun n X => A n X - L (B n X)) := by
    intro a ha
    apply (ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top (Pn n) _)).mpr
    simpa [Pn, Delta, L, A] using hALB a ha
  have hA : TendstoInProbZero Pn A := by
    refine tendstoInProbZero_of_norm_le_three (c := 1) zero_lt_one hR0 hBias hzero ?_
    intro n X
    have ht := norm_add_le (A n X - L (B n X)) (L (B n X))
    rw [sub_add_cancel] at ht
    simpa only [one_mul, norm_zero, add_zero] using ht
  intro a ha
  rw [← ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top (Pn n) _)]
  simpa [Pn, Delta, A] using! hA a ha

/-- Native vector vdV Theorem 25.54 for the original corrected moving-bias
bundle. -/
theorem rawMovingBias_asympLinear_2554_vec
    {d : Nat} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
    {theta0 : EuclideanSpace Real (Fin d)}
    {scoreHat : forall n,
      (Fin n -> Omega) -> Omega -> EuclideanSpace Real (Fin d)}
    {score0 : Fin d -> ↥(L2ZeroMean P)}
    {F : Fin d -> Set (Omega -> Real)}
    {I : Matrix (Fin d) (Fin d) Real}
    -- USER-INPUT: native estimating equation, replacement, QMD transport,
    -- cross-moment identity, and positive-definite information; vdV Theorem 25.54.
    (h : RawMovingBiasExpansionHyp_vec P M estimator theta0 scoreHat score0 F I)
    -- LEAN-ONLY: estimator measurability for the finite-prefix tightness step.
    (hEstimator_meas : forall n, Measurable (estimator n))
    -- USER-INPUT: vector equation (25.52), in rate-free normalized form;
    -- vdV Theorem 25.54.
    (h52 : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        (1 + ‖Real.sqrt n • (estimator n X - theta0)‖)⁻¹ •
          rawMovingBias_vec M estimator theta0 scoreHat n X)) :
    AsymptoticallyLinearAt_vec estimator P
      (fun j => ∑ k, I⁻¹ j k • score0 k) theta0 := by
  exact asympLinear_of_normalizedExpansion_2554_vec
    (fun j => (h.B0.coord_hyp j).score0_memLp) hEstimator_meas
    (rawMovingBias_normalized_expansion_2559_vec h) h52

namespace RawMovingBiasExpansionHyp_vec

/-- Build the native raw moving-bias bundle from efficient-score coordinates
and a native QMD model. The cross-moment matrix is derived from `hScore` and
efficient-score orthogonality rather than supplied as an input. -/
theorem ofEfficientScores
    {d : Nat} {P : Measure Omega} [IsProbabilityMeasure P]
    {Theta : Type*} [NormedAddCommGroup Theta] [InnerProductSpace Real Theta]
    [CompleteSpace Theta]
    (S_theta : OrdinaryScore P Theta) (T_nuis : NuisanceTangentSpace P)
    -- Mathlib's orthogonal projection API requires this instance.
    [proj : T_nuis.HasOrthogonalProjection] (e : Fin d -> Theta)
    {M : QMDModel (Omega := Omega) P d}
    {estimator : forall n,
      (Fin n -> Omega) -> EuclideanSpace Real (Fin d)}
    {theta0 : EuclideanSpace Real (Fin d)}
    {scoreHat : forall n,
      (Fin n -> Omega) -> Omega -> EuclideanSpace Real (Fin d)}
    {F : Fin d -> Set (Omega -> Real)}
    -- vdV §25.8 native estimating equation at the fitted score.
    (score_eq : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X => (Real.sqrt n)⁻¹ • ∑ i : Fin n, scoreHat n X (X i)))
    -- vdV Lemma 19.24 coordinatewise random-index replacement primitives.
    (B0 : RandomIndexScoreReplacementHyp_vec P d scoreHat
      (tupleEval P (fun k => @efficientScore Omega _ P _ Theta _ _ _
        S_theta T_nuis proj (e k))) F)
    -- vdV §25.8 DQM plus condition (25.53) native moving-law score
    -- transport primitives.
    (hTransport : HellingerScoreTransportHypVec P M estimator theta0 scoreHat
      (tupleEval P (fun k => @efficientScore Omega _ P _ Theta _ _ _
        S_theta T_nuis proj (e k))))
    -- each native QMD score coordinate realizes its ordinary-score direction.
    (hScore : forall k,
      (fun omega => M.score omega k) =ᵐ[P]
        fun omega => ((S_theta (e k) : Lp Real 2 P) : Omega -> Real) omega)
    -- vdV Theorem 25.54 nonsingularity of the efficient information matrix.
    (hPD : (@efficientInformationMatrix Omega _ P _ Theta _ _ _ d
      S_theta T_nuis proj e).PosDef) :
    RawMovingBiasExpansionHyp_vec P M estimator theta0 scoreHat
      (fun k => @efficientScore Omega _ P _ Theta _ _ _
        S_theta T_nuis proj (e k)) F
      (@efficientInformationMatrix Omega _ P _ Theta _ _ _ d
        S_theta T_nuis proj e) := by
  refine ⟨score_eq, B0, hTransport, ?_, hPD⟩
  ext j k
  change (∫ omega,
      (((@efficientScore Omega _ P _ Theta _ _ _
        S_theta T_nuis proj (e j) : ↥(L2ZeroMean P)) :
          Lp Real 2 P) : Omega → Real) omega * M.score omega k ∂P) = _
  calc
    _ = ∫ omega,
        (((@efficientScore Omega _ P _ Theta _ _ _
          S_theta T_nuis proj (e j) : ↥(L2ZeroMean P)) :
            Lp Real 2 P) : Omega → Real) omega *
          (((S_theta (e k) : ↥(L2ZeroMean P)) :
            Lp Real 2 P) : Omega → Real) omega ∂P := by
      apply integral_congr_ae
      filter_upwards [hScore k] with omega homega
      rw [homega]
    _ = inner Real
          ((@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj (e j) :
            ↥(L2ZeroMean P)) : Lp Real 2 P)
          ((S_theta (e k) : ↥(L2ZeroMean P)) : Lp Real 2 P) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega => mul_comm _ _
    _ = inner Real
          ((@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj (e j) :
            ↥(L2ZeroMean P)) : Lp Real 2 P)
          ((@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj (e k) :
            ↥(L2ZeroMean P)) : Lp Real 2 P) :=
      @efficientScore_inner_ordinary_eq_self Omega _ P _ Theta _ _ _
        S_theta T_nuis proj (e j) (e k)
    _ = @efficientInformationMatrix Omega _ P _ Theta _ _ _ d
          S_theta T_nuis proj e j k :=
      (@efficientInformationMatrix_apply Omega _ P _ Theta _ _ _ d
        S_theta T_nuis proj e j k).symm

end RawMovingBiasExpansionHyp_vec

end AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasExpansionVec
