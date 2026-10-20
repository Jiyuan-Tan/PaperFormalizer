module
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorEmpiricalReplacement
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorModelShift
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScore

@[expose] public section

/-!
# Raw moving-bias expansion for scalar Z-estimators

This file proves the covariantly corrected scalar form of vdV
Theorem 25.59.  The raw moving bias is

`B_n = sqrt n * P_{thetaHat,eta} scoreHat`.

Solving the estimating equation gives the positive correction
`+ I⁻¹ B_n`.  The literal display on vdV p. 395 writes `+ B_n`; the final
corollary below records that printed normalization only under `I = 1`.

This formulation uses the positive-sign correction and assumes no
`submodel_at_zero` field.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasExpansion

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimator
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorModelShift
open AsymptoticStatistics.StrictModel.EfficientScore

-- `RandomIndexScoreReplacementHyp` has a universe-zero carrier.
variable {Omega : Type} [MeasurableSpace Omega]

private lemma tendstoInProbZero_of_abs_le_three
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P' : ∀ n, Measure (Omega' n)} [∀ n, IsProbabilityMeasure (P' n)]
    {Z A B C : ∀ n, Omega' n → ℝ} {c : ℝ} (hc : 0 < c)
    (hA : TendstoInProbZero P' A) (hB : TendstoInProbZero P' B)
    (hC : TendstoInProbZero P' C)
    (hle : ∀ n omega, |Z n omega| ≤ c * (|A n omega| + |B n omega| + |C n omega|)) :
    TendstoInProbZero P' Z := by
  intro epsilon hepsilon
  have hlevel : 0 < epsilon / (3 * c) := by positivity
  have hsum := (hA _ hlevel).add ((hB _ hlevel).add (hC _ hlevel))
  refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) (by simpa using hsum)
  refine (measureReal_mono (fun omega homega => ?_)).trans <|
    (measureReal_union_le
      {omega | epsilon / (3 * c) ≤ ‖A n omega‖}
      ({omega | epsilon / (3 * c) ≤ ‖B n omega‖} ∪
        {omega | epsilon / (3 * c) ≤ ‖C n omega‖})).trans
      (add_le_add_right (measureReal_union_le
        {omega | epsilon / (3 * c) ≤ ‖B n omega‖}
        {omega | epsilon / (3 * c) ≤ ‖C n omega‖}) _)
  simp only [Set.mem_setOf_eq, Set.mem_union] at homega ⊢
  by_contra hall
  push Not at hall
  have hbound := hle n omega
  rw [Real.norm_eq_abs] at homega
  have hc0 : c ≠ 0 := ne_of_gt hc
  field_simp [hc0] at hall
  simp only [Real.norm_eq_abs] at hall
  have hsumlt : c * (|A n omega| + |B n omega| + |C n omega|) < epsilon := by
    nlinarith [abs_nonneg (A n omega), abs_nonneg (B n omega), abs_nonneg (C n omega)]
  exact (not_lt_of_ge (homega.trans hbound)) hsumlt
private lemma rawMovingBias_algebra (I q r delta sumHat sum0 pHat pMove : ℝ)
    (hI : I ≠ 0) :
    I⁻¹ * ((q * (sumHat - sum0) - r * pHat) +
        (r * (pHat - pMove) + delta * I) - q * sumHat) =
      delta - I⁻¹ * (q * sum0) - I⁻¹ * (r * pMove) := by
  field_simp [hI]
  ring
/-- Minimal hypotheses for the corrected raw moving-bias expansion
of vdV Theorem 25.59.

The fixed score is an element of `L2ZeroMean P`, so its measurability,
square-integrability, and centering are part of the existing score concept.
The two analytic bundles are reused without copying their fields.  This
bundle contains neither a Bartlett/no-bias condition, an asymptotic-linear
conclusion, nor a Taylor conclusion.
-/
structure RawMovingBiasExpansionHyp
    (P : Measure Omega) [IsProbabilityMeasure P]
    (gamma : QMDPath P)
    (estimator : forall n, (Fin n -> Omega) -> Real) (theta0 : Real)
    (scoreHat : forall n, (Fin n -> Omega) -> Omega -> Real)
    (score0 : ↥(L2ZeroMean P)) (F : Set (Omega -> Real)) (I : Real) : Prop where
  /-- Constitutive (vdV §25.8, Theorem 25.59): the estimator solves
  the ordinary empirical estimating equation up to `o_P(n⁻¹/²)`. -/
  score_eq : TendstoInProbZero
    (fun n : Nat => Measure.pi (fun _ : Fin n => P))
    (fun n X => (Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreHat n X (X i))
  /-- Constitutive (vdV Lemma 19.24 as used in §25.8): random-index
  empirical-score replacement, including its measurability and
  integrability conditions. -/
  B0 : RandomIndexScoreReplacementHyp P scoreHat
    (fun x => (score0 : Lp Real 2 P) x) F
  /-- Constitutive (vdV §25.8, DQM plus condition (25.53)): Hellinger/QMD
  transport of the estimated score along the moving-parameter path. -/
  hTransport : HellingerScoreTransportHyp P gamma estimator theta0 scoreHat
    (fun x => (score0 : Lp Real 2 P) x)
  /-- Constitutive (vdV §25.8): the score/path cross moment is the
  scalar information used to solve the estimating equation. -/
  hCross :
    (∫ x, (score0 : Lp Real 2 P) x * (gamma.score : Omega -> Real) x ∂P) = I
  /-- Constitutive (vdV §25.8): nondegenerate scalar information. -/
  hI : 0 < I

/-- Rate-free corrected form of vdV Theorem 25.59.

The residual is normalized by `1 + |Δ_n|`, where
`Δ_n = sqrt n * (thetaHat_n - theta0)`.  The sign of the raw moving-bias
term is positive after solving the estimating equation.

Proof idea: `h.score_eq` supplies the ordinary estimating-equation residual;
`randomIndex_empiricalScoreReplacement_oP h.B0` replaces
the random empirical score; `qmdPath_modelShift_normalized_oP
h.hTransport` supplies the rate-free moving-model term;
`h.hCross` identifies its coefficient; `h.hI`
licenses division by `I`; and the `L2ZeroMean` type of `score0` removes its
truth-law mean.
-/
theorem rawMovingBias_normalized_expansion_2559
    {P : Measure Omega} [IsProbabilityMeasure P]
    {gamma : QMDPath P}
    {estimator : forall n, (Fin n -> Omega) -> Real} {theta0 : Real}
    {scoreHat : forall n, (Fin n -> Omega) -> Omega -> Real}
    {score0 : ↥(L2ZeroMean P)} {F : Set (Omega -> Real)} {I : Real}
    -- USER-INPUT: estimating equation, random-index replacement, QMD transport,
    -- cross-moment identity, and nonsingularity; vdV Theorem 25.59.
    (h : RawMovingBiasExpansionHyp P gamma estimator theta0 scoreHat score0 F I) :
    TendstoInProbZero (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        let Delta := Real.sqrt n * (estimator n X - theta0)
        (1 + |Delta|)⁻¹ *
          (Delta
            - I⁻¹ * ((Real.sqrt n)⁻¹ *
                ∑ i : Fin n, (score0 : Lp Real 2 P) (X i))
            - I⁻¹ * rawMovingBias gamma estimator theta0 scoreHat n X)) := by
  have hmean : ∫ x, (score0 : Lp ℝ 2 P) x ∂P = 0 := by
    have hker : (score0 : Lp ℝ 2 P) ∈
        LinearMap.ker (integralL2 P).toLinearMap := score0.2
    rw [LinearMap.mem_ker] at hker
    change ⟪oneL2 P, (score0 : Lp ℝ 2 P)⟫_ℝ = 0 at hker
    rw [MeasureTheory.L2.inner_def] at hker
    have hone : ((oneL2 P : Lp ℝ 2 P) : Omega → ℝ) =ᵐ[P] fun _ => 1 :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    rw [integral_congr_ae] at hker
    · exact hker
    · filter_upwards [hone] with x hx
      change (score0 : Lp ℝ 2 P) x * (oneL2 P : Lp ℝ 2 P) x = _
      rw [hx, mul_one]
  have hB0 := randomIndex_empiricalScoreReplacement_oP h.B0
  have hShift := qmdPath_modelShift_normalized_oP h.hTransport
  have hIne : I ≠ 0 := ne_of_gt h.hI
  refine tendstoInProbZero_of_abs_le_three
    (c := |I⁻¹|) (abs_pos.mpr (inv_ne_zero hIne)) hB0 hShift h.score_eq ?_
  intro n X
  rw [integral_sub (h.hTransport.scoreHat_integrable_truth n X)
    (h.B0.score0_memLp.integrable (by norm_num)), hmean, sub_zero,
    Finset.sum_sub_distrib]
  simp only [rawMovingBias, h.hCross]
  let r : ℝ := Real.sqrt n
  let q : ℝ := (Real.sqrt n)⁻¹
  let delta : ℝ := estimator n X - theta0
  let Delta : ℝ := r * delta
  let sumHat : ℝ := ∑ i : Fin n, scoreHat n X (X i)
  let sum0 : ℝ := ∑ i : Fin n, (score0 : Lp ℝ 2 P) (X i)
  let pHat : ℝ := ∫ x, scoreHat n X x ∂P
  let pMove : ℝ := ∫ x, scoreHat n X x ∂(gamma.curve delta)
  change |(1 + |Delta|)⁻¹ *
        (Delta - I⁻¹ * (q * sum0) - I⁻¹ * (r * pMove))| ≤
    |I⁻¹| *
      (|q * (sumHat - sum0) - r * pHat| +
        |(if delta = 0 then 0 else ((pMove - pHat) - delta * I) / |delta|)| +
        |q * sumHat|)
  let A := q * (sumHat - sum0) - r * pHat
  let M := r * (pHat - pMove) + Delta * I
  let E := q * sumHat
  let N := if delta = 0 then 0 else ((pMove - pHat) - delta * I) / |delta|
  have halg :
      (1 + |Delta|)⁻¹ *
          (Delta - I⁻¹ * (q * sum0) - I⁻¹ * (r * pMove)) =
        (1 + |Delta|)⁻¹ * I⁻¹ * (A + M - E) := by
    calc
      _ = (1 + |Delta|)⁻¹ * (I⁻¹ * (A + M - E)) := by
        rw [show A + M - E =
          (q * (sumHat - sum0) - r * pHat) +
            (r * (pHat - pMove) + Delta * I) - q * sumHat from rfl,
          rawMovingBias_algebra I q r Delta sumHat sum0 pHat pMove hIne]
      _ = _ := by ring
  have hden0 : 0 ≤ (1 + |Delta|)⁻¹ := by positivity
  have hden1 : (1 + |Delta|)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by linarith [abs_nonneg Delta])
  have hM : (1 + |Delta|)⁻¹ * |M| ≤ |N| := by
    by_cases hd : delta = 0
    · have hD : Delta = 0 := by simp [Delta, delta, hd]
      have hp : pMove = pHat := by simp [pMove, pHat, delta, hd, gamma.curve_at_zero]
      simp [M, N, hd, hD, hp]
    · have hr : 0 ≤ r := by simp [r]
      have habs : |Delta| = r * |delta| := by
        simp [Delta, abs_mul, abs_of_nonneg hr]
      have hcoeff : (1 + |Delta|)⁻¹ * (r * |delta|) ≤ 1 := by
        rw [← habs, mul_comm]
        exact mul_inv_le_one_of_le₀ (by linarith [abs_nonneg Delta]) (by positivity)
      have hMabs : |M| = r * |(pMove - pHat) - delta * I| := by
        rw [show M = -r * ((pMove - pHat) - delta * I) by
          simp only [M, Delta]; ring,
          abs_mul, abs_neg, abs_of_nonneg hr]
      calc
        (1 + |Delta|)⁻¹ * |M| =
            ((1 + |Delta|)⁻¹ * (r * |delta|)) *
              (|(pMove - pHat) - delta * I| / |delta|) := by
                rw [hMabs]
                field_simp [abs_ne_zero.mpr hd]
        _ ≤ 1 * (|(pMove - pHat) - delta * I| / |delta|) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
        _ = |N| := by simp [N, hd, abs_div]
  rw [halg, abs_mul, abs_mul, abs_of_nonneg hden0]
  have htri : |A + M - E| ≤ |A| + |M| + |E| := by
    calc
      _ ≤ |A + M| + |E| := abs_sub _ _
      _ ≤ (|A| + |M|) + |E| := by gcongr; exact abs_add_le A M
  calc
    (1 + |Delta|)⁻¹ * |I⁻¹| * |A + M - E| ≤
        (1 + |Delta|)⁻¹ * |I⁻¹| * (|A| + |M| + |E|) :=
      mul_le_mul_of_nonneg_left htri (mul_nonneg hden0 (abs_nonneg _))
    _ = |I⁻¹| * ((1 + |Delta|)⁻¹ * |A| +
        (1 + |Delta|)⁻¹ * |M| + (1 + |Delta|)⁻¹ * |E|) := by ring
    _ ≤ |I⁻¹| * (|A| + |N| + |E|) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add
          (mul_le_of_le_one_left (abs_nonneg A) hden1) hM)
          (mul_le_of_le_one_left (abs_nonneg E) hden1)) (abs_nonneg _)

/-- Conditional ordinary expansion obtained from the rate-free corrected vdV 25.59 form.

The conclusion uses the stated asymptotic-linearity-with-bias predicate.
Its bias argument is `+ I⁻¹ B_n`, rather than the negative-residual convention.
Root-`n` tightness is an additional assumption not supplied by the stated
vdV 25.59 hypotheses, so this result is
a conditional corollary rather than the unqualified book theorem.

Proof idea: combine `rawMovingBias_normalized_expansion_2559` with
`hDelta_tight` to remove the self-normalizer, or assemble directly from
`randomIndex_empiricalScoreReplacement_oP` and
`qmdPath_modelShift_oP_of_sqrtN_tight`; rewrite the cross moment using
`h.hCross`, use `h.score_eq`, and divide by the nonzero `I`
obtained from `h.hI`.
-/
theorem rawMovingBias_expansion_2559_of_sqrtN_tight
    {P : Measure Omega} [IsProbabilityMeasure P]
    {gamma : QMDPath P}
    {estimator : forall n, (Fin n -> Omega) -> Real} {theta0 : Real}
    {scoreHat : forall n, (Fin n -> Omega) -> Omega -> Real}
    {score0 : ↥(L2ZeroMean P)} {F : Set (Omega -> Real)} {I : Real}
    -- USER-INPUT: estimating equation, random-index replacement, QMD transport,
    -- cross-moment identity, and nonsingularity; vdV Theorem 25.59.
    (h : RawMovingBiasExpansionHyp P gamma estimator theta0 scoreHat score0 F I)
    -- root-`n` tightness is not supplied by the stated vdV 25.59
    -- hypotheses; it makes this result a conditional corollary.
    (hDelta_tight : IsBoundedInProb
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n * (estimator n X - theta0))) :
    AsymptoticallyLinearWithBiasAt estimator P (I⁻¹ • score0) theta0
      (fun n X => I⁻¹ * rawMovingBias gamma estimator theta0 scoreHat n X) := by
  let Pn := fun n : ℕ => Measure.pi (fun _ : Fin n => P)
  let Delta := fun n (X : Fin n → Omega) => Real.sqrt n * (estimator n X - theta0)
  let R := fun n (X : Fin n → Omega) =>
    Delta n X - I⁻¹ * ((Real.sqrt n)⁻¹ *
      ∑ i : Fin n, (score0 : Lp ℝ 2 P) (X i)) -
        I⁻¹ * rawMovingBias gamma estimator theta0 scoreHat n X
  have hnorm := rawMovingBias_normalized_expansion_2559 h
  have hfactor : IsBoundedInProb Pn (fun n X => 1 + |Delta n X|) := by
    intro epsilon hepsilon
    obtain ⟨M, hM⟩ := hDelta_tight epsilon hepsilon
    refine ⟨M + 1, fun n => ?_⟩
    rw [show {X | M + 1 < ‖1 + |Delta n X|‖} =
        {X | M < ‖Delta n X‖} by
      ext X
      have hnonneg : 0 ≤ 1 + |Delta n X| := by positivity
      simp only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      constructor <;> intro hx <;> linarith]
    exact hM n
  have hR := tendstoInProbZero_of_isBoundedInProb_mul hfactor hnorm
  have hResidual : TendstoInProbZero Pn R := by
    convert hR using 1
    funext n X
    simp only [smul_eq_mul, R, Delta]
    conv_rhs => rw [← mul_assoc, mul_inv_cancel₀ (by positivity :
      1 + |Real.sqrt n * (estimator n X - theta0)| ≠ 0), one_mul]
  intro epsilon hepsilon
  rw [← ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top (Pn n) _)]
  have hcoeP :
      (fun x => ((((I⁻¹ • score0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) :
        Omega → ℝ) x)) =ᵐ[P]
        fun x => I⁻¹ * (score0 : Lp ℝ 2 P) x := by
    change (((I⁻¹ • (score0 : Lp ℝ 2 P) : Lp ℝ 2 P) : Omega → ℝ)) =ᵐ[P] _
    simpa only [smul_eq_mul] using! Lp.coeFn_smul I⁻¹ (score0 : Lp ℝ 2 P)
  refine (hResidual epsilon hepsilon).congr' ?_
  filter_upwards [] with n
  rw [measureReal_def]
  apply congrArg ENNReal.toReal
  apply measure_congr
  have hcoePi : ∀ i : Fin n,
      (fun X : Fin n → Omega =>
        ((((I⁻¹ • score0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Omega → ℝ) (X i))) =ᵐ[Pn n]
          fun X => I⁻¹ * (score0 : Lp ℝ 2 P) (X i) := fun i =>
    hcoeP.comp_tendsto <|
      (measurePreserving_eval (μ := fun _ : Fin n => P) i).quasiMeasurePreserving.tendsto_ae
  have hcoeAll : ∀ᵐ X ∂(Pn n), ∀ i,
      ((((I⁻¹ • score0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Omega → ℝ) (X i)) =
        I⁻¹ * (score0 : Lp ℝ 2 P) (X i) := by
    rw [ae_all_iff]
    exact hcoePi
  filter_upwards [hcoeAll] with X hX
  have hsum :
      (∑ i : Fin n,
        ((((I⁻¹ • score0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Omega → ℝ) (X i))) =
        I⁻¹ * ∑ i : Fin n, (score0 : Lp ℝ 2 P) (X i) := by
    rw [Finset.sum_congr rfl (fun i _ => hX i), ← Finset.mul_sum]
  change (epsilon ≤ |Real.sqrt n * (estimator n X - theta0) -
      I⁻¹ * ((Real.sqrt n)⁻¹ * ∑ i : Fin n, (score0 : Lp ℝ 2 P) (X i)) -
      I⁻¹ * rawMovingBias gamma estimator theta0 scoreHat n X|) =
    (epsilon ≤ |Real.sqrt n * (estimator n X - theta0) -
      (Real.sqrt n)⁻¹ * ∑ i : Fin n,
        ((((I⁻¹ • score0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Omega → ℝ) (X i)) -
      I⁻¹ * rawMovingBias gamma estimator theta0 scoreHat n X|)
  rw [hsum]
  ring

/-- Conditional corollary with the literal printed `+ B_n` form of vdV Theorem 25.59,
valid in the information-normalized scalar coordinate `I = 1`.

This corollary is the explicit erratum boundary: without `hI_one`, the
covariant statement is `rawMovingBias_expansion_2559_of_sqrtN_tight` and the
bias is `+ I⁻¹ B_n`. It also takes root-`n` tightness as an additional user
input not supplied by the stated vdV 25.59 hypotheses.

Proof idea: specialize `rawMovingBias_expansion_2559_of_sqrtN_tight` and
rewrite both `I⁻¹ • score0` and `I⁻¹ * B_n` with `hI_one`.
-/
theorem rawMovingBias_expansion_2559_vdv_printed_of_information_eq_one
    {P : Measure Omega} [IsProbabilityMeasure P]
    {gamma : QMDPath P}
    {estimator : forall n, (Fin n -> Omega) -> Real} {theta0 : Real}
    {scoreHat : forall n, (Fin n -> Omega) -> Omega -> Real}
    {score0 : ↥(L2ZeroMean P)} {F : Set (Omega -> Real)} {I : Real}
    -- estimating equation, random-index replacement, QMD transport,
    -- cross-moment identity, and nonsingularity; vdV Theorem 25.59.
    (h : RawMovingBiasExpansionHyp P gamma estimator theta0 scoreHat score0 F I)
    -- information-normalized coordinate required by vdV's printed display.
    (hI_one : I = 1)
    -- root-`n` tightness is not supplied by the stated vdV 25.59
    -- hypotheses; it makes this result a conditional corollary.
    (hDelta_tight : IsBoundedInProb
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n * (estimator n X - theta0))) :
    AsymptoticallyLinearWithBiasAt estimator P score0 theta0
      (rawMovingBias gamma estimator theta0 scoreHat) := by
  subst I
  simpa using rawMovingBias_expansion_2559_of_sqrtN_tight h hDelta_tight

/-- Root-`n` tightness bootstrap for the scalar form of vdV Theorem 25.54.

Equation (25.52) is stated for the raw moving-parameter, fixed-nuisance bias
`B_n`.  Together with the normalized corrected 25.59 expansion, it rules out
escape of `Delta_n = sqrt n * (thetaHat_n - theta0)`: on a large-`Delta_n`
event, the tight normalized empirical sum is small, while both normalized
remainder terms vanish in probability.

Proof idea: `rawMovingBias_normalized_expansion_2559 h` supplies corrected
normalized 25.59; `h52` is normalized equation (25.52); the fixed-score
empirical sum is tight from the `L2ZeroMean` score carried by `h.B0`.  An event
split at a deterministic empirical-sum bound then bootstraps `Delta_n =
O_P(1)`.

Here `h` supplies the estimating-equation, empirical-replacement,
QMD-transport, cross-moment, and nonsingularity inputs through the normalized
25.59 theorem; deleting `h52` removes exactly vdV's no-bias condition and
leaves only the 25.59 conclusion.  The `hEstimator_meas` hypothesis makes the
finitely many pre-asymptotic estimator laws tight.
-/
theorem rawMovingBias_sqrtN_tight_2554
    {P : Measure Omega} [IsProbabilityMeasure P]
    {gamma : QMDPath P}
    {estimator : forall n, (Fin n -> Omega) -> Real} {theta0 : Real}
    {scoreHat : forall n, (Fin n -> Omega) -> Omega -> Real}
    {score0 : ↥(L2ZeroMean P)} {F : Set (Omega -> Real)} {I : Real}
    -- estimating equation, random-index replacement, QMD transport,
    -- cross-moment identity, and nonsingularity; vdV Theorem 25.54.
    (h : RawMovingBiasExpansionHyp P gamma estimator theta0 scoreHat score0 F I)
    -- LEAN-ONLY: finite-prefix tightness for the all-`n` `O_P(1)` predicate used here.
    (hEstimator_meas : forall n, Measurable (estimator n))
    -- USER-INPUT: vdV equation (25.52), in the rate-free normalized form.
    (h52 : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        (1 + |Real.sqrt n * (estimator n X - theta0)|)⁻¹ *
          rawMovingBias gamma estimator theta0 scoreHat n X)) :
    IsBoundedInProb
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n * (estimator n X - theta0)) := by
  classical
  let Pn := fun n : ℕ => Measure.pi (fun _ : Fin n => P)
  let Delta := fun n (X : Fin n → Omega) => Real.sqrt n * (estimator n X - theta0)
  let S := fun n (X : Fin n → Omega) => (Real.sqrt n)⁻¹ *
    ∑ i : Fin n, (score0 : Lp ℝ 2 P) (X i)
  have hmean : ∫ x, (score0 : Lp ℝ 2 P) x ∂P = 0 := by
    have hker : (score0 : Lp ℝ 2 P) ∈
        LinearMap.ker (integralL2 P).toLinearMap := score0.2
    rw [LinearMap.mem_ker] at hker
    change ⟪oneL2 P, (score0 : Lp ℝ 2 P)⟫_ℝ = 0 at hker
    rw [MeasureTheory.L2.inner_def] at hker
    have hone : ((oneL2 P : Lp ℝ 2 P) : Omega → ℝ) =ᵐ[P] fun _ => 1 :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    rw [integral_congr_ae] at hker
    · exact hker
    · filter_upwards [hone] with x hx
      change (score0 : Lp ℝ 2 P) x * (oneL2 P : Lp ℝ 2 P) x = _
      rw [hx, mul_one]
  have hS : IsBoundedInProb Pn S := by
    intro epsilon hepsilon
    let g : Omega → ℝ := fun x => (score0 : Lp ℝ 2 P) x
    let V := ProbabilityTheory.variance g P
    have hV : 0 ≤ V := ENNReal.toReal_nonneg
    let K := Real.sqrt (V / epsilon + 1)
    have hK : 0 < K := Real.sqrt_pos.mpr (by positivity)
    have hVK : V / K ^ 2 ≤ epsilon := by
      rw [show K ^ 2 = V / epsilon + 1 by
        exact Real.sq_sqrt (by positivity)]
      by_cases hV0 : V = 0
      · simp [hV0, hepsilon.le]
      · have hVp : 0 < V := lt_of_le_of_ne hV (Ne.symm hV0)
        calc V / (V / epsilon + 1) ≤ V / (V / epsilon) :=
              div_le_div_of_nonneg_left hVp.le (div_pos hVp hepsilon)
                (by linarith)
          _ = epsilon := by field_simp
    refine ⟨K, fun n => ?_⟩
    by_cases hn : n = 0
    · subst n
      have hset : {X : Fin 0 → Omega | K < ‖S 0 X‖} = ∅ := by
        ext X
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          S, Nat.cast_zero, Real.sqrt_zero, inv_zero, Fin.sum_univ_zero,
          mul_zero, norm_zero]
        exact not_lt_of_ge hK.le
      rw [hset, measureReal_empty]
      exact hepsilon.le
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hgi : ∀ i : Fin n, MemLp (fun X : Fin n → Omega => g (X i)) 2 (Pn n) :=
      fun i => h.B0.score0_memLp.comp_measurePreserving
        (measurePreserving_eval (μ := fun _ : Fin n => P) i)
    have hSmem : MemLp (S n) 2 (Pn n) :=
      (memLp_finset_sum Finset.univ (fun i _ => hgi i)).const_mul _
    have hSint : ∫ X, S n X ∂(Pn n) = 0 := by
      have heach : ∀ i : Fin n,
          ∫ X : Fin n → Omega, g (X i) ∂(Pn n) = 0 := by
        intro i
        rw [integral_comp_eval (i := i) (μ := fun _ : Fin n => P)
          h.B0.score0_memLp.aestronglyMeasurable]
        exact hmean
      rw [show S n = fun X => (Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i) from rfl,
        integral_const_mul, integral_finset_sum _
          (fun i _ => (hgi i).integrable (by norm_num))]
      simp [heach]
    have hSvar : ProbabilityTheory.variance (S n) (Pn n) = V := by
      rw [show S n = fun X => (Real.sqrt n)⁻¹ * ∑ i : Fin n, g (X i) from rfl,
        ProbabilityTheory.variance_const_mul]
      have hp := ProbabilityTheory.variance_sum_pi
        (μ := fun _ : Fin n => P) (X := fun _ : Fin n => g)
        (fun _ => h.B0.score0_memLp)
      have heq : (∑ i : Fin n, fun X : Fin n → Omega => g (X i)) =
          fun X => ∑ i : Fin n, g (X i) := by funext X; simp [Finset.sum_apply]
      rw [heq] at hp
      rw [hp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hsqrt : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
        Real.mul_self_sqrt hnR.le
      rw [show (Real.sqrt n)⁻¹ ^ 2 = (n : ℝ)⁻¹ by rw [inv_pow, sq, hsqrt]]
      field_simp
      rfl
    have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hSmem hK
    rw [hSint, hSvar] at hcheb
    simp only [sub_zero] at hcheb
    rw [measureReal_def]
    calc
      ((Pn n) {X | K < ‖S n X‖}).toReal ≤ (ENNReal.ofReal epsilon).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono (fun X hX => by
          simpa [Real.norm_eq_abs] using le_of_lt hX)).trans
            (hcheb.trans (ENNReal.ofReal_le_ofReal hVK)))
      _ = epsilon := ENNReal.toReal_ofReal hepsilon.le
  let T := fun n (X : Fin n → Omega) => I⁻¹ * S n X
  have hT : IsBoundedInProb Pn T := by
    intro epsilon hepsilon
    obtain ⟨K, hK⟩ := hS epsilon hepsilon
    refine ⟨|I⁻¹| * max K 0, fun n => (measureReal_mono (fun X hX => ?_)).trans (hK n)⟩
    simp only [Set.mem_setOf_eq, T, Real.norm_eq_abs, abs_mul] at hX ⊢
    have hc : 0 < |I⁻¹| := abs_pos.mpr (inv_ne_zero (ne_of_gt h.hI))
    have hm : max K 0 < |S n X| := by nlinarith [hX]
    exact lt_of_le_of_lt (le_max_left K 0) hm
  let B := rawMovingBias gamma estimator theta0 scoreHat
  let d := fun n (X : Fin n → Omega) => (1 + |Delta n X|)⁻¹
  let R := fun n (X : Fin n → Omega) => d n X * (Delta n X - T n X - I⁻¹ * B n X)
  have hR : TendstoInProbZero Pn R := by
    simpa [Pn, Delta, S, T, B, d, R] using rawMovingBias_normalized_expansion_2559 h
  have h52I : TendstoInProbZero Pn (fun n X => I⁻¹ * (d n X * B n X)) := by
    intro a ha
    have hc : 0 < |I⁻¹| := abs_pos.mpr (inv_ne_zero (ne_of_gt h.hI))
    simpa only [Pn, Delta, B, d, Real.norm_eq_abs, abs_mul,
      div_le_iff₀ hc, mul_comm] using h52 (a / |I⁻¹|) (div_pos ha hc)
  have hzero : TendstoInProbZero Pn (fun n X => (0 : ℝ)) := by
    intro a ha
    simpa only [norm_zero, not_le.mpr ha, Set.setOf_false, measureReal_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hE : TendstoInProbZero Pn
      (fun n X => R n X + I⁻¹ * (d n X * B n X)) := by
    refine tendstoInProbZero_of_abs_le_three (c := 1) zero_lt_one hR h52I hzero ?_
    intro n X
    simp only [one_mul, abs_zero, add_zero]
    exact abs_add_le _ _
  intro epsilon hepsilon
  obtain ⟨K, hK⟩ := hT (epsilon / 2) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp <|
    (hE (1 / 2) (by norm_num)).eventually (Iio_mem_nhds (by positivity : 0 < epsilon / 2))
  let Dpre := fun n (X : Fin n → Omega) => if n < N then Delta n X else 0
  have hDpre0 : TendstoInProbZero Pn Dpre := by
    intro a ha
    apply (tendsto_congr' (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)).2
      tendsto_const_nhds
    have hset : {X : Fin n → Omega | a ≤ ‖Dpre n X‖} = ∅ := by
      ext X; simp [Dpre, not_lt.mpr hn, not_le.mpr ha]
    rw [hset, measureReal_empty]
  have hDpre_meas : ∀ n, Measurable (Dpre n) := by
    intro n
    by_cases hn : n < N
    · simpa [Dpre, hn, Delta] using (hEstimator_meas n).sub_const theta0 |>.const_mul (Real.sqrt n)
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
      {X | K < ‖T n X‖} ∪ {X | 1 / 2 ≤ ‖R n X + I⁻¹ * (d n X * B n X)‖} := by
    intro X hX
    by_cases hTX : K < ‖T n X‖
    · exact Or.inl hTX
    · refine Or.inr ?_
      simp only [Set.mem_setOf_eq]
      rw [show R n X + I⁻¹ * (d n X * B n X) = d n X * (Delta n X - T n X) by
        simp only [R, d]; ring, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ d n X)]
      have htri : |Delta n X| - |T n X| ≤ |Delta n X - T n X| := by
        have ht := abs_add_le (Delta n X - T n X) (T n X)
        rw [sub_add_cancel] at ht
        linarith
      have hlarge : 2 * max K 0 + 1 < |Delta n X| :=
        lt_of_le_of_lt (le_max_right _ _) (by simpa [Real.norm_eq_abs] using hX)
      have hsmall : |T n X| ≤ max K 0 :=
        (not_lt.mp hTX).trans (le_max_left K 0)
      simp only [d]
      have hden : 0 < 1 + |Delta n X| := by positivity
      rw [show (1 / 2 : ℝ) = (1 + |Delta n X|)⁻¹ * ((1 + |Delta n X|) / 2) by
        field_simp]
      exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hden.le)
  calc
    (Pn n).real {X | max M0 (2 * max K 0 + 1) < ‖Delta n X‖}
        ≤ (Pn n).real ({X | K < ‖T n X‖} ∪
            {X | 1 / 2 ≤ ‖R n X + I⁻¹ * (d n X * B n X)‖}) := measureReal_mono hsub
    _ ≤ (Pn n).real {X | K < ‖T n X‖} +
          (Pn n).real {X | 1 / 2 ≤ ‖R n X + I⁻¹ * (d n X * B n X)‖} :=
      measureReal_union_le _ _
    _ ≤ epsilon := by linarith [hK n, hN n (not_lt.mp hn)]

/-- Scalar vdV Theorem 25.54 assembled from its raw no-bias condition.

This conclusion contains no bias term: normalized equation (25.52) first
bootstraps root-`n` tightness, then yields the ordinary raw-bias convergence
needed to collapse the corrected 25.59 expansion.

Proof idea: apply `rawMovingBias_sqrtN_tight_2554 h hEstimator_meas h52`;
combine the resulting tightness with `h52` to remove the self-normalizer and
prove `B_n ->_P 0`; specialize `rawMovingBias_expansion_2559_of_sqrtN_tight`;
finally use the 25.59-to-25.54 vanishing-bias collapse.

Here `h52` is precisely the additional (25.52) input distinguishing
25.54 from 25.59; `h` is consumed by both the tightness bootstrap and the
corrected ordinary 25.59 expansion.  No asymptotic-linearity, tightness,
raw-bias-vanishing, or Bartlett conclusion is assumed.  `hEstimator_meas` is
passed only to the finite-prefix step of the tightness bootstrap.
-/
theorem rawMovingBias_asympLinear_2554
    {P : Measure Omega} [IsProbabilityMeasure P]
    {gamma : QMDPath P}
    {estimator : forall n, (Fin n -> Omega) -> Real} {theta0 : Real}
    {scoreHat : forall n, (Fin n -> Omega) -> Omega -> Real}
    {score0 : ↥(L2ZeroMean P)} {F : Set (Omega -> Real)} {I : Real}
    -- USER-INPUT: estimating equation, random-index replacement, QMD transport,
    -- cross-moment identity, and nonsingularity; vdV Theorem 25.54.
    (h : RawMovingBiasExpansionHyp P gamma estimator theta0 scoreHat score0 F I)
    -- LEAN-ONLY: finite-prefix tightness for the all-`n` `O_P(1)` predicate used here.
    (hEstimator_meas : forall n, Measurable (estimator n))
    -- USER-INPUT: equation (25.52), in rate-free normalized form;
    -- vdV Theorem 25.54.
    (h52 : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        (1 + |Real.sqrt n * (estimator n X - theta0)|)⁻¹ *
          rawMovingBias gamma estimator theta0 scoreHat n X)) :
    AsymptoticallyLinearAt estimator P (I⁻¹ • score0) theta0 := by
  let Pn := fun n : ℕ => Measure.pi (fun _ : Fin n => P)
  let Delta := fun n (X : Fin n → Omega) => Real.sqrt n * (estimator n X - theta0)
  let B := rawMovingBias gamma estimator theta0 scoreHat
  have hDelta := rawMovingBias_sqrtN_tight_2554 h hEstimator_meas h52
  have hfactor : IsBoundedInProb Pn (fun n X => 1 + |Delta n X|) := by
    intro epsilon hepsilon
    obtain ⟨M, hM⟩ := hDelta epsilon hepsilon
    refine ⟨M + 1, fun n => ?_⟩
    rw [show {X | M + 1 < ‖1 + |Delta n X|‖} = {X | M < ‖Delta n X‖} by
      ext X
      simp only [Set.mem_setOf_eq, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 1 + |Delta n X|)]
      constructor <;> intro hX <;> linarith]
    exact hM n
  have hB0 : TendstoInProbZero Pn B := by
    have hp := tendstoInProbZero_of_isBoundedInProb_mul hfactor h52
    convert hp using 1
    funext n X
    change B n X = (1 + |Delta n X|) * ((1 + |Delta n X|)⁻¹ * B n X)
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity : 1 + |Delta n X| ≠ 0), one_mul]
  have hBias : TendstoInProbZero Pn (fun n X => I⁻¹ * B n X) := by
    intro a ha
    have hc : 0 < |I⁻¹| := abs_pos.mpr (inv_ne_zero (ne_of_gt h.hI))
    simpa only [Real.norm_eq_abs, abs_mul, div_le_iff₀ hc, mul_comm] using
      hB0 (a / |I⁻¹|) (div_pos ha hc)
  have hALB := rawMovingBias_expansion_2559_of_sqrtN_tight h hDelta
  let A := fun n (X : Fin n → Omega) => Real.sqrt n * (estimator n X - theta0) -
    (Real.sqrt n)⁻¹ * ∑ i : Fin n,
      ((((I⁻¹ • score0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Omega → ℝ) (X i))
  have hR0 : TendstoInProbZero Pn (fun n X => A n X - I⁻¹ * B n X) := by
    intro a ha
    apply (ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top (Pn n) _)).mpr
    simpa [Pn, A, B, Real.norm_eq_abs] using hALB a ha
  have hzero : TendstoInProbZero Pn (fun n X => (0 : ℝ)) := by
    intro a ha
    simpa only [norm_zero, not_le.mpr ha, Set.setOf_false, measureReal_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hA : TendstoInProbZero Pn A := by
    refine tendstoInProbZero_of_abs_le_three (c := 1) zero_lt_one hR0 hBias hzero ?_
    intro n X
    have ht := abs_add_le (A n X - I⁻¹ * B n X) (I⁻¹ * B n X)
    rw [sub_add_cancel] at ht
    simpa [Real.norm_eq_abs] using ht
  intro a ha
  rw [← ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top (Pn n) _)]
  simpa [Pn, A, Real.norm_eq_abs] using! hA a ha

namespace RawMovingBiasExpansionHyp

/-- Build the scalar raw moving-bias bundle from an efficient score and an
ordinary-score QMD path. The cross moment is derived from efficient-score
orthogonality and `hScore`, rather than supplied separately.

Proof idea: rewrite the QMD-path score with `hScore`, identify the resulting
inner product by `efficientScore_inner_ordinary_eq_self`, and unfold
`efficientInformation` for the diagonal efficient-score norm.
-/
theorem ofEfficientScore
    {P : Measure Omega} [IsProbabilityMeasure P]
    {Theta : Type*} [NormedAddCommGroup Theta] [InnerProductSpace Real Theta]
    [CompleteSpace Theta]
    (S_theta : OrdinaryScore P Theta) (T_nuis : NuisanceTangentSpace P)
    -- Mathlib's orthogonal projection API requires this instance.
    [proj : T_nuis.HasOrthogonalProjection] (v : Theta)
    {gamma : QMDPath P}
    {estimator : forall n, (Fin n -> Omega) -> Real} {theta0 : Real}
    {scoreHat : forall n, (Fin n -> Omega) -> Omega -> Real}
    {F : Set (Omega -> Real)}
    -- vdV §25.8 estimating equation at the fitted score.
    (score_eq : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X => (Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreHat n X (X i)))
    -- vdV Lemma 19.24 random-index replacement primitives.
    (B0 : RandomIndexScoreReplacementHyp P scoreHat
      (fun omega => ((@efficientScore Omega _ P _ Theta _ _ _
        S_theta T_nuis proj v : Lp Real 2 P) :
        Omega -> Real) omega) F)
    -- vdV §25.8 DQM plus condition (25.53) moving-law score transport primitives.
    (hTransport : HellingerScoreTransportHyp P gamma estimator theta0 scoreHat
      (fun omega => ((@efficientScore Omega _ P _ Theta _ _ _
        S_theta T_nuis proj v : Lp Real 2 P) :
        Omega -> Real) omega))
    -- the supplied QMD path realizes the ordinary score direction `v`.
    (hScore : gamma.score = S_theta v)
    -- vdV Theorem 25.54 nonsingularity of efficient information.
    (hI : 0 < @efficientInformation Omega _ P _ Theta _ _ _
      S_theta T_nuis proj v) :
    RawMovingBiasExpansionHyp P gamma estimator theta0 scoreHat
      (@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj v) F
      (@efficientInformation Omega _ P _ Theta _ _ _
        S_theta T_nuis proj v) := by
  refine ⟨score_eq, B0, hTransport, ?_, hI⟩
  rw [hScore]
  calc
    (∫ x,
        ((@efficientScore Omega _ P _ Theta _ _ _
          S_theta T_nuis proj v : Lp Real 2 P) : Omega → Real) x *
          (((S_theta v : ↥(L2ZeroMean P)) : Lp Real 2 P) : Omega → Real) x ∂P) =
        inner Real
          ((@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj v :
            ↥(L2ZeroMean P)) : Lp Real 2 P)
          ((S_theta v : ↥(L2ZeroMean P)) : Lp Real 2 P) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => mul_comm _ _
    _ = inner Real
          ((@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj v :
            ↥(L2ZeroMean P)) : Lp Real 2 P)
          ((@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj v :
            ↥(L2ZeroMean P)) : Lp Real 2 P) :=
      @efficientScore_inner_ordinary_eq_self Omega _ P _ Theta _ _ _
        S_theta T_nuis proj v v
    _ = @efficientInformation Omega _ P _ Theta _ _ _
          S_theta T_nuis proj v := by
      rw [real_inner_self_eq_norm_sq]
      rfl

end RawMovingBiasExpansionHyp

end AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasExpansion
