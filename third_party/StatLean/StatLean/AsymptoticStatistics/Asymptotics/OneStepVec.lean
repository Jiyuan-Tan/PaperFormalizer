module
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScoreVec
public import StatLean.AsymptoticStatistics.Core.EfficiencyOperationalVec
public import StatLean.AsymptoticStatistics.ForMathlib.InProbability
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs

@[expose] public section

/-!
# One-step estimator semiparametric efficiency — vector parameter

Vector-parameter (`θ ∈ ℝᵈ`) counterpart of
`AsymptoticStatistics.Asymptotics.OneStep`. Given a `√n`-rate consistent
preliminary estimator, the one-step estimator
`θ̂_n := θ̃_n + Î_n⁻¹ · (1/n) Σ_i ℓ̂_n(X_i, θ̃_n)` (with `Î_n⁻¹` a `d × d`
matrix correction) is asymptotically linear with vector influence
function `Ĩ⁻¹ ℓ̃` and asymptotically efficient under (25.55) + (25.56).

The structure below records the empirical-process consequence as the explicit
assumption `asympLinear_25_57_vec`. The primitive conditions (25.55)--(25.56)
imply this assumption in `Asymptotics.Discharge.OneStepVec`.

Reference: vdV §25.5, thm:25.57 (vector form).

Main declarations: `OneStepAssumptions_vec`,
`oneStep_semiparametricallyEfficient_vec`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.OneStepVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec

variable {Ω : Type*} [MeasurableSpace Ω]
variable {d : ℕ}

/-- *Bundled assumptions for vdV thm:25.57 (one-step semiparametric
efficiency, vector parameter).*

Structure parameters: model identity (`S_θ`, `T_nuis`, `e`, `T`, `Dψ`) +
estimator triple (`preliminary`, `score_estimate_seq`,
`info_estimate_seq`) + the combined one-step estimator + vector
centering `θ₀`. The one-step formula `estimator_def` uses the matrix
inverse `Î_n⁻¹` of the (vector-valued) information estimate.

Reference: vdV §25.5, thm:25.57 (vector form). -/
structure OneStepAssumptions_vec
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [proj : T_nuis.HasOrthogonalProjection] (e : Fin d → Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P)) (Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d))
    (preliminary : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (score_estimate_seq : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (info_estimate_seq : ∀ n, (Fin n → Ω) → Matrix (Fin d) (Fin d) ℝ)
    (estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (θ₀ : EuclideanSpace ℝ (Fin d)) where
  /-- vdV §25.4 (lem:25.25): `Ĩ` positive-definite. -/
  hPD : (@efficientInformationMatrix Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e).PosDef
  /-- vdV §25.4 (lem:25.25): each `IF j ∈ T`. -/
  h_mem : ∀ j, @candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e j ∈ T
  /-- vdV §25.4 (lem:25.25): `Dψ`'s `j`-th coordinate acts as `⟪IF j, ·⟫`. -/
  h_Dψ : ∀ (j : Fin d) (g : T),
    (EuclideanSpace.proj j ∘L Dψ) g
      = ⟪@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e j,
          (g : ↥(L2ZeroMean P))⟫_ℝ
  /-- vdV §25.5 (eq:25.58, vector form): the one-step estimator is the
  preliminary plus the matrix-corrected empirical mean
  `θ̂_n = θ̃_n + Î_n⁻¹ · (1/n) Σ_i ℓ̂_n(X_i, θ̃_n)`. -/
  estimator_def : ∀ n (X : Fin n → Ω),
    estimator n X
      = preliminary n X
        + (info_estimate_seq n X)⁻¹.mulVecLin
            ((n : ℝ)⁻¹ • (∑ i, score_estimate_seq n (X i) (preliminary n X)))
  /-- vdV §25.5 (eqs:25.55 + 25.56 + `√n`-rate + info consistency
  `Î_n →_P Ĩ`): the one-step estimator is asymptotically linear at `P`
  with vector influence tuple `IF` and centering `θ₀`. This field is an
  explicit assumption of this conditional theorem. -/
  asympLinear_25_57_vec :
    AsymptoticallyLinearAt_vec estimator P
      (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) θ₀

/-- *vdV thm:25.57 — one-step semiparametric efficiency (vector
parameter).*

If the bundled `OneStepAssumptions_vec` holds and the vector centering
equals `ψ P`, then `estimator` is semiparametrically efficient at `P` for
the vector functional `ψ` relative to `T`.

Reference: vdV §25.5, thm:25.57 (vector form).

The efficient-score construction gives the vector EIF, while
`asympLinear_25_57_vec` gives the required expansion after substituting
`ψ P = θ₀`; `estimator_semiparametricallyEfficient_of_asympLinear_eif_vec`
combines these conclusions. -/
theorem oneStep_semiparametricallyEfficient_vec
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [proj : T_nuis.HasOrthogonalProjection] {e : Fin d → Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {preliminary : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {score_estimate_seq :
      ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {info_estimate_seq : ∀ n, (Fin n → Ω) → Matrix (Fin d) (Fin d) ℝ}
    {estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {θ₀ : EuclideanSpace ℝ (Fin d)}
    (h : @OneStepAssumptions_vec Ω _ d P _ Θ _ _ _ S_θ T_nuis proj e T Dψ
            preliminary score_estimate_seq info_estimate_seq estimator θ₀)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt_vec estimator ψ P T := by
  have hEIF : IsEfficientInfluenceFunction_vec Dψ
      (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) :=
    @eif_from_efficientScore_vec Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e T Dψ
      h.hPD h.h_mem h.h_Dψ
  have hAL : AsymptoticallyLinearAt_vec estimator P
      (@candidateVecEIF Ω _ P _ Θ _ _ _ d S_θ T_nuis proj e) (ψ P) := by
    rw [h_ψ]; exact h.asympLinear_25_57_vec
  exact estimator_semiparametricallyEfficient_of_asympLinear_eif_vec hEIF hAL

/-! ## Native formulation of vdV Theorem 25.57 -/

/-- The probability measure represented by a density in the local finite-dimensional
model used in the finite-dimensional form of Theorem 25.57. This is the book's
`P_{θ,η}` with the
nuisance value fixed. -/
noncomputable def modelMeasure
    (M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))) (μ : Measure Ω)
    (t : EuclideanSpace ℝ (Fin d)) : Measure Ω :=
  μ.withDensity fun x => ENNReal.ofReal (M.density t x)

/-- The square-root-density weighted score `ℓ̃_{θ,η} dP_{θ,η}^{1/2}`
appearing literally in vdV (25.56). -/
noncomputable def weightedScore
    (M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d)))
    (score : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (t : EuclideanSpace ℝ (Fin d)) (x : Ω) : EuclideanSpace ℝ (Fin d) :=
  M.sqrtDensity t x • score t x

/-- A deterministic sequence is in a root-`n` neighbourhood of `θ0` when
`√n · ‖θn-θ0‖` is eventually bounded. -/
def IsRootNBoundedSeq {d : ℕ}
    (thetaSeq : ℕ → EuclideanSpace ℝ (Fin d))
    (theta0 : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    Real.sqrt n * ‖thetaSeq n - theta0‖ ≤ C

/-- Empirical mean of the index-specific, sample-split estimated scores.

Constitutive (vdV §25.8 p.393): the nuisance estimate used for observation `i`
may depend on the other observations, hence both the full sample and `i` remain
visible in `scoreHat`.  At `n = 0` the empty sum and totalized inverse make this
zero. -/
noncomputable def scoreMean
    (scoreHat : ∀ n, (Fin n → Ω) → Fin n → EuclideanSpace ℝ (Fin d) →
      Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (X : Fin n → Ω) (t : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  (n : ℝ)⁻¹ • ∑ i, scoreHat n X i t (X i)

/-- Empirical efficient-information estimate: the Gram matrix of the indexed
estimated scores, normalized by `n`.

Constitutive (vdV §25.8 p.393): this is exactly the matrix inside the
one-step Newton correction, divided by `n`.  At `n = 0` it is the zero matrix. -/
noncomputable def empInfo
    (scoreHat : ∀ n, (Fin n → Ω) → Fin n → EuclideanSpace ℝ (Fin d) →
      Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (X : Fin n → Ω) (t : EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun j k => (n : ℝ)⁻¹ * ∑ i, scoreHat n X i t (X i) j * scoreHat n X i t (X i) k

/-- Turn a two-half shared nuisance-score construction into the indexed score
used by `scoreMean` and `empInfo`.

Constitutive (vdV §25.8 p.393): every observation in evaluation half `b` uses
the same score estimated from the opposite half.  At `n = 0` the function has
no index at which it can be evaluated. -/
def indexedSplitScore
    (splitSide : ∀ n, Fin n → Bool)
    (scoreHalf : ∀ n, (Fin n → Ω) → Bool → EuclideanSpace ℝ (Fin d) →
      Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (X : Fin n → Ω) (i : Fin n) :
    EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d) :=
  scoreHalf n X (splitSide n i)

/-- Primitive hypotheses for the vector form of vdV Theorem 25.57.

Constitutive (vdV §25.8 pp.393–394): the bundle contains the preliminary
root-`n` estimator and grid restriction, the two shared half-sample scores,
their book-constitutive `L²` integrability and score centering, the literal
deterministic-sequence clauses (25.55) and (25.56), and the exact one-step
formula.  It deliberately contains no asymptotic-linearity conclusion, no Ch5
condition (5.47), and no Z-estimator score equation or Taylor conclusion. -/
structure OneStep2557NativeHyp_vec
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_theta : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [proj : T_nuis.HasOrthogonalProjection] (e : Fin d → Θ)
    (M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))) (μ : Measure Ω)
    (theta0 : EuclideanSpace ℝ (Fin d))
    (scoreLocal : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (splitSide : ∀ n, Fin n → Bool)
    (scoreHalf : ∀ n, (Fin n → Ω) → Bool → EuclideanSpace ℝ (Fin d) →
      Ω → EuclideanSpace ℝ (Fin d))
    (preliminary estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)) :
    Prop where
  /-- vdV 25.57 assumes the efficient information matrix is nonsingular;
  positive definiteness is the symmetric Gram-matrix form used by the vector API. -/
  hPD : (@efficientInformationMatrix Ω _ P _ Θ _ _ _ d S_theta T_nuis proj e).PosDef
  /-- the displayed density model at `theta0` is the true law `P`. -/
  hP : P = modelMeasure M μ theta0
  /-- `M` consists of probability densities with respect to `μ`. -/
  hPDF : IsPDFOf M μ
  /-- the preliminary estimator is root-`n` bounded in probability. -/
  preliminary_rootN : IsBoundedInProb
    (fun n : ℕ => Measure.pi (fun _ : Fin n => P))
    (fun n X => Real.sqrt n • (preliminary n X - theta0))
  /-- the harmless root-`n` discretization used in vdV's proof. -/
  preliminary_grid : ∀ n, 0 < n → ∀ X, ∃ z : Fin d → ℤ, ∀ j,
    preliminary n X j = (z j : ℝ) / Real.sqrt n
  /-- the score shared by evaluation half `b` is generated only
  from the opposite half.  Joint block independence is then derived from the
  product law rather than postulated coordinate by coordinate. -/
  split_half_locality : ∀ n (X Y : Fin n → Ω) b t,
    (∀ j, splitSide n j ≠ b → X j = Y j) →
      scoreHalf n X b t = scoreHalf n Y b t
  /-- Constitutive (vdV §25.8, (25.55)): every moving-model
  fixed-nuisance efficient score is square-integrable. -/
  scoreLocal_memLp : ∀ t, MemLp (scoreLocal t) 2 (modelMeasure M μ t)
  /-- Constitutive (vdV §25.8, score identity): every moving-model
  fixed-nuisance efficient score has mean zero under its own law. -/
  scoreLocal_centered : ∀ t,
    (∫ x, scoreLocal t x ∂(modelMeasure M μ t)) = 0
  /-- Constitutive (vdV §25.8, (25.55)): each shared estimated
  half-score is square-integrable under the moving law, so its Bochner integral
  cannot collapse to the nonintegrable fallback value. -/
  scoreHalf_memLp : ∀ n X b t,
    MemLp (scoreHalf n X b t) 2 (modelMeasure M μ t)
  /-- first literal clause of (25.55), stated for each of the two
  shared nuisance-score estimates. -/
  condition2555_mean : ∀ thetaSeq, IsRootNBoundedSeq thetaSeq theta0 →
    ∀ b : Bool, TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n •
        ∫ x, scoreHalf n X b (thetaSeq n) x ∂(modelMeasure M μ (thetaSeq n)))
  /-- second literal clause of (25.55), the population `L²`
  distance between the estimated and fixed-nuisance efficient scores. -/
  condition2555_l2 : ∀ thetaSeq, IsRootNBoundedSeq thetaSeq theta0 →
    ∀ b : Bool, TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => ∫ x,
        ‖scoreHalf n X b (thetaSeq n) x - scoreLocal (thetaSeq n) x‖ ^ 2
        ∂(modelMeasure M μ (thetaSeq n)))
  /-- literal weighted-score continuity (25.56). -/
  condition2556 : ∀ thetaSeq, IsRootNBoundedSeq thetaSeq theta0 →
    Tendsto (fun n => ∫ x,
      ‖weightedScore M scoreLocal (thetaSeq n) x -
        M.sqrtDensity theta0 x •
          tupleEval P (fun j =>
            @efficientScore Ω _ P _ Θ _ _ _ S_theta T_nuis proj (e j)) x‖ ^ 2 ∂μ)
      atTop (nhds 0)
  /-- Joint sample/observation measurability of each shared half-score. In
  particular, every fixed-sample and fixed-observation section is measurable. -/
  scoreHalf_joint_meas : ∀ n b t,
    Measurable (fun p : (Fin n → Ω) × Ω => scoreHalf n p.1 b t p.2)
  /-- measurability of the local fixed-nuisance score family. -/
  scoreLocal_meas : ∀ t, Measurable (scoreLocal t)
  /-- measurability of the preliminary estimator. -/
  preliminary_meas : ∀ n, Measurable (preliminary n)
  /-- Constitutive (vdV §25.8 p.393): the literal one-step update, written
  with normalized Gram matrix and score mean. -/
  estimator_def : ∀ n X,
    estimator n X = preliminary n X +
      (empInfo (indexedSplitScore splitSide scoreHalf) n X (preliminary n X))⁻¹.mulVecLin
        (scoreMean (indexedSplitScore splitSide scoreHalf) n X (preliminary n X))

end AsymptoticStatistics.Asymptotics.OneStepVec
