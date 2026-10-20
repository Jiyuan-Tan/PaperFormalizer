module
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScoreVec
public import StatLean.AsymptoticStatistics.Core.EfficiencyOperationalVec

@[expose] public section

/-!
# Z-estimator semiparametric efficiency — vector parameter

Vector-parameter (`θ ∈ ℝᵈ`) counterpart of
`AsymptoticStatistics.Asymptotics.ZEstimator`. The Z-estimator solves a
vector estimating equation `P_n ψ̂_n(·, θ̂_n) ≈ 0`; under the no-bias
condition (25.52) and the Donsker condition (25.53), `θ̂_n` is
asymptotically linear with the vector influence function `Ĩ⁻¹ ℓ̃` and
asymptotically efficient.

The structure field `asympLinear_25_54_vec` records the vector
asymptotic-linear premise consumed by the efficiency assembly. The
discharge layer separately derives the corresponding expansion from
native vector Taylor primitives.

Reference: vdV §25.5, thm:25.54 (vector form).

Headline declarations: `zEstimator_semiparametricallyEfficient_vec`,
`zEstimator_biasResidual_expansion_vec`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.ZEstimatorVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec

variable {Ω : Type*} [MeasurableSpace Ω]
variable {d : ℕ}

/-- *Bundled assumptions for vdV thm:25.54 (Z-estimator semiparametric
efficiency, vector parameter).*

Structure parameters carry the model identity (score operator `S_θ`,
nuisance tangent space `T_nuis`, parameter directions `e : Fin d → Θ`,
target tangent space `T`, vector derivative `Dψ`, estimator sequence
`estimator`, vector centering `θ₀`); the body bundles the vector-EIF
construction hypotheses (`hPD`, `h_mem`, `h_Dψ`) and the vector
asymptotic-linear expansion (`asympLinear_25_54_vec`).

Reference: vdV §25.5, thm:25.54 (vector form). -/
structure EfficientScoreEqAssumptions_vec
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (e : Fin d → Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P)) (Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d))
    (estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (θ₀ : EuclideanSpace ℝ (Fin d)) where
  /-- vdV §25.4 (lem:25.25): the efficient information matrix `Ĩ` is
  positive-definite (identifiability / non-degeneracy). -/
  hPD : (efficientInformationMatrix S_θ T_nuis e).PosDef
  /-- vdV §25.4 (lem:25.25): each component of the candidate vector EIF
  `IF j = Σₖ (Ĩ⁻¹)ⱼₖ • ℓ̃(eₖ)` lies in the target tangent space `T`. -/
  h_mem : ∀ j, candidateVecEIF S_θ T_nuis e j ∈ T
  /-- vdV §25.4 (lem:25.25): the `j`-th coordinate functional of `Dψ`
  acts on `T` as `⟪IF j, ·⟫`. -/
  h_Dψ : ∀ (j : Fin d) (g : T),
    (EuclideanSpace.proj j ∘L Dψ) g
      = ⟪candidateVecEIF S_θ T_nuis e j, (g : ↥(L2ZeroMean P))⟫_ℝ
  /-- vdV §25.5 (eqs:25.52 + 25.53 + estimating equation): the
  Z-estimator is asymptotically linear at `P` with vector influence tuple
  `IF` and vector centering `θ₀`. -/
  asympLinear_25_54_vec :
    AsymptoticallyLinearAt_vec estimator P
      (candidateVecEIF S_θ T_nuis e) θ₀

/-- *vdV thm:25.54 — Z-estimator semiparametric efficiency (vector
parameter).*

If the bundled `EfficientScoreEqAssumptions_vec` holds and the vector
centering equals `ψ P`, then `estimator` is semiparametrically efficient
at `P` for the vector functional `ψ` relative to `T`.

Reference: vdV §25.5, thm:25.54 (vector form).

Proof (3-step, mirroring the scalar template):
* **Step A** — produce the vector EIF via `eif_from_efficientScore_vec`.
* **Step B** — unwrap the bundled vector AL expansion (modulo `ψ P = θ₀`).
* **Step C** — combine via
  `estimator_semiparametricallyEfficient_of_asympLinear_eif_vec`. -/
theorem zEstimator_semiparametricallyEfficient_vec
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {e : Fin d → Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {θ₀ : EuclideanSpace ℝ (Fin d)}
    (h : EfficientScoreEqAssumptions_vec P Θ S_θ T_nuis e T Dψ estimator θ₀)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt_vec estimator ψ P T := by
  -- Step A: the strict-model vec layer produces the vector EIF.
  have hEIF : IsEfficientInfluenceFunction_vec Dψ
      (candidateVecEIF S_θ T_nuis e) :=
    eif_from_efficientScore_vec S_θ T_nuis e T Dψ h.hPD h.h_mem h.h_Dψ
  -- Step B: the bundled vector AL expansion (modulo `ψ P = θ₀`).
  have hAL : AsymptoticallyLinearAt_vec estimator P
      (candidateVecEIF S_θ T_nuis e) (ψ P) := by
    rw [h_ψ]; exact h.asympLinear_25_54_vec
  -- Step C: combine via the operational-form vector lemma.
  exact estimator_semiparametricallyEfficient_of_asympLinear_eif_vec hEIF hAL

/-! ### Bias-residual variant — vdV thm:25.59 (vector parameter) -/

/-- *Bundled assumptions for vdV thm:25.59 (Z-estimator bias-residual
expansion, vector parameter).*

Differs from `EfficientScoreEqAssumptions_vec` by dropping the no-bias
condition (25.52) and bundling `AsymptoticallyLinearWithBiasAt_vec`
(retaining the vector bias-residual `bias`) instead of
`AsymptoticallyLinearAt_vec`.

Reference: vdV §25.5, thm:25.59 (vector form). -/
structure EfficientScoreEqBiasResidualAssumptions_vec
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (e : Fin d → Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P)) (Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d))
    (estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (bias : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (θ₀ : EuclideanSpace ℝ (Fin d)) where
  /-- vdV §25.4 (lem:25.25): `Ĩ` positive-definite. -/
  hPD : (efficientInformationMatrix S_θ T_nuis e).PosDef
  /-- vdV §25.4 (lem:25.25): each `IF j ∈ T`. -/
  h_mem : ∀ j, candidateVecEIF S_θ T_nuis e j ∈ T
  /-- vdV §25.4 (lem:25.25): `Dψ`'s `j`-th coordinate acts as `⟪IF j, ·⟫`. -/
  h_Dψ : ∀ (j : Fin d) (g : T),
    (EuclideanSpace.proj j ∘L Dψ) g
      = ⟪candidateVecEIF S_θ T_nuis e j, (g : ↥(L2ZeroMean P))⟫_ℝ
  /-- vdV §25.5 (eq:25.53 + estimating equation, **omitting** 25.52): the
  vector bias-residual expansion holds with the supplied `bias`. -/
  asympLinear_25_59_vec :
    AsymptoticallyLinearWithBiasAt_vec estimator P
      (candidateVecEIF S_θ T_nuis e) θ₀ bias

/-- *vdV thm:25.59 — Z-estimator bias-residual expansion (vector
parameter).*

If the bundled `EfficientScoreEqBiasResidualAssumptions_vec` holds, then
the Z-estimator satisfies the vector bias-residual expansion. Combined
with the operational lemma
`estimator_semiparametricallyEfficient_of_asympLinear_eif_vec`, this
formalises the necessity of (25.52) for vector semiparametric efficiency.

Reference: vdV §25.5, thm:25.59 (vector form).

Proof: unwrap `asympLinear_25_59_vec` directly. -/
theorem zEstimator_biasResidual_expansion_vec
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {e : Fin d → Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {bias : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {θ₀ : EuclideanSpace ℝ (Fin d)}
    (h : EfficientScoreEqBiasResidualAssumptions_vec
            P Θ S_θ T_nuis e T Dψ estimator bias θ₀) :
    AsymptoticallyLinearWithBiasAt_vec estimator P
      (candidateVecEIF S_θ T_nuis e) θ₀ bias :=
  h.asympLinear_25_59_vec

/-- *Recovery: vector thm:25.54 = vector thm:25.59 with vanishing bias.*
When the bias-residual sequence is identically zero, the bias-residual
bundle reduces to the standard `EfficientScoreEqAssumptions_vec`.

Reference: vdV §25.5, the (25.52)-collapse step (vector form). -/
def EfficientScoreEqBiasResidualAssumptions_vec.toEfficientScoreEqAssumptions_vec
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {e : Fin d → Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {θ₀ : EuclideanSpace ℝ (Fin d)}
    (h : EfficientScoreEqBiasResidualAssumptions_vec
            P Θ S_θ T_nuis e T Dψ estimator (fun _ _ => 0) θ₀) :
    EfficientScoreEqAssumptions_vec P Θ S_θ T_nuis e T Dψ estimator θ₀ where
  hPD := h.hPD
  h_mem := h.h_mem
  h_Dψ := h.h_Dψ
  asympLinear_25_54_vec :=
    (asympLinearWithBiasAt_vec_zero_iff_asympLinearAt_vec _ _ _ _).mp
      h.asympLinear_25_59_vec

end AsymptoticStatistics.Asymptotics.ZEstimatorVec
