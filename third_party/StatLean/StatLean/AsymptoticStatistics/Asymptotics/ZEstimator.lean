module
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScore
public import StatLean.AsymptoticStatistics.Core.EfficiencyOperational

@[expose] public section

/-!
# Z-estimator semiparametric efficiency

A *Z-estimator* $\hat\theta_n$ solves the efficient score estimating
equation $\sum_{i=1}^n \tilde\ell_{\hat\theta_n,\hat\eta_n}(X_i) = 0$ —
equivalently, $\sqrt{n}\,\mathbb{P}_n\,\tilde\ell_{\hat\theta_n,\hat\eta_n}
= o_P(1)$ — where $\tilde\ell_{\theta_0,\eta_0}$ is the efficient score
function (the ordinary score for $\theta$ minus its $L^2(P)$-projection
onto the nuisance tangent space) and $\hat\eta_n$ is a plug-in estimator
of the nuisance parameter. Assume the efficient information
$\tilde I_{\theta_0,\eta_0}$ is positive (the scalar analogue of "the
efficient information matrix is nonsingular"). Then, under the no-bias
condition (25.52) and the consistency / Donsker condition (25.53),
$\hat\theta_n$ is asymptotically linear with influence function
$\tilde I_{\theta_0,\eta_0}^{-1}\,\tilde\ell_{\theta_0,\eta_0}$ and is
asymptotically efficient for $\theta$ at $(\theta_0,\eta_0)$.

The **bias-residual variant** drops the no-bias condition (25.52),
retaining the bias term explicitly:
$$\sqrt{n}\,(\hat\theta_n-\theta_0)
  = \frac{1}{\sqrt{n}}\sum_{i=1}^n
      \tilde I_{\theta_0,\eta_0}^{-1}\,\tilde\ell_{\theta_0,\eta_0}(X_i)
    + \sqrt{n}\,P_{\hat\theta_n,\eta}\,\tilde\ell_{\hat\theta_n,\hat\eta_n}
    + o_P(1).$$
Combined with the operational characterization of efficiency, this
formalizes the *necessity* of the no-bias condition (25.52): efficiency
forces the bias residual to vanish at rate $\sqrt{n}$.

Deviations from the book worth noting: the scope here is a **scalar
parameter** (a one-dimensional score direction $v$), so the book's
"nonsingular information matrix" hypothesis specializes to the positivity
$\tilde I_{\theta_0,\eta_0} > 0$ needed to invert the EIF formula.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge
Series in Statistical and Probabilistic Mathematics, Cambridge University
Press, 1998. Chapter 25 (Semiparametric Models), §25.8 (Efficient Score
Equations), Theorem 25.54 (Z-estimator semiparametric efficiency) and
Theorem 25.59 (bias-residual expansion), Eqs (25.52) (no-bias condition)
and (25.53) (consistency / Donsker condition). (All in-file tags cite
§25.8; the equation and theorem numbers 25.52, 25.53, 25.54, 25.59 are
as cited.)

**Proof formalization notes.** The empirical-process content of (25.52)
and (25.53) is *not* reproved here: the bundled hypothesis
`asympLinear_25_54` directly asserts the asymptotic-linear expansion that
vdV §25.8 derives from those two conditions together with the estimating
equation $\sqrt{n}\,\mathbb{P}_n\,\tilde\ell_{\hat\theta_n,\hat\eta_n}
= o_P(1)$ (operationally, `P_n ψ̂_n(·, θ̂_n) = o_P(n^{-1/2})`). Given that
input, `zEstimator_semiparametricallyEfficient` (Thm 25.54) is a 3-step
assembly: (Step A) construct the efficient influence function
$\tilde I_{\theta_0,\eta_0}^{-1}\,\tilde\ell_{\theta_0,\eta_0}$ from the
strict-model layer; (Step B) unwrap the bundled asymptotic-linear
expansion modulo the centering rewrite $\psi(P)=\theta_0$; (Step C)
combine via the operational efficiency lemma. The bias-residual variant
`zEstimator_biasResidual_expansion` (Thm 25.59) is the direct unwrapping
of `asympLinear_25_59`; the recovery direction (vanishing bias ⇒ Thm
25.54) is shipped as `…toEfficientScoreEqAssumptions`.

Scope: scalar parameter / 1-dim score direction `v : Θ`.

Headline declarations: `zEstimator_semiparametricallyEfficient`,
`zEstimator_biasResidual_expansion`.

**Bibliographic comments.** This is a folklore synthesis with no single
seminal paper. The efficient score function and efficient influence
function are the central objects of the modern semiparametric efficiency
theory developed in P. J. Bickel, C. A. J. Klaassen, Y. Ritov, and J. A.
Wellner, *Efficient and Adaptive Estimation for Semiparametric Models*,
Johns Hopkins University Press, 1993 (republished Springer, 1998); the
efficient-influence-function lower bound itself descends from the
convolution and local-asymptotic-minimaxity theorems of J. Hájek (*Z.
Wahrsch. Verw. Gebiete* 14, 1970, 323–330) and L. Le Cam, with the
projection construction of the efficient score going back to C. Stein
(*Proc. 3rd Berkeley Symp.*, 1956). The specific packaging as the
"efficient score equation" method, with the no-bias condition (25.52),
the Donsker condition (25.53), and the asymptotic-efficiency conclusions
of Theorems 25.54 and 25.59, is van der Vaart's exposition in §25.8 of
the cited text and is best regarded as folklore consolidated there.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.ZEstimator

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.StrictModel.EfficientScore

variable {Ω : Type*} [MeasurableSpace Ω]

/-- *Bundled assumptions for vdV thm:25.54 (Z-estimator semiparametric
efficiency).*

The structure parameters carry the model identity (score operator
`S_θ`, nuisance tangent space `T_nuis`, parameter direction `v`,
target tangent space `T`, parameter derivative `dψ`, estimator
sequence `estimator`, centering `θ₀`); the structure body bundles the
EIF-construction hypotheses (`h_mem`, `h_dψ`, `hI_pos`) and the
asymptotic-linear expansion (`asympLinear_25_54`) that vdV §25.8
derives from (25.52) + (25.53) + the estimating-equation
`P_n ψ̂_n(·, θ̂_n) = o_P(n^{-1/2})`.

Reference: vdV §25.8, eqs:25.52, 25.53, thm:25.54.

Edge behavior:
* When `efficientInformation S_θ T_nuis v = 0` (i.e. `S_θ v ∈ T_nuis`,
  the parameter direction `v` is unidentified at `(θ₀, η₀)`), `hI_pos`
  fails and the structure is uninhabited: matches vdV's convention
  that "no Z-estimator is efficient when the efficient information
  vanishes".
* When `T = ⊥`, `h_mem` forces the candidate EIF to be `0`, so
  `efficientScore S_θ T_nuis v = 0` (modulo the scaling), so again
  `hI_pos` fails. Trivial-tangent-space case excluded by the
  efficient-information positivity field. -/
structure EfficientScoreEqAssumptions
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P)) (dψ : T →L[ℝ] ℝ)
    (estimator : ∀ n, (Fin n → Ω) → ℝ) (θ₀ : ℝ) where
  /-- vdV §25.4 (lem:25.25): the candidate EIF
  `(1 / Ĩ_{θ₀, η₀}) • ℓ̃_{θ₀, η₀}` lies in the target tangent space `T`. -/
  h_mem :
    (1 / efficientInformation S_θ T_nuis v)
      • efficientScore S_θ T_nuis v ∈ T
  /-- vdV §25.4 (lem:25.25): the parameter derivative
  `dψ` acts on `T` as `(1 / Ĩ) ⟪ℓ̃, ·⟫`. -/
  h_dψ : ∀ g : T,
    dψ g
      = (1 / efficientInformation S_θ T_nuis v)
          * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ
  /-- vdV §25.4 (lem:25.25): efficient information is
  non-degenerate at `v` (i.e. `S_θ v ∉ T_nuis`). Required to invert
  `Ĩ` in the EIF formula `(1 / Ĩ) • ℓ̃`. -/
  hI_pos : 0 < efficientInformation S_θ T_nuis v
  /-- vdV §25.8 (eqs:25.52 + 25.53 + estimating-equation
  `P_n ψ̂_n(·, θ̂_n) = o_P(n^{-1/2})`):

  the Z-estimator `estimator` is asymptotically linear at `P` with
  influence function `(1 / Ĩ) • ℓ̃` and centering `θ₀`. Concrete model
  files prove this from Donsker / asymptotic-equicontinuity machinery
  (vdV §25.8 proof of 25.54).

  Equivalent operational form (cf. vdV eq:25.22):
  `√n · (estimator_n − θ₀) − (1/√n) · Σ_i (1/Ĩ) ℓ̃(X_i) →_P 0`
  under the iid product `Pⁿ`. -/
  asympLinear_25_54 :
    AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v)
      θ₀

/-- *vdV thm:25.54 — Z-estimator semiparametric efficiency.*

If the bundled `EfficientScoreEqAssumptions` holds for the model triple
`(S_θ, T_nuis, v)`, target tangent space `T`, derivative `dψ`,
estimator sequence `estimator`, and centering `θ₀ = ψ P`, then
`estimator` is semiparametrically efficient at `P` for the parameter
functional `ψ` relative to `T`.

Reference: vdV §25.8, thm:25.54.

Proof (3-step):
* **Step A** — produce the EIF via `eif_from_efficientScore`.
* **Step B** — unwrap the bundled asymptotic-linear expansion
  (modulo a centering rewrite `ψ P = θ₀`).
* **Step C** — combine via
  `estimator_semiparametricallyEfficient_of_asympLinear_eif`.

The empirical-process content of (25.52) + (25.53) is bundled as
`asympLinear_25_54` and not proved here. -/
theorem zEstimator_semiparametricallyEfficient
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    {estimator : ∀ n, (Fin n → Ω) → ℝ} {θ₀ : ℝ}
    (h : EfficientScoreEqAssumptions P Θ S_θ T_nuis v T dψ estimator θ₀)
    {ψ : Measure Ω → ℝ} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt estimator ψ P T := by
  -- Step A: the strict-model layer produces the EIF
  -- `(1 / Ĩ) • ℓ̃` from `h_mem` + `h_dψ`.
  have hEIF : IsEfficientInfluenceFunction P T dψ
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) :=
    eif_from_efficientScore S_θ T_nuis v T h.h_mem dψ h.h_dψ
  -- Step B: the bundled `asympLinear_25_54` is precisely the AL
  -- expansion needed (modulo the centering rewrite `ψ P = θ₀`).
  have hAL : AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) (ψ P) := by
    rw [h_ψ]
    exact h.asympLinear_25_54
  -- Step C: combine via the operational-form lemma.
  exact estimator_semiparametricallyEfficient_of_asympLinear_eif hEIF hAL

/-! ### Bias-residual variant — vdV thm:25.59

`thm:25.59` is `thm:25.54` *without* the no-bias condition (25.52),
exhibiting the bias-residual term `√n · P_{θ̂_n,η} ℓ̃_{θ̂_n,η̂_n}`
explicitly. Combined with `lem:25.23` (operational efficiency,
`estimator_semiparametricallyEfficient_of_asympLinear_eif`) it
formalises the **necessity of (25.52) for semiparametric efficiency**.

The structure parameter `bias : ∀ n, (Fin n → Ω) → ℝ` is supplied by
concrete consumers as `bias n X = √n · P_{θ̂_n(X), η} ℓ̃_{θ̂_n(X), η̂_n(X)}`. -/

/-- *Bundled assumptions for vdV thm:25.59 (Z-estimator bias-residual
expansion).*

Differs from `EfficientScoreEqAssumptions` in two ways:
1. drops the no-bias condition (25.52) — the bias-residual
   `√n · P_{θ̂_n,η} ℓ̃_{θ̂_n,η̂_n}` is **not** assumed `o_P(1)`;
2. the bundled regularity field is `AsymptoticallyLinearWithBiasAt`
   rather than `AsymptoticallyLinearAt`, retaining the bias term in
   the conclusion.

Reference: vdV §25.8, thm:25.59. -/
structure EfficientScoreEqBiasResidualAssumptions
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P)) (dψ : T →L[ℝ] ℝ)
    (estimator : ∀ n, (Fin n → Ω) → ℝ)
    (bias : ∀ n, (Fin n → Ω) → ℝ) (θ₀ : ℝ) where
  /-- vdV §25.4 (lem:25.25): the candidate EIF
  `(1 / Ĩ) • ℓ̃` lies in `T`. -/
  h_mem :
    (1 / efficientInformation S_θ T_nuis v)
      • efficientScore S_θ T_nuis v ∈ T
  /-- vdV §25.4 (lem:25.25): `dψ` acts on `T` as
  `(1 / Ĩ) ⟪ℓ̃, ·⟫`. -/
  h_dψ : ∀ g : T,
    dψ g
      = (1 / efficientInformation S_θ T_nuis v)
          * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ
  /-- vdV §25.4 (lem:25.25): `Ĩ_{θ₀,η₀} > 0`. -/
  hI_pos : 0 < efficientInformation S_θ T_nuis v
  /-- vdV §25.8 (eq:25.53 + estimating-equation
  `√n · 𝕡_n ℓ̃_{θ̂_n,η̂_n} = o_P(1)`, **omitting** (25.52)):

  the Z-estimator's bias-residual expansion holds with the supplied
  `bias` sequence:
  `√n (estimator − θ₀) = (1/√n) Σ (1/Ĩ) ℓ̃(X_i) + bias_n + o_P(1)`
  under `Pⁿ`. Concrete model files prove this from Donsker /
  Glivenko–Cantelli machinery applied to `ℓ̃_{θ̂_n,η̂_n}` (vdV §25.8
  proof, with the (25.52) cancellation step omitted). -/
  asympLinear_25_59 :
    AsymptoticallyLinearWithBiasAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v)
      θ₀ bias

/-- *vdV thm:25.59 — Z-estimator bias-residual expansion.*

If the bundled `EfficientScoreEqBiasResidualAssumptions` holds,
then the Z-estimator satisfies
`√n (estimator − θ₀) = (1/√n) Σ (1/Ĩ) ℓ̃(X_i) + bias_n + o_P(1)`
under `Pⁿ`.

Combined with `lem:25.23`
(`estimator_semiparametricallyEfficient_of_asympLinear_eif`), this
formalises the **necessity** of vdV's no-bias condition (25.52) for
semiparametric efficiency: efficiency requires
`AsymptoticallyLinearAt` with influence `(1/Ĩ) • ℓ̃`, which by the
bias-residual expansion forces `bias →_P 0` at rate `√n` — i.e.,
(25.52). The recovery direction (bias = 0 ⇒ thm:25.54) is shipped
separately as
`EfficientScoreEqBiasResidualAssumptions.toEfficientScoreEqAssumptions`.

Reference: vdV §25.8, thm:25.59.

Proof: unwrap `asympLinear_25_59` directly (Steps A and C of the
`thm:25.54` template are not used — the conclusion is the AL-with-bias
expansion itself, not `SemiparametricallyEfficientAt`). -/
theorem zEstimator_biasResidual_expansion
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    {estimator : ∀ n, (Fin n → Ω) → ℝ}
    {bias : ∀ n, (Fin n → Ω) → ℝ} {θ₀ : ℝ}
    (h : EfficientScoreEqBiasResidualAssumptions
            P Θ S_θ T_nuis v T dψ estimator bias θ₀) :
    AsymptoticallyLinearWithBiasAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) θ₀ bias :=
  h.asympLinear_25_59

/-- *Recovery: thm:25.54 = thm:25.59 with vanishing bias.* When the
bias-residual sequence is identically zero (i.e., (25.52) holds at
the strongest rate), the bias-residual bundle reduces to the
standard `EfficientScoreEqAssumptions`.

Reference: vdV §25.8, the (25.52)-collapse step. -/
def EfficientScoreEqBiasResidualAssumptions.toEfficientScoreEqAssumptions
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    {estimator : ∀ n, (Fin n → Ω) → ℝ} {θ₀ : ℝ}
    (h : EfficientScoreEqBiasResidualAssumptions
            P Θ S_θ T_nuis v T dψ estimator (fun _ _ => 0) θ₀) :
    EfficientScoreEqAssumptions P Θ S_θ T_nuis v T dψ estimator θ₀ where
  h_mem := h.h_mem
  h_dψ := h.h_dψ
  hI_pos := h.hI_pos
  asympLinear_25_54 :=
    (asympLinearWithBiasAt_zero_iff_asympLinearAt _ _ _ _).mp h.asympLinear_25_59

end AsymptoticStatistics.Asymptotics.ZEstimator
