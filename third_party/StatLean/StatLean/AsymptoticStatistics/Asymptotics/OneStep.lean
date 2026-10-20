module
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScore
public import StatLean.AsymptoticStatistics.Core.EfficiencyOperational

@[expose] public section

/-!
# One-step estimator semiparametric efficiency

Given a $\sqrt{n}$-consistent preliminary (initial) estimator $\tilde\theta_n$, the
*one-step estimator* is
$$\hat\theta_n \;=\; \tilde\theta_n \;+\; \frac{1}{n}\sum_{i=1}^n \hat I_n^{-1}\,
  \hat\ell_n(X_i,\tilde\theta_n),$$
where $\hat\ell_n$ estimates the efficient score function $\tilde\ell_{\theta,\eta}$ and
$\hat I_n$ estimates the efficient information $\tilde I_{\theta,\eta}$. This is one
Newton–Raphson step toward solving the efficient score equation
$\sum_i \tilde\ell_{\theta,\eta}(X_i)=0$ starting from $\tilde\theta_n$. Under the
score-consistency condition (Eq. (25.55)) and the no-bias / negligible-remainder condition
(Eq. (25.56)) — with the efficient information assumed nonsingular — the estimator
$\hat\theta_n$ is asymptotically linear at $P$ with influence function
$(1/\tilde I)\,\tilde\ell$ and is asymptotically (semiparametrically) efficient.

This formalization works with a scalar parameter and a one-dimensional score direction, so
the nonsingular efficient information matrix becomes the positivity hypothesis
$\tilde I > 0$. The Lean bundle additionally fixes the algebraic shape of the one-step update
(an unnumbered display preceding Eq. (25.55)) and carries the empirical-process conclusion (asymptotic linearity) as a single
bundled hypothesis, since the underlying Donsker / Glivenko–Cantelli machinery is out of scope
here; see the formalization notes below.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 25 (Semiparametric
Models), §25.8 (Efficient Score Equations), Theorem 25.57, Eqs. (25.55), (25.56).

**Proof formalization notes.**
Headline declarations: `OneStepAssumptions`, `oneStep_semiparametricallyEfficient`.
Scope: scalar parameter / 1-dim score direction, matching `SemiparametricallyEfficientAt`
and `eif_from_efficientScore`.

The empirical-process content of (25.55) + (25.56) together with the $\sqrt n$-rate of the
preliminary estimator and the information consistency $\hat I_n \to_P \tilde I$ is bundled as
the structure field `asympLinear_25_57` and is not reproved here; concrete model files
discharge it from Donsker / Glivenko–Cantelli arguments applied to the score estimate together
with the one-step formula. The one-step update (an unnumbered display preceding (25.55)) is bundled as `estimator_def`; its role
is to shape `asympLinear_25_57` for downstream consumers, so it is not consumed in the proof of
the headline theorem itself. The book's sample-splitting (half-sample) trick and the grid
discretization of $\tilde\theta_n$ are proof devices used to discharge `asympLinear_25_57`, not
separate book theorems. The headline proof then runs in three steps: (A) build the efficient
influence function via `eif_from_efficientScore`; (B) unwrap `asympLinear_25_57` modulo
$\psi(P)=\theta_0$; (C) combine via
`estimator_semiparametricallyEfficient_of_asympLinear_eif`.

**Bibliographic comments.**
The one-step / Newton–Raphson construction with grid-discretized initial estimators
originates with L. Le Cam, "On the asymptotic theory of estimation and testing hypotheses",
*Proceedings of the Third Berkeley Symposium on Mathematical Statistics and Probability*,
Vol. 1, University of California Press, 1956, pp. 129–156, where discretization is used to turn
a $\sqrt n$-consistent preliminary estimator into an efficient one. The semiparametric form
formalized here — efficient score / efficient information, the no-bias condition, and the
sample-splitting device — is developed in P. J. Bickel, C. A. J. Klaassen, Y. Ritov, and
J. A. Wellner, *Efficient and Adaptive Estimation for Semiparametric Models*, Johns Hopkins
University Press, 1993; van der Vaart's Theorem 25.57 is a streamlined account of that theory.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.OneStep

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.StrictModel.EfficientScore

variable {Ω : Type*} [MeasurableSpace Ω]

/-- *Bundled assumptions for vdV thm:25.57 (one-step semiparametric
efficiency).*

Structure parameters: model identity (`S_θ`, `T_nuis`, `v`, `T`, `dψ`)
+ estimator triple (`preliminary`, `score_estimate_seq`,
`info_estimate_seq`) + the one-step combined estimator + centering
`θ₀`. Structure body: the EIF hypotheses + the one-step formula
identity (`estimator_def`) + the empirical-process consequence
(`asympLinear_25_57`).

Reference: vdV §25.8 (Efficient Score Equations), eqs:25.55, 25.56, thm:25.57.

Edge behavior:
* `efficientInformation = 0` ⇒ `hI_pos` fails ⇒ uninhabited (matches
  the standard non-degeneracy convention).
* `info_estimate_seq` having a different limit than `Ĩ` would falsify
  `asympLinear_25_57` rather than the bundle being uninhabited;
  encoded as a downstream-discharged constraint, not a structure
  field. -/
structure OneStepAssumptions
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P)) (dψ : T →L[ℝ] ℝ)
    (preliminary : ∀ n, (Fin n → Ω) → ℝ)
    (score_estimate_seq : ℕ → Ω → ℝ → ℝ)
    (info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ)
    (estimator : ∀ n, (Fin n → Ω) → ℝ) (θ₀ : ℝ) where
  /-- vdV §25.4 (lem:25.25): the candidate EIF
  `(1 / Ĩ) • ℓ̃` lies in the target tangent space `T`. -/
  h_mem :
    (1 / efficientInformation S_θ T_nuis v)
      • efficientScore S_θ T_nuis v ∈ T
  /-- vdV §25.4 (lem:25.25): `dψ` acts on `T` as
  `(1 / Ĩ) ⟪ℓ̃, ·⟫`. -/
  h_dψ : ∀ g : T,
    dψ g
      = (1 / efficientInformation S_θ T_nuis v)
          * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ
  /-- vdV §25.4 (lem:25.25): efficient information is
  positive at `v`. -/
  hI_pos : 0 < efficientInformation S_θ T_nuis v
  /-- vdV §25.8 (the one-step update; an unnumbered display preceding
  eq:25.55): the one-step estimator is the
  preliminary plus the empirical correction
  `θ̂_n = θ̃_n + (1/n) · Σ_i Î_n⁻¹ · ℓ̂_n(X_i, θ̃_n)`. Pinning the
  formula in the bundle lets `asympLinear_25_57` reference a known
  algebraic shape, and lets concrete model files prove the AL
  expansion by a one-step Taylor argument on this exact form. -/
  estimator_def : ∀ n (X : Fin n → Ω),
    estimator n X
      = preliminary n X
        + (info_estimate_seq n X)⁻¹
            * ((n : ℝ)⁻¹ * (∑ i, score_estimate_seq n (X i) (preliminary n X)))
  /-- vdV §25.8 (eqs:25.55 + 25.56 + `√n`-rate of the preliminary
  + information consistency `Î_n →_P Ĩ`):

  the one-step estimator `estimator` is asymptotically linear at `P`
  with influence function `(1 / Ĩ) • ℓ̃` and centering `θ₀`. Concrete
  model files prove this from Donsker / Glivenko–Cantelli machinery
  applied to `score_estimate_seq` together with the one-step
  `estimator_def`; the consequence is bundled as a single hypothesis
  to keep the empirical-process layer out of scope.

  Sample-splitting (the half-sample trick) is a proof technique used
  to discharge this field; it is not a separate book theorem. -/
  asympLinear_25_57 :
    AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v)
      θ₀

/-- *vdV thm:25.57 — one-step semiparametric efficiency.*

If the bundled `OneStepAssumptions` holds for the model triple
`(S_θ, T_nuis, v)`, target tangent space `T`, derivative `dψ`, the
preliminary / score / information estimator triple
`(preliminary, score_estimate_seq, info_estimate_seq)`, the combined
one-step estimator `estimator`, and centering `θ₀ = ψ P`, then
`estimator` is semiparametrically efficient at `P` for the parameter
functional `ψ` relative to `T`.

Reference: vdV §25.8 (Efficient Score Equations), thm:25.57. Sample-splitting is the proof
technique behind the bundled `asympLinear_25_57`, not a separate
theorem.

Proof template:
* **Step A**: produce the EIF via `eif_from_efficientScore`.
* **Step B**: unwrap `asympLinear_25_57` modulo `ψ P = θ₀`.
* **Step C**: combine via
  `estimator_semiparametricallyEfficient_of_asympLinear_eif`.

The empirical-process content of (25.55) + (25.56) + the
preliminary's `√n`-rate is bundled as `asympLinear_25_57` and not
proved here; the one-step update formula (an unnumbered display
preceding `eq:25.55`) is bundled as
`estimator_def` and likewise not used in this proof (its role is to
shape `asympLinear_25_57` for downstream consumers). -/
theorem oneStep_semiparametricallyEfficient
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    {preliminary : ∀ n, (Fin n → Ω) → ℝ}
    {score_estimate_seq : ℕ → Ω → ℝ → ℝ}
    {info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ}
    {estimator : ∀ n, (Fin n → Ω) → ℝ} {θ₀ : ℝ}
    (h : OneStepAssumptions P Θ S_θ T_nuis v T dψ
            preliminary score_estimate_seq info_estimate_seq estimator θ₀)
    {ψ : Measure Ω → ℝ} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt estimator ψ P T := by
  have hEIF : IsEfficientInfluenceFunction P T dψ
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) :=
    eif_from_efficientScore S_θ T_nuis v T h.h_mem dψ h.h_dψ
  have hAL : AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) (ψ P) := by
    rw [h_ψ]
    exact h.asympLinear_25_57
  exact estimator_semiparametricallyEfficient_of_asympLinear_eif hEIF hAL

end AsymptoticStatistics.Asymptotics.OneStep
