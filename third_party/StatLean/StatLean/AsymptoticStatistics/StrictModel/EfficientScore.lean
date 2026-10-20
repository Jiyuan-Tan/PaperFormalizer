module
public import StatLean.AsymptoticStatistics.Core.EIF

@[expose] public section

/-!
# Efficient score for strict `(θ, η)` semiparametric models

This file develops the ordinary score, nuisance tangent space, efficient
score, and efficient information for classical `(θ, η)` semiparametric
models, culminating in the 1-dimensional form of the efficient-score
characterization of the efficient influence function (van der Vaart,
Lemma 25.25): the normalized efficient score is an efficient influence
function for a linear functional of `θ`.

In standard notation, for a model `\{P_{\theta,\eta}\}` with finite-dimensional
parameter `\theta` and infinite-dimensional nuisance `\eta`, let
`\dot\ell_\theta` be the ordinary score for `\theta` and let `\dot{\mathcal P}_\eta`
denote the nuisance tangent space (the closed linear span in `L^2_0(P)` of the
nuisance scores). The **efficient score** in direction `v` is the residual of
the ordinary score after projecting out the nuisance directions,
`\tilde\ell_{\theta,v} = \dot\ell_\theta v - \Pi(\dot\ell_\theta v \mid \dot{\mathcal P}_\eta)`,
and the **efficient information** is `\tilde I_v = \lVert \tilde\ell_{\theta,v}\rVert_{L^2(P)}^2`.
The lemma states that, whenever `\tilde I_v \neq 0`, the function
`\tilde I_v^{-1}\,\tilde\ell_{\theta,v}` is the efficient influence function for the
real-valued functional `\psi(P_{\theta,\eta}) = \langle v, \theta\rangle`, i.e. the
estimator achieving the semiparametric efficiency bound for that functional.

The 1-dim restriction (a linear functional of `θ` in a single direction
`v`) keeps the API inside the abstract EIF framework's derivative form
`dψ : T →L[ℝ] ℝ`; the multivariate version replaces `\tilde I_v` by the
efficient information matrix `\tilde I = \langle\tilde\ell_{\theta,i},\tilde\ell_{\theta,j}\rangle`
and the candidate by `\tilde I^{-1}\tilde\ell_\theta`.

Headline declaration: `eif_from_efficientScore`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series
in Statistical and Probabilistic Mathematics, Cambridge University Press,
1998, Chapter 25 (Semiparametric Models), §25.4 (Score and Information
Operators), Lemma 25.25.

**Proof formalization notes.** The 1-dim restriction (linear functional of
`θ` in a single direction `v`) keeps the API inside the abstract EIF
framework's `dψ : T →L[ℝ] ℝ` form. The headline theorem reduces to the
abstract `eif_of_representation_and_membership` by checking two conditions on
the candidate `IF := (1/I_eff(v)) • S_eff(v)`: (1) membership `IF ∈ T`,
supplied as the hypothesis `h_mem` (assumes the ambient tangent space `T` is
large enough to contain the efficient score residual); and (2) the
influence-function representation, supplied as `h_dψ`, which passes `dψ`
already evaluated as `dψ g = (1/I_eff(v)) ⟪S_eff(v), g⟫` for every `g ∈ T`.
The orthogonality used in the informal derivation — `⟪S_eff(v), g_η⟫ = 0` for
nuisance directions `g_η ∈ T_nuis`, since the efficient score is by
construction the orthogonal residual of the ordinary score — is built into
the definition of `efficientScore` via `starProjection`. Edge behavior: when
the ordinary score `S_θ v` already lies in the nuisance tangent space the
efficient score vanishes, `I_eff(v) = 0`, and the non-degeneracy needed for
the conclusion fails.

**Bibliographic comments.** The efficient score as the projection of the
score onto the orthocomplement of the nuisance tangent space, and the
resulting efficient influence function `\tilde I^{-1}\tilde\ell_\theta`, are the
central organizing concepts of modern semiparametric efficiency theory; van
der Vaart's Lemma 25.25 is a synthesis rather than a single seminal
result. The geometric/projection formulation traces back to C. Stein,
"Efficient nonparametric testing and estimation," *Proc. Third Berkeley
Symp. Math. Statist. Probab.*, vol. 1 (1956), 187–195, and was developed into
a full tangent-space theory by P. J. Bickel, C. A. J. Klaassen, Y. Ritov and
J. A. Wellner, *Efficient and Adaptive Estimation for Semiparametric Models*,
Johns Hopkins University Press, 1993 (reprinted Springer, 1998) — see their
Chapters 2–3, where the efficient score function and information bound for
`(θ, η)` models are constructed exactly as the score residual orthogonal to
the nuisance scores. Van der Vaart's §25.4 presents this material in the
score/information-operator language adopted here.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.StrictModel.EfficientScore

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- *Ordinary score operator* for the parameter `θ` at `θ₀`.

A continuous linear map from the parameter Hilbert space `Θ` into
`↥(L²₀(P))`. For a parametric family `t ↦ P_{θ₀ + t·v, η₀}`, evaluating
the score operator at `v` yields the QMD score function (vdV §25.4).

Reference: vdV §25.4. -/
abbrev OrdinaryScore (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    [CompleteSpace Θ] :=
  Θ →L[ℝ] ↥(L2ZeroMean P)

/-- *Nuisance tangent space*: a closed submodule of `↥(L²₀(P))`
representing the scores reachable by perturbing the nuisance parameter
`η`.

Reference: vdV §25.4. The specific submodule depends on the nuisance
model; we take it as a user-supplied input rather than fixing a
particular construction. -/
abbrev NuisanceTangentSpace (P : Measure Ω) [IsProbabilityMeasure P] :=
  Submodule ℝ ↥(L2ZeroMean P)

variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
  [CompleteSpace Θ]

/-- *Efficient score* for the parameter direction `v` at `θ₀`: the
ordinary score `S_θ v` minus its orthogonal projection onto the
nuisance tangent space. The residual is, by construction, orthogonal
to every nuisance direction.

`efficientScore S_θ T_nuis v := S_θ v - T_nuis.starProjection (S_θ v)`.

Reference: vdV §25.4. The efficient score captures the part of the
ordinary score that *cannot* be explained by perturbing the nuisance
parameter.

Edge behavior: when `S_θ v ∈ T_nuis`, `efficientScore = 0` (no
direction-`v` information remains after the nuisance projection);
the corresponding `eif_from_efficientScore` hypothesis
`I_eff(v) ≠ 0` then fails. -/
noncomputable def efficientScore
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (v : Θ) : ↥(L2ZeroMean P) :=
  S_θ v - T_nuis.starProjection (S_θ v)

/-- *Efficient information* for parameter direction `v`: the squared
`L²(P)`-norm of the efficient score.

`efficientInformation S_θ T_nuis v := ‖efficientScore S_θ T_nuis v‖²`.

Reference: vdV §25.4. In the multi-dim setting (k-dim θ), this
generalises to the *efficient information matrix* with entries
`⟪S_eff(eᵢ), S_eff(eⱼ)⟫`; the 1-dim form here is its single diagonal
entry along direction `v`.

Edge behavior: zero iff `S_θ v ∈ T_nuis`. -/
noncomputable def efficientInformation
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (v : Θ) : ℝ :=
  ‖efficientScore S_θ T_nuis v‖^2

/-- *vdV lem:25.25 (1-dim form).* Under non-degenerate efficient
information, `(1 / I_eff(v)) • S_eff(v)` is an efficient influence
function for the linear-functional derivative `dψ` whose action on the
score range is `dψ (S_θ u) = ⟪v, u⟫`.

Reference: vdV §25.4, lem:25.25. The k-dim form
`EIF = I_eff⁻¹ S_eff` (with `I_eff` the efficient information matrix)
generalises this; the 1-dim form here is its slice along direction `v`.

The hypothesis `h_dψ` encodes the parameter derivative shape: for a
linear functional `ψ(P_{θ, η}) := ⟨v, θ⟩` of the parameter, the
pathwise derivative on the score-range submodule of `T` matches
`u ↦ ⟪v, u⟫_Θ`. Concrete consumers prove this via
`PathwiseDifferentiableAt`.

Proof: reduce to `eif_of_representation_and_membership` by checking
two conditions on the candidate `IF := (1/I_eff(v)) • S_eff(v)`:
(1) `IF ∈ T` (membership): assumes `T` is large enough to contain
    `S_eff(v)`. We add `h_mem : (1/I_eff(v)) • S_eff(v) ∈ T` directly.
(2) `IsInfluenceFunction P T dψ IF`: for any `g ∈ T`,
    `⟪IF, g⟫ = (1/I_eff(v)) ⟪S_eff(v), g⟫`. Splitting `g = g_θ + g_η`
    with `g_θ ∈ range(S_θ)` and `g_η ∈ T_nuis`:
    - `⟪S_eff(v), g_η⟫ = 0` since `S_eff(v) ⊥ T_nuis` by construction.
    - `⟪S_eff(v), g_θ⟫ = ⟪S_θ v, g_θ⟫ - ⟪proj S_θ v, g_θ⟫`.
    The cleanest formulation passes `dψ` already evaluated: we
    require `dψ g = (1/I_eff(v)) ⟪S_eff(v), g⟫` for every `g ∈ T`,
    which is the influence-function condition we want to prove. -/
theorem eif_from_efficientScore
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (v : Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P))
    (h_mem :
      (1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v ∈ T)
    (dψ : T →L[ℝ] ℝ)
    (h_dψ : ∀ g : T,
      dψ g
        = (1 / efficientInformation S_θ T_nuis v)
            * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ) :
    IsEfficientInfluenceFunction P T dψ
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) := by
  refine ⟨?_, h_mem⟩
  intro g
  -- `IsInfluenceFunction` says `⟪IF, g⟫ = dψ g`.
  -- Compute `⟪c • S_eff, g⟫ = c * ⟪S_eff, g⟫` and combine with `h_dψ`.
  rw [real_inner_smul_left]
  exact (h_dψ g).symm

/-- *Efficient score is orthogonal to the nuisance tangent space.* By
construction `efficientScore S_θ T_nuis v = S_θ v - proj_{T_nuis}(S_θ v)`
is the residual of `S_θ v` after projecting onto `T_nuis`, hence lies in
`T_nuisᗮ`. Therefore its inner product against any `g ∈ T_nuis` is zero.

Reference: vdV §25.4, p.368 — `ℓ̃_{θ,η} = ℓ̇_{θ,η} - Π_{η}ℓ̇_{θ,η}`, the
defining orthogonality of the efficient score to the nuisance scores. -/
theorem efficientScore_inner_nuisance_eq_zero
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (v : Θ) {g : ↥(L2ZeroMean P)} (hg : g ∈ T_nuis) :
    ⟪efficientScore S_θ T_nuis v, g⟫_ℝ = 0 := by
  -- The residual `S_θ v - proj S_θ v` lies in `T_nuisᗮ`.
  have h_resid_perp : efficientScore S_θ T_nuis v ∈ T_nuisᗮ :=
    T_nuis.sub_starProjection_mem_orthogonal (S_θ v)
  -- `g ∈ T_nuis` gives `⟪g, residual⟫ = 0`; commute.
  have hgy : ⟪g, efficientScore S_θ T_nuis v⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal _ _).mp h_resid_perp g hg
  rwa [real_inner_comm] at hgy

/-- The efficient score is homogeneous in the direction: it is the image
of a continuous-linear map (ordinary score minus its nuisance projection),
so it commutes with scalars. -/
theorem efficientScore_smul
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (c : ℝ) (v : Θ) :
    efficientScore S_θ T_nuis (c • v) = c • efficientScore S_θ T_nuis v := by
  simp only [efficientScore, map_smul, smul_sub]

/-- *Efficient-score inner products only see the efficient part.* Because
`S_θ u = S̃_eff(u) + Π_{T_nuis}(S_θ u)` and `S̃_eff(v) ⊥ T_nuis`, the inner
product of the efficient score `S̃_eff(v)` against the **ordinary** score
`S_θ u` coincides with its inner product against the **efficient** score
`S̃_eff(u)`: the nuisance projection drops out.

This is the Pythagorean identity underlying the efficient-information
matrix `⟪ℓ̃(v), ℓ̇_θ(u)⟫ = ⟪ℓ̃(v), ℓ̃(u)⟫` (vdV §25.4, p.368). Internalizing
it lets `eif_from_efficientScore'` require only the coordinate-normalization
identity in efficient-score form, keeping the orthogonality half out of the
hypothesis surface. -/
theorem efficientScore_inner_ordinary_eq_self
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (v u : Θ) :
    ⟪efficientScore S_θ T_nuis v, S_θ u⟫_ℝ
      = ⟪efficientScore S_θ T_nuis v, efficientScore S_θ T_nuis u⟫_ℝ := by
  have hsplit : S_θ u
      = efficientScore S_θ T_nuis u + T_nuis.starProjection (S_θ u) := by
    rw [efficientScore]; abel
  rw [hsplit, inner_add_right,
      efficientScore_inner_nuisance_eq_zero S_θ T_nuis v
        (T_nuis.starProjection_apply_mem (S_θ u)),
      add_zero]

/-- *vdV lem:25.25 (1-dim form), derived version.* This is the
**derived** counterpart of `eif_from_efficientScore`: instead of
assuming the influence-function representation `h_dψ` as a hypothesis,
it *derives* that representation from the book's path-existence content
(25.26) and the efficient-information cross identity, then concludes via
`eif_from_efficientScore`.

The derived-vs-assumed distinction: `eif_from_efficientScore` takes
`h_dψ : ∀ g, dψ g = (1/Ĩ)⟪ℓ̃, g⟫` directly (the influence-function
identity packaged as a hypothesis, as the `*Assumptions` bundles in
`Asymptotics/` supply it). The present theorem shows that field is not a
free input: it follows from

* `h_decomp` — every tangent direction splits as `S_θ u + g_nuis` with
  `g_nuis ∈ T_nuis`. This is the book's tangent-set structure
  `Ṗ_{P_{θ,η}} = lin(ℓ̇_θ) + η̇Ṗ` (vdV §25.4, p.368, the tangent set in
  the conclusion of lem:25.25). Legitimate external input: it pins down
  *which* model `T` corresponds to.
* `h_deriv_eq` — along a path with score `S_θ u + g_nuis`, the
  difference quotient of `ψ` tends to `⟪v, u⟫_Θ`. This is the book's
  statement that `ψ(P_{θ,η}) = ⟨v, θ⟩` is the θ-coordinate functional,
  whose derivative reads off the `S_θ`-component `u`. The path-existence
  hypothesis (25.26) is what makes `dψ` well-defined on the whole
  `S_θ '' univ + T_nuis`; here we consume its consequence directly via
  the pathwise derivative `hpd.derivative`.
* `h_gram` — the efficient-information **self**-identity in efficient-score
  form `⟪ℓ̃(v), ℓ̃(u)⟫ = Ĩ · ⟪v, u⟫_Θ`, the `(v,u)` entry of the efficient
  information matrix (its diagonal `Ĩ` at `u = v`). This is only the
  coordinate-normalization half: the orthogonality half
  `⟪ℓ̃(v), ℓ̇_θ(u)⟫ = ⟪ℓ̃(v), ℓ̃(u)⟫` (the nuisance projection drops out) is
  now **derived internally** via `efficientScore_inner_ordinary_eq_self`,
  not part of the hypothesis surface. We take the 1-dim slice of the
  self-identity as an input rather than rebuild the matrix.

Given these, `dψ g = ⟪v, u⟫ = (1/Ĩ)·Ĩ·⟪v, u⟫ = (1/Ĩ)·⟪ℓ̃(v), ℓ̃(u)⟫
= (1/Ĩ)·⟪ℓ̃(v), S_θ u⟫ = (1/Ĩ)·⟪ℓ̃(v), S_θ u + g_nuis⟫ = (1/Ĩ)·⟪ℓ̃(v), g⟫`,
where `⟪ℓ̃(v), ℓ̃(u)⟫ = ⟪ℓ̃(v), S_θ u⟫` is `efficientScore_inner_ordinary_eq_self`
and the last step uses `⟪ℓ̃(v), g_nuis⟫ = 0`. The `hI_pos : 0 < Ĩ` hypothesis is the
book's nonsingularity of `Ĩ` (mandatory: at `Ĩ = 0` the functional is
not differentiable, vdV p.369).

Reference: vdV §25.4 Lemma 25.25 + eq (25.26), p.368-369. -/
theorem eif_from_efficientScore'
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (v : Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P))
    (ψ : Measure Ω → ℝ)
    (hpd : AsymptoticStatistics.Core.Pathwise.PathwiseDifferentiableAt P T ψ)
    (h_decomp : ∀ g : T, ∃ (u : Θ) (g_nuis : ↥(L2ZeroMean P)),
        g_nuis ∈ T_nuis ∧ (g : ↥(L2ZeroMean P)) = S_θ u + g_nuis)
    (h_deriv_eq : ∀ (u : Θ) (g_nuis : ↥(L2ZeroMean P)), g_nuis ∈ T_nuis →
        ∀ (hmem : S_θ u + g_nuis ∈ T),
          hpd.derivative ⟨S_θ u + g_nuis, hmem⟩ = ⟪v, u⟫_ℝ)
    (h_gram : ∀ u : Θ,
        ⟪efficientScore S_θ T_nuis v, efficientScore S_θ T_nuis u⟫_ℝ
          = efficientInformation S_θ T_nuis v * ⟪v, u⟫_ℝ)
    (hI_pos : 0 < efficientInformation S_θ T_nuis v)
    (h_mem :
      (1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v ∈ T) :
    IsEfficientInfluenceFunction P T hpd.derivative
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) := by
  -- Abbreviation for the efficient information (positive scalar).
  set Ĩ := efficientInformation S_θ T_nuis v with hĨ
  have hI_ne : Ĩ ≠ 0 := ne_of_gt hI_pos
  -- Derive the influence-function representation `h_dψ`, then conclude
  -- via the assumed-form theorem `eif_from_efficientScore`.
  apply eif_from_efficientScore S_θ T_nuis v T h_mem hpd.derivative
  intro g
  -- Split `g = S_θ u + g_nuis` with `g_nuis ∈ T_nuis`.
  obtain ⟨u, g_nuis, hg_nuis, hg_eq⟩ := h_decomp g
  -- The derivative reads off `⟪v, u⟫` along this path.
  have hmem : S_θ u + g_nuis ∈ T := by rw [← hg_eq]; exact g.2
  have h_dv : hpd.derivative g = ⟪v, u⟫_ℝ := by
    have hg_subtype : g = ⟨S_θ u + g_nuis, hmem⟩ := by
      apply Subtype.ext; exact hg_eq
    rw [hg_subtype]; exact h_deriv_eq u g_nuis hg_nuis hmem
  -- `⟪efficientScore, g⟫ = ⟪efficientScore, S_θ u⟫ + ⟪efficientScore, g_nuis⟫
  --   = Ĩ·⟪v,u⟫ + 0`.
  have h_orth : ⟪efficientScore S_θ T_nuis v, g_nuis⟫_ℝ = 0 :=
    efficientScore_inner_nuisance_eq_zero S_θ T_nuis v hg_nuis
  have h_inner :
      ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ
        = Ĩ * ⟪v, u⟫_ℝ := by
    rw [hg_eq, inner_add_right, h_orth, add_zero,
        efficientScore_inner_ordinary_eq_self S_θ T_nuis v u, h_gram u]
  -- Assemble: `dψ g = ⟪v,u⟫ = (1/Ĩ)·(Ĩ·⟪v,u⟫) = (1/Ĩ)·⟪efficientScore, g⟫`.
  rw [h_dv, h_inner, ← hĨ]
  rw [one_div, ← mul_assoc, inv_mul_cancel₀ hI_ne, one_mul]

end AsymptoticStatistics.StrictModel.EfficientScore
