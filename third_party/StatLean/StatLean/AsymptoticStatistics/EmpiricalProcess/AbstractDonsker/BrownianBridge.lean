module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.Carrier
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.GPProcess
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.MeasureTheory.Measure.Tight

@[expose] public section

/-!
# The `P`-Brownian-bridge limit `G_P` in `ℓ∞(F)`

The weak limit of the empirical process `𝔾ₙ` over a `P`-Donsker class `F` is the
**`P`-Brownian bridge** `G_P`: a tight, Borel-measurable, centred Gaussian
process on `ℓ∞(F)` whose finite-dimensional marginals are mean-zero Gaussian with
covariance `cov(G_P f, G_P g) = P(fg) − Pf · Pg` (van der Vaart,
*Asymptotic Statistics* §19.2, book p.269; van der Vaart–Wellner Ch. 2.1), and
which concentrates on the uniformly-`distL2 P`-continuous (UC) paths.

The predicate `ProbabilityTheory.IsGaussianProcess` specifies finite-dimensional
marginals. A Brownian bridge additionally requires a tight Borel path-space law
on `ℓ∞(F)` with almost surely uniformly continuous sample paths. The structure
below records these properties of `G_P`; four of its five fields hold for the
candidate law `gpBridgeMeasure`, while tightness is proved in
`PBridgeTight.lean`.

## Main definitions

* `IsPBrownianBridge F P ν` — predicate: `ν` is *the* `P`-Brownian-bridge law on
  `ℓ∞(F)` (probability measure, centred Gaussian marginals with covariance
  `Pfg − Pf·Pg`, tight, UC paths).

## Main results

* `pBridge_isProbabilityMeasure`, `pBridge_cov`, `pBridge_isGaussian_fdd`,
  `pBridge_ucPaths` — four of the five `IsPBrownianBridge` properties for the
  candidate law `ν = gpBridgeMeasure`. Tightness (`pBridge_tight`) and the
  existence theorem `exists_pBrownianBridge`, with witness `gaussianPBridge`,
  are proved in `PBridgeTight.lean`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory IsonormalProcess
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`P`-Brownian bridge in `ℓ∞(F)`** (the abstract-Donsker limit `G_P`).

`ν : Measure (LinfF F)` is a `P`-Brownian-bridge law iff it is a tight, centred
Gaussian Borel measure on `ℓ∞(F)` whose finite-dimensional marginals have
covariance `cov(z f, z g) = P(fg) − Pf·Pg = marginalCovEntry P ![f,g] 0 1`
(vdV §19.2, book p.269), concentrated on the `distL2 P`-uniformly-continuous
paths.

This is the **`G_P`** target specification, with the full vdV §19.2 field set:
probability measure, Brownian-bridge covariance, centred Gaussian
finite-dimensional marginals (`isGaussian_fdd`), tightness of the Borel law
(`tight`), and concentration on the `distL2 P`-uniformly-continuous sample paths
(`ucPaths`). -/
structure IsPBrownianBridge (F : Set (Ω → ℝ)) (P : Measure Ω)
    (ν : Measure (LinfF F)) : Prop where
  /-- `G_P` is a genuine probability law. -/
  isProbabilityMeasure : IsProbabilityMeasure ν
  /-- **Covariance specification.** The second mixed moment of the coordinate
  evaluations `z ↦ z f`, `z ↦ z g` under `ν` is the Brownian-bridge covariance
  `P(fg) − Pf·Pg`. (The coordinate readout `fun z : LinfF F => z f'` for
  `f' : ↥F` is the finite-dim projection; centredness makes the second mixed
  moment equal to the covariance.)

  Stated as: for all `f g : ↥F`,
  `∫ z, (z f) * (z g) ∂ν = ∫ x, (f:Ω→ℝ) x * (g:Ω→ℝ) x ∂P
                            − (∫ x, (f:Ω→ℝ) x ∂P) * (∫ x, (g:Ω→ℝ) x ∂P)`. -/
  cov : ∀ f g : ↥F,
    ∫ z : LinfF F, (z f) * (z g) ∂ν
      = (∫ x, (f : Ω → ℝ) x * (g : Ω → ℝ) x ∂P)
        - (∫ x, (f : Ω → ℝ) x ∂P) * (∫ x, (g : Ω → ℝ) x ∂P)
  /-- Constitutive (vdV §19.2 p.269): **centred (mean-zero) coordinate marginals.**
  Each coordinate evaluation `z ↦ z f` has integral `0` under `ν`: vdV's limit
  process `G_P` is a *centred* Gaussian, `E G_P f = 0`.  Together with `cov` this
  pins down every finite-dimensional marginal as `N(0, Σ)`; removing it would allow
  a nonzero-mean Gaussian, hence not *the* (centred) Brownian bridge. -/
  mean : ∀ f : ↥F, ∫ z : LinfF F, (z f) ∂ν = 0
  /-- Constitutive (vdV §19.2 p.269): **centred Gaussian finite-dimensional
  marginals.** For any finite tuple of indices `φ : Fin m → ↥F`, the coordinate
  readout `z ↦ (z (φ 0), …, z (φ (m-1)))` has a (multivariate) Gaussian law under
  `ν`. This is exactly vdV's "the limit process `G_P` is Gaussian": the f.d.d.
  marginals are jointly Gaussian. Removing this field makes `ν` not a Gaussian
  process, hence not *the* `P`-Brownian bridge. -/
  isGaussian_fdd : ∀ (m : ℕ) (φ : Fin m → ↥F),
    ProbabilityTheory.HasGaussianLaw (fun z : LinfF F => (fun k => z (φ k))) ν
  /-- Constitutive (vdV §19.2 p.269): **tightness of the Borel law `ν`.** The
  Brownian-bridge law is a *tight* (Radon) Borel measure on `ℓ∞(F)` — vdV's
  weak limit `G_P` is by construction tight (this is the content of the
  Donsker/Prohorov side of §18). Without tightness the object is a finitely-
  additive Gaussian "process" with no genuine path-space law; tightness is what
  makes `ν` a bona fide measure-theoretic limit. -/
  tight : MeasureTheory.IsTightMeasureSet ({ν} : Set (Measure (LinfF F)))
  /-- Constitutive (vdV §19.2 p.269): **uniformly-continuous sample paths.**
  `ν`-almost every path `z` is uniformly continuous as a function `↥F → ℝ` in the
  intrinsic `L²(P)` semimetric `distL2`. vdV's `G_P` concentrates on
  `UC(F, ρ_P)`; this is the defining sample-path regularity of the Brownian
  bridge.  Stated as an explicit ε-δ predicate on `distL2 P`-balls because the
  subtype `↥F` carries no `UniformSpace`/`PseudoMetricSpace` instance in scope
  (the Carrier layer deliberately avoids committing to one). -/
  ucPaths : ∀ᵐ z ∂ν, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∀ f g : ↥F, distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ → |z f - z g| < ε

/-! ## `IsPBrownianBridge` fields for the candidate law `ν = gpBridgeMeasure`

The candidate `P`-Brownian-bridge law is `ν = gpBridgeMeasure … = iidStdGaussian.map gpPath`
(`GPProcess.lean`).  The three lemmas below discharge the
`isProbabilityMeasure` / `cov` / `ucPaths` fields of `IsPBrownianBridge` for this `ν`
from the building blocks already established for `gpPath` and `gpX`. -/

section GpBridgeFields

variable {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
variable {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
  (hF_meas : ∀ f ∈ F, Measurable f)
  (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
  (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
  (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty)

/-- **B1 — probability measure.** `gpBridgeMeasure = iidStdGaussian.map gpPath` is a
probability measure: `iidStdGaussian` is one, and pushforward of a probability
measure under an `AEMeasurable` map is a probability measure
(`isProbabilityMeasure_map` + `gpPath_aemeasurable`). -/
theorem pBridge_isProbabilityMeasure :
    IsProbabilityMeasure
      (gpBridgeMeasure hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) := by
  rw [gpBridgeMeasure]
  exact Measure.isProbabilityMeasure_map
    (gpPath_aemeasurable hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne)

/-- **B2 — Brownian-bridge covariance.** The second mixed moment of the coordinate
evaluations `z ↦ z f`, `z ↦ z g` under `ν = gpBridgeMeasure` is `P(fg) − Pf·Pg`.

Push the integral through `gpPath` (`integral_map` with the `AEStronglyMeasurable`
integrand `z ↦ (z f) * (z g)`, continuous coordinate evaluation × continuous
product), reduce the integrand to `gpX f · gpX g` via the coordinate a.e.-agreement
`gpPath_aeeq_coord`, then apply `gpX_cov`. -/
theorem pBridge_cov (f g : ↥F) :
    ∫ z : LinfF F,
        (z f) * (z g) ∂(gpBridgeMeasure hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne)
      = (∫ x, (f : Ω → ℝ) x * (g : Ω → ℝ) x ∂P)
        - (∫ x, (f : Ω → ℝ) x ∂P) * (∫ x, (g : Ω → ℝ) x ∂P) := by
  -- Coordinate evaluation `z ↦ z i` is continuous on `ℓ∞(F)` (1-Lipschitz).
  have hcont_eval : ∀ i : ↥F, Continuous (fun z : LinfF F => z i) := by
    intro i
    have hlip : LipschitzWith 1 (fun z : LinfF F => z i) := by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
      have hsub : (z : ↥F → ℝ) i - (w : ↥F → ℝ) i = (z - w) i := by
        rw [lp.coeFn_sub z w]; rfl
      rw [show ‖(z : ↥F → ℝ) i - (w : ↥F → ℝ) i‖ = ‖(z - w) i‖ from by rw [hsub]]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w) i
    exact hlip.continuous
  -- The integrand `z ↦ (z f)*(z g)` is `AEStronglyMeasurable`.
  have hint_asm : AEStronglyMeasurable (fun z : LinfF F => (z f) * (z g))
      (gpBridgeMeasure hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) :=
    (((hcont_eval f).mul (hcont_eval g)).stronglyMeasurable).aestronglyMeasurable
  rw [gpBridgeMeasure]
  rw [integral_map
    (gpPath_aemeasurable hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne)
    (by
      rw [gpBridgeMeasure] at hint_asm
      exact hint_asm)]
  -- After `integral_map`, the integrand is `ω ↦ (gpPath ω f) * (gpPath ω g)`.
  -- Reduce to `gpX f · gpX g` via the coordinate a.e.-agreement.
  have hpt : (fun ω => (gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f)
        * (gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω g))
      =ᵐ[iidStdGaussian]
      fun ω => gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep f ω
        * gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep g ω := by
    filter_upwards [gpPath_aeeq_coord hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne f,
      gpPath_aeeq_coord hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne g] with ω hf hg
    rw [hf, hg]
  rw [integral_congr_ae hpt]
  exact gpX_cov ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep f g

/-- **B2′ — mean-zero coordinate marginals.** The coordinate evaluation `z ↦ z f`
under `ν = gpBridgeMeasure` has integral `0`: the `P`-Brownian bridge is centred.

Push the integral through `gpPath` (`integral_map` with the `AEStronglyMeasurable`
integrand `z ↦ z f`, continuous coordinate evaluation), reduce to `gpX f` via the
coordinate a.e.-agreement `gpPath_aeeq_coord` then to the isonormal image via
`gpX_aeeq`, whose pushforward law is `gaussianReal 0 ‖·‖²`
(`isonormal_map_eq_gaussianReal`), so its mean is `0` (`integral_id_gaussianReal`). -/
theorem pBridge_mean (f : ↥F) :
    ∫ z : LinfF F,
        (z f) ∂(gpBridgeMeasure hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) = 0 := by
  -- Coordinate evaluation `z ↦ z i` is continuous on `ℓ∞(F)` (1-Lipschitz).
  have hcont_eval : ∀ i : ↥F, Continuous (fun z : LinfF F => z i) := by
    intro i
    have hlip : LipschitzWith 1 (fun z : LinfF F => z i) := by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
      have hsub : (z : ↥F → ℝ) i - (w : ↥F → ℝ) i = (z - w) i := by
        rw [lp.coeFn_sub z w]; rfl
      rw [show ‖(z : ↥F → ℝ) i - (w : ↥F → ℝ) i‖ = ‖(z - w) i‖ from by rw [hsub]]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w) i
    exact hlip.continuous
  -- The integrand `z ↦ z f` is `AEStronglyMeasurable`.
  have hint_asm : AEStronglyMeasurable (fun z : LinfF F => (z f))
      (gpBridgeMeasure hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) :=
    ((hcont_eval f).stronglyMeasurable).aestronglyMeasurable
  rw [gpBridgeMeasure]
  rw [integral_map
    (gpPath_aemeasurable hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne)
    (by
      rw [gpBridgeMeasure] at hint_asm
      exact hint_asm)]
  -- After `integral_map`, the integrand is `ω ↦ gpPath ω f`. Reduce a.e. to the
  -- isonormal image `isonormal gpBasis (gpEmbed f)` (via `gpPath_aeeq_coord`, `gpX_aeeq`).
  have hpt : (fun ω => gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f)
      =ᵐ[iidStdGaussian]
      fun ω => isonormal (gpBasis ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep)
        (gpEmbed ⟨G, hG_env, hG⟩ hF_meas f) ω := by
    filter_upwards [gpPath_aeeq_coord hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne f,
      gpX_aeeq ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep f] with ω h1 h2
    rw [h1, h2]
  rw [integral_congr_ae hpt]
  -- `∫ isonormal b (gpEmbed f) ∂iidStdGaussian = ∫ x ∂(iidStdGaussian.map (isonormal …))`
  -- `= ∫ x ∂(gaussianReal 0 ‖·‖²) = 0`.
  set W := isonormal (gpBasis ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep)
    (gpEmbed ⟨G, hG_env, hG⟩ hF_meas f) with hW
  have hmap : ∫ a, (W : (ℕ → ℝ) → ℝ) a ∂iidStdGaussian
      = ∫ x : ℝ, x ∂(iidStdGaussian.map (W : (ℕ → ℝ) → ℝ)) :=
    (integral_map (Lp.aestronglyMeasurable W).aemeasurable aestronglyMeasurable_id).symm
  rw [hmap, isonormal_map_eq_gaussianReal]; exact integral_id_gaussianReal

/-- **Measurability of the UC-path predicate set.** The set of paths `z : LinfF F`
satisfying the `distL2 P`-ε-δ uniform-continuity predicate is Borel-measurable.

The predicate `P z = ∀ ε > 0, ∃ δ > 0, ∀ f g, distL2 P f g < δ → |z f − z g| < ε`
is equivalent (by monotonicity in `ε`/`δ` and density of `ℚ`) to its `ℚ⁺`-indexed
form with the inner strict `<` relaxed to `≤`:
`∀ ε : ℚ, 0 < ε → ∃ δ : ℚ, 0 < δ ∧ ∀ f g, distL2 P f g < δ → |z f − z g| ≤ ε`.
For each fixed `(ε, δ)` and `(f, g)`, the set `{z | distL2 f g < δ → |z f − z g| ≤ ε}`
is closed (coordinate evaluations `z ↦ z f` are continuous, so `z ↦ |z f − z g|` is,
and `isClosed_le` applies; when `distL2 f g ≥ δ` it is the whole space).  An arbitrary
intersection over `(f, g)` of closed sets is closed, and the outer `⋂_ε ⋃_δ` ranges over
the countable `ℚ`, so the whole set is measurable. -/
theorem pBridge_ucPaths_measurableSet :
    MeasurableSet
      {z : LinfF F | ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
        ∀ f g : ↥F, distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ → |z f - z g| < ε} := by
  -- Coordinate evaluation `z ↦ z i` is continuous on `ℓ∞(F)` (1-Lipschitz).
  have hcont_eval : ∀ i : ↥F, Continuous (fun z : LinfF F => z i) := by
    intro i
    have hlip : LipschitzWith 1 (fun z : LinfF F => z i) := by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
      have hsub : (z : ↥F → ℝ) i - (w : ↥F → ℝ) i = (z - w) i := by
        rw [lp.coeFn_sub z w]; rfl
      rw [show ‖(z : ↥F → ℝ) i - (w : ↥F → ℝ) i‖ = ‖(z - w) i‖ from by rw [hsub]]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w) i
    exact hlip.continuous
  -- `Cl ε δ`: paths with `distL2 f g < δ → |z f − z g| ≤ ε`, an ∩ of closed sets.
  set Cl : ℝ → ℝ → Set (LinfF F) := fun ε δ =>
    {z : LinfF F | ∀ f g : ↥F, distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ → |z f - z g| ≤ ε}
    with hCldef
  have hCl_closed : ∀ ε δ : ℝ, IsClosed (Cl ε δ) := by
    intro ε δ
    have : Cl ε δ = ⋂ f : ↥F, ⋂ g : ↥F,
        {z : LinfF F | distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ → |z f - z g| ≤ ε} := by
      ext z; simp only [hCldef, Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    refine isClosed_iInter (fun f => isClosed_iInter (fun g => ?_))
    by_cases hfg : distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ
    · have hset : {z : LinfF F | distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ → |z f - z g| ≤ ε}
          = {z : LinfF F | |z f - z g| ≤ ε} := by
        ext z; simp only [Set.mem_setOf_eq]; exact ⟨fun h => h hfg, fun h _ => h⟩
      rw [hset]
      exact isClosed_le (((hcont_eval f).sub (hcont_eval g)).abs) continuous_const
    · have hset : {z : LinfF F | distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ → |z f - z g| ≤ ε}
          = Set.univ := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact fun h => absurd h hfg
      rw [hset]; exact isClosed_univ
  have hCl_meas : ∀ ε δ : ℝ, MeasurableSet (Cl ε δ) := fun ε δ => (hCl_closed ε δ).measurableSet
  -- The UC-predicate set = `⋂_{ε∈ℚ⁺} ⋃_{δ∈ℚ⁺} Cl ε δ`, a countable combination.
  have heq : {z : LinfF F | ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
        ∀ f g : ↥F, distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ → |z f - z g| < ε}
      = ⋂ ε : ℚ, {z : LinfF F | 0 < ε →
          ∃ δ : ℚ, 0 < δ ∧ z ∈ Cl (ε : ℝ) (δ : ℝ)} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, hCldef]
    constructor
    · -- real ⟹ ℚ⁺ (relaxed): for rational ε>0, find rational δ below a real witness.
      intro hP ε hε
      obtain ⟨δ₀, hδ₀, hδ₀_uc⟩ := hP (ε : ℝ) (by exact_mod_cast hε)
      obtain ⟨δ, hδ_pos, hδ_lt⟩ := exists_rat_btwn hδ₀
      refine ⟨δ, by exact_mod_cast hδ_pos, fun f g hfg => ?_⟩
      exact le_of_lt (hδ₀_uc f g (lt_trans hfg hδ_lt))
    · -- ℚ⁺ (relaxed) ⟹ real: for real ε>0, pick rational ε'<ε below it.
      intro hQ ε hε
      obtain ⟨ε', hε'_pos, hε'_lt⟩ := exists_rat_btwn hε
      have hε'_qpos : (0 : ℚ) < ε' := by exact_mod_cast hε'_pos
      obtain ⟨δ, hδ_pos, hδ_uc⟩ := hQ ε' hε'_qpos
      refine ⟨(δ : ℝ), by exact_mod_cast hδ_pos, fun f g hfg => ?_⟩
      exact lt_of_le_of_lt (hδ_uc f g hfg) hε'_lt
  rw [heq]
  refine MeasurableSet.iInter (fun ε => ?_)
  by_cases hε : (0 : ℚ) < ε
  · have : {z : LinfF F | 0 < ε → ∃ δ : ℚ, 0 < δ ∧ z ∈ Cl (ε : ℝ) (δ : ℝ)}
        = ⋃ δ : ℚ, ⋃ (_ : 0 < δ), Cl (ε : ℝ) (δ : ℝ) := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_iUnion, hε, forall_true_left,
        exists_prop]
    rw [this]
    exact MeasurableSet.iUnion (fun δ => MeasurableSet.iUnion (fun _ => hCl_meas _ _))
  · have : {z : LinfF F | 0 < ε → ∃ δ : ℚ, 0 < δ ∧ z ∈ Cl (ε : ℝ) (δ : ℝ)} = Set.univ := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact fun h => absurd h hε
    rw [this]; exact MeasurableSet.univ

/-- **B4 — uniformly-continuous sample paths.** `ν`-almost every path `z` is
uniformly continuous (`distL2 P`-ε-δ).  The good event `{ω | gpGood ω}` is co-null
(`gpSkeleton_spec`) and on it `gpPath ω = pathExtend ω` is uniformly continuous, so
the ε-δ predicate holds of `gpPath ω`.  Transport this a.e. property through the
pushforward `gpBridgeMeasure = iidStdGaussian.map gpPath` via `ae_map_iff`, whose
measurability obligation is `pBridge_ucPaths_measurableSet`. -/
theorem pBridge_ucPaths :
    ∀ᵐ z ∂(gpBridgeMeasure hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne),
      ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
        ∀ f g : ↥F, distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ → |z f - z g| < ε := by
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  -- The ε-δ predicate holds a.e. of `gpPath ω` (on the good event).
  have hae_omega : ∀ᵐ ω ∂iidStdGaussian,
      ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f g : ↥F,
        distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ →
        |gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f
          - gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω g| < ε := by
    filter_upwards [(gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.2]
      with ω hω
    -- `ω` is good; `gpPath ω = pathExtend ω` is uniformly continuous.
    have huc := uniformContinuous_pathExtend_of_good hG_env hG hF_meas hH_inf hH_sep
      hF_ent hF_ne hω
    rw [Metric.uniformContinuous_iff] at huc
    intro ε hε
    obtain ⟨δ, hδ, hδ_uc⟩ := huc ε hε
    refine ⟨δ, hδ, fun f g hfg => ?_⟩
    rw [gpPath_apply_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω f,
      gpPath_apply_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω g]
    -- `|pathExtend ω f − pathExtend ω g| = dist (pathExtend ω f) (pathExtend ω g) < ε`.
    rw [← Real.dist_eq]
    exact hδ_uc (show dist f g < δ from hfg)
  -- Transport the a.e. predicate through the pushforward map via `ae_map_iff`.
  rw [gpBridgeMeasure]
  rw [MeasureTheory.ae_map_iff
    (gpPath_aemeasurable hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne)
    pBridge_ucPaths_measurableSet]
  exact hae_omega

/-- **B3 — centred Gaussian finite-dimensional marginals.** For any finite tuple
`φ : Fin m → ↥F`, the coordinate readout `z ↦ (z (φ k))ₖ` has a multivariate
Gaussian law under `ν = gpBridgeMeasure`.

`gpBridgeMeasure = iidStdGaussian.map gpPath`, so by `Measure.map_map` the readout
law is the pushforward of `iidStdGaussian` along `ω ↦ (gpPath ω (φ k))ₖ`.  This tuple
agrees `a.e.` (coordinatewise, finite intersection) with
`ω ↦ (isonormal gpBasis (gpEmbed (φ k)) ω)ₖ` via `gpPath_aeeq_coord` + `gpX_aeeq`,
whose Gaussian law is `isonormal_hasGaussianLaw_tuple`.  `HasGaussianLaw.congr`
transports it to the `gpPath` tuple, and the `map_map` identity to the readout. -/
theorem pBridge_isGaussian_fdd (m : ℕ) (φ : Fin m → ↥F) :
    ProbabilityTheory.HasGaussianLaw (fun z : LinfF F => (fun k => z (φ k)))
      (gpBridgeMeasure hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) := by
  -- Coordinate evaluation `z ↦ z i` is continuous on `ℓ∞(F)` (1-Lipschitz); the
  -- readout `R z = (z (φ k))ₖ` is therefore continuous, hence measurable.
  have hcont_eval : ∀ i : ↥F, Continuous (fun z : LinfF F => z i) := by
    intro i
    have hlip : LipschitzWith 1 (fun z : LinfF F => z i) := by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
      have hsub : (z : ↥F → ℝ) i - (w : ↥F → ℝ) i = (z - w) i := by
        rw [lp.coeFn_sub z w]; rfl
      rw [show ‖(z : ↥F → ℝ) i - (w : ↥F → ℝ) i‖ = ‖(z - w) i‖ from by rw [hsub]]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w) i
    exact hlip.continuous
  have hR_meas : Measurable (fun z : LinfF F => (fun k => z (φ k))) :=
    measurable_pi_lambda _ (fun k => (hcont_eval (φ k)).measurable)
  -- The `gpPath` tuple agrees a.e. with the isonormal tuple over `gpEmbed ∘ φ`.
  have hae : (fun ω => (fun k => gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω (φ k)))
      =ᵐ[iidStdGaussian]
      (fun ω => (fun k => isonormal (gpBasis ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep)
        (gpEmbed ⟨G, hG_env, hG⟩ hF_meas (φ k)) ω)) := by
    have hcoord : ∀ k : Fin m,
        (fun ω => gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω (φ k))
          =ᵐ[iidStdGaussian]
          (fun ω => isonormal (gpBasis ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep)
            (gpEmbed ⟨G, hG_env, hG⟩ hF_meas (φ k)) ω) := by
      intro k
      filter_upwards [gpPath_aeeq_coord hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne (φ k),
        gpX_aeeq ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep (φ k)] with ω h1 h2
      rw [h1, h2]
    filter_upwards [ae_all_iff.mpr hcoord] with ω hω
    funext k
    exact hω k
  -- The isonormal tuple is jointly Gaussian; transport to the `gpPath` tuple.
  have hgp_tuple : HasGaussianLaw
      (fun ω => (fun k => gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω (φ k)))
      iidStdGaussian :=
    (isonormal_hasGaussianLaw_tuple (gpBasis ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep)
      (fun k => gpEmbed ⟨G, hG_env, hG⟩ hF_meas (φ k))).congr hae.symm
  -- The readout law on `gpBridgeMeasure` is the pushforward of the tuple via `map_map`.
  refine ⟨?_⟩
  rw [gpBridgeMeasure,
    AEMeasurable.map_map_of_aemeasurable hR_meas.aemeasurable
      (gpPath_aemeasurable hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne)]
  exact hgp_tuple.isGaussian_map

end GpBridgeFields

/-! The existence lemma `exists_pBrownianBridge` and the chosen witness
`gaussianPBridge` are assembled from the five `IsPBrownianBridge` field lemmas in
`PBridgeTight.lean` (which has `pBridge_tight` in scope, closing the import cycle:
`PBridgeTight` imports `BrownianBridge`). -/

end AsymptoticStatistics.EmpiricalProcess
