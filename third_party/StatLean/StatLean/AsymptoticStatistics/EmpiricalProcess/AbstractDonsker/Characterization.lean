module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.PBridgeTight
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.SufficiencyDiscretization
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.NecessityTightness
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.Outer

@[expose] public section

/-!
# van der Vaart **Theorem 18.14**: abstract Donsker ⟺ marginal CLT + equicontinuity

The literal abstract-Donsker property: the empirical process `𝔾ₙ`, viewed as a
random element of `ℓ∞(F)` (the carrier `LinfF F`), converges weakly **in the
van der Vaart–Wellner outer sense** `⇝ₒ` to the tight `P`-Brownian-bridge law
`G_P = gaussianPBridge`. van der Vaart, *Asymptotic Statistics* Theorem 18.14
(book p.261) states this is equivalent to the operational characterization
`IsMarginalCLT F P ∧ IsAsymptoticallyEquicontinuous F P` — which is exactly the
current working definition `IsPDonsker` (`Donsker.lean`).

## Main definitions

* `IsPDonsker'` — the **literal** abstract-Donsker property: `𝔾ₙ ⇝ₒ G_P` in
  `ℓ∞(F)`.

## Main results (Theorem 18.14)

* `isPDonsker'_of_marginalCLT_and_asymptoticallyEquicontinuous` (⟸) — marginal
  CLT + asymptotic equicontinuity ⟹ `𝔾ₙ ⇝ₒ G_P` (vdV p.261).
* `marginalCLT_and_asymptoticallyEquicontinuous_of_isPDonsker'` (⟹) —
  `𝔾ₙ ⇝ₒ G_P` ⟹ marginal CLT + asymptotic equicontinuity
  (vdV p.261; uses outer-Prohorov 18.12).
* `isPDonsker'_iff` — the headline equivalence `IsPDonsker' F P ↔ IsPDonsker F P`,
  assembled from the two directions.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), Theorem
18.14 (book p.261), §19.2.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter Topology AsymptoticStatistics
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Literal abstract-Donsker property** (`𝔾ₙ ⇝ₒ G_P` in `ℓ∞(F)`).

For every iid sample `X : ℕ → Ξ → Ω` with law `P`, the empirical process
`n ↦ (f ↦ 𝔾ₙ f)`, packaged as a sequence of (non-measurable) maps
`Ξ → LinfF F = ℓ∞(F)`, converges weakly **in outer expectation** `⇝ₒ` to the tight
`P`-Brownian-bridge law `gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne`.

The iid-binder block matches `IsAsymptoticallyEquicontinuous` /`IsMarginalCLT`
verbatim. The vdV §19.2 Donsker preconditions supply both the `ℓ∞`-boundedness of
`𝔾ₙ` (`memℓp_empiricalProcess`, which only needs the `L¹` envelope derived inline
from the `L²` one `hG` via `MemLp.integrable`) and the existence of the limit
`G_P` (`gaussianPBridge`).  They are taken in the unbundled form required by the
`gpBridgeMeasure`-based construction of `gaussianPBridge`:

* `hG_env` / `hG` — `F` has a **square-integrable envelope** `G` (vdV
  §19.2): `IsEnvelope F G` plus `MemLp G 2 P`.
* `hF_meas` (vdV §19.2) — as in vdV, `F` is a class of measurable functions,
  encoded by requiring every `f ∈ F` to be `Measurable`.
* `hH_inf` (vdV §19.2) — the Gaussian Hilbert space is
  **infinite-dimensional**, as required by the `gpBridgeMeasure` construction.
* `hH_sep` (vdV §19.2) — separability of the Gaussian Hilbert space
  (derivable from `hF_ent` via `totallyBounded_L2`; kept as a hypothesis here for
  consistency with the construction).
* `hF_ent` (vdV §19.2) — **finite bracketing-entropy integral**.
* `hF_ne` (vdV §19.2) — `F` is nonempty.

vdV §18.1 / Theorem 18.14: `𝔾ₙ ⇝ₒ G_P` in `ℓ∞(F)`. -/
def IsPDonsker' (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty) : Prop :=
  ∀ {Ξ : Type} [_inst : MeasurableSpace Ξ] (μ : Measure Ξ)
    [_inst2 : IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω),
    (∀ i, Measurable (X i)) →
    ProbabilityTheory.iIndepFun X μ →
    (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
    μ.map (X 0) = P →
    WeakConvergesOuter (fun _ => μ)
      (fun n ξ => empiricalProcessLinf (fun i : Fin n => X i.val ξ)
        (memℓp_empiricalProcess
          ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
          (fun i : Fin n => X i.val ξ)))
      (gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne)

/-- **Theorem 18.14, sufficiency (⟸).** If `F` satisfies the marginal CLT and is
asymptotically equicontinuous, then the empirical process converges weakly in
`ℓ∞(F)` (outer sense) to the `P`-Brownian bridge.

vdV p.261 (⟸): the hard direction. Following vdV's own route, the readout tail is
controlled *only* for bounded-Lipschitz test functions (via the marginal CLT, the
limit-tail and the empirical discretization-error `S3`, assembled in
`isPDonsker'_of_marginalCLT_and_asymptoticallyEquicontinuous_aux`); the upgrade to all
bounded-*continuous* test functions is the inf-convolution / bounded-Lipschitz
portmanteau `weakConvergesOuter_of_lipschitz_readout`, which needs no tightness or
properness assumption. This avoids building an asymptotically-tight compact set for
the empirical process (vdV does not), so the non-proper carrier `ℓ∞(F)` poses no
obstruction. -/
theorem isPDonsker'_of_marginalCLT_and_asymptoticallyEquicontinuous
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty)
    (h : IsMarginalCLT F P ∧ IsAsymptoticallyEquicontinuous F P) :
    IsPDonsker' F P hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne := by
  intro Ξ _ μ _ X hX_meas hX_indep hX_id hX_law
  -- The empirical process `𝔾ₙ` and limit law `G_P`, written exactly as in the
  -- `IsPDonsker'` body / `_aux` conclusion (kept syntactic to avoid a `whnf` blow-up).
  let 𝔾 : ℕ → Ξ → LinfF F := fun n ξ =>
    empiricalProcessLinf (fun i : Fin n => X i.val ξ)
      (memℓp_empiricalProcess
        ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
        (fun i : Fin n => X i.val ξ))
  let GP := gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
  -- `G_P` is a probability measure; supply the instance so the portmanteau's
  -- `[IsProbabilityMeasure νD]` resolves without unfolding `gaussianPBridge`.
  haveI hGP_prob : IsProbabilityMeasure GP :=
    (isPBrownianBridge_gaussianPBridge hG_env hG hF_meas hH_inf hH_sep
      hF_ent hF_ne).isProbabilityMeasure
  -- Bounded-Lipschitz ⟹ bounded-continuous via the inf-convolution portmanteau; the
  -- bounded-Lipschitz readout family is supplied directly by `_aux`.
  exact weakConvergesOuter_of_lipschitz_readout (μ := fun _ => μ) (Xn := 𝔾) (νD := GP)
    (fun f hf_lip => isPDonsker'_of_marginalCLT_and_asymptoticallyEquicontinuous_aux
      hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne h.1 h.2 μ X hX_meas hX_indep hX_id hX_law
      f hf_lip)

/-- **Theorem 18.14, necessity (⟹) — fdd half.** If the empirical process
converges weakly in `ℓ∞(F)` (outer sense) to the `P`-Brownian bridge, then `F`
satisfies the marginal CLT (Theorem 18.14(a)).

**Mathematical content.** The marginal-CLT predicate `IsMarginalCLT F P` is the
conjunction of (a) `∀ f ∈ F, MemLp f 2 P` and (b) the finite-dimensional
distributional-convergence clause: every finite tuple `f : Fin k → (Ω → ℝ)`
valued in `F` has the standardised empirical vector converge in distribution to
`multivariateGaussian 0 (marginalCovMatrix P f)`.

Conjunct (a) is the `L²`-envelope consequence `memLp_of_mem_F` (each `f ∈ F` is
dominated by the square-integrable envelope `G`). Conjunct (b) is the *classical
multivariate central limit theorem* for the iid square-integrable vectors
`ω ↦ (f₀ ω, …, f_{k-1} ω)`: vdV's Theorem 18.14(a) is precisely the marginal CLT,
and the marginal CLT for iid `L²` functions is the multivariate CLT, with Gaussian
covariance `P fᵢfⱼ − Pfᵢ·Pfⱼ`. That CLT is already established standalone as
`marginalCLT_fdd_of_iid`, assembled into the full predicate by
`isMarginalCLT_of_memLp`. The Donsker hypothesis `h` is therefore not consumed by
the fdd half (it is genuinely needed only for the equicontinuity half, where the
outer-Prohorov / asymptotic-tightness machinery of vdV 18.12 enters); it is kept
in the signature for uniformity with the necessity-direction binder block.

vdV p.261 (⟹), Theorem 18.14(a): the marginal CLT is the finite-dimensional
projection of weak `ℓ∞(F)` convergence to the Gaussian bridge. -/
theorem marginalCLT_of_isPDonsker'
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty)
    (_h : IsPDonsker' F P hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) :
    IsMarginalCLT F P :=
  isMarginalCLT_of_memLp (fun _ hf => memLp_of_mem_F hG_env hG hF_meas hf)

/-- **Theorem 18.14, necessity (⟹) — equicontinuity half.** If the empirical
process converges weakly in `ℓ∞(F)` (outer sense) to the `P`-Brownian bridge,
then `F` is asymptotically equicontinuous (Theorem 18.14(b)).

vdV p.261 (⟹): this is the genuinely Donsker-driven half. Asymptotic
equicontinuity is the tightness side of weak `ℓ∞(F)` convergence: the limit
`gaussianPBridge` concentrates on the `distL2 P`-uniformly-continuous paths
(`IsPBrownianBridge.ucPaths`), and weak convergence to a tight limit transfers the
oscillation control back to the empirical process. The formal route uses the outer
asymptotic-tightness machinery (vdV 18.12 / van der Vaart–Wellner §2.1). -/
theorem asymptoticallyEquicontinuous_of_isPDonsker'
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty)
    (h : IsPDonsker' F P hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) :
    IsAsymptoticallyEquicontinuous F P :=
  equicont_of_weakConvergesOuter_gp hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne h

/-- **Theorem 18.14, necessity (⟹).** If the empirical process converges weakly
in `ℓ∞(F)` (outer sense) to the `P`-Brownian bridge, then `F` satisfies the
marginal CLT and is asymptotically equicontinuous.

Splits into the two halves `marginalCLT_of_isPDonsker'` (Theorem 18.14(a), the
finite-dimensional marginal CLT) and
`asymptoticallyEquicontinuous_of_isPDonsker'` (Theorem 18.14(b), the
asymptotic-tightness / equicontinuity half).

vdV p.261 (⟹): needs the outer Prohorov / asymptotic-tightness machinery
(vdV 18.12) for the equicontinuity half. -/
theorem marginalCLT_and_asymptoticallyEquicontinuous_of_isPDonsker'
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty)
    (h : IsPDonsker' F P hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) :
    IsMarginalCLT F P ∧ IsAsymptoticallyEquicontinuous F P :=
  ⟨marginalCLT_of_isPDonsker' hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne h,
   asymptoticallyEquicontinuous_of_isPDonsker' hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne h⟩

/-- **Theorem 18.14 (headline equivalence).** The literal abstract-Donsker
property `𝔾ₙ ⇝ₒ G_P` in `ℓ∞(F)` is equivalent to the operational
characterization `IsPDonsker F P = IsMarginalCLT F P ∧ IsAsymptoticallyEquicontinuous F P`.

Assembled from `marginalCLT_and_asymptoticallyEquicontinuous_of_isPDonsker'` (⟹)
and `isPDonsker'_of_marginalCLT_and_asymptoticallyEquicontinuous` (⟸); the RHS
`IsPDonsker` unfolds definitionally to the conjunction. -/
theorem isPDonsker'_iff {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty) :
    IsPDonsker' F P hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ↔ IsPDonsker F P :=
  ⟨fun h =>
      marginalCLT_and_asymptoticallyEquicontinuous_of_isPDonsker'
        hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne h,
   fun h =>
      isPDonsker'_of_marginalCLT_and_asymptoticallyEquicontinuous
        hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne h⟩

end AsymptoticStatistics.EmpiricalProcess
