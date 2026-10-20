module
public import StatLean.RobustStatistics.MEstimation.MLocationFunctional
public import StatLean.RobustStatistics.MEstimation.AsymptoticBreakdown
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# Scale M-functionals — the log-scale reduction and the breakdown point `min(δ, 1−δ)`

A scale M-estimate solves `(1/n) ∑ ρ(xᵢ/σ̂) = δ` (`MMY §2.5`, eq. (2.49)); its population
version solves `∫ ρ(x/σ) dP = δ`. Robustness of a scale estimator means staying away
from *both* boundary pieces of `Θ = (0, ∞)`: contamination can cause **explosion**
(`σ → ∞`, outliers) or **implosion** (`σ → 0`, inliers). The organizing device — `MMY
§3.2.2` — is that a scale M-estimator is a *location* M-estimator "in the log scale":
with `y = log|x|`, `μ = log σ`, `ψ(t) = ρ(eᵗ) − δ`, the scale equation becomes the
location equation, and the Round-1 location breakdown pair (`MMY (3.21)`/(3.22)) with
`k₁ = δ`, `k₂ = 1 − δ` yields the scale breakdown point

  `ε* = min(δ, 1 − δ)`   (`MMY (3.23)`),

with `δ` the explosion BP and `1 − δ` the implosion BP.

* `IsMScaleRoot` — the population scale M-equation (`MMY (2.49)`, population form).
* `logAbs`, `scaleScorePsi` — the log-scale transport data.
* `isMScaleRoot_iff_logScale` — the reduction (`MMY §3.2.2`, the display).
* `mScaleRoot_bounded_of_contamination` — no explosion, no implosion below
  `min(δ, 1−δ)` (`MMY (3.23)`, stability direction).
* `mScaleRoot_explodes` / `mScaleRoot_implodes` — sharpness beyond the BP.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera,
*Robust Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.)
§2.5 (eq. (2.49)), §2.6 (dispersion conditions (2.58)), §3.2.2 (the log-scale
reduction; eq. (3.23)). The population MAD (`MMY (2.62)`) is the scale M-functional of
the *discontinuous* loss `ρ = 1{|x| ≥ 1}` at `δ = 1/2`; it is outside the continuous-`ρ`
hypotheses used here and is treated only through its finite-sample breakdown
(`Scale/DispersionBreakdown.lean`).

**Bibliographic comments.** M-estimators of scale and their breakdown are part of Huber's
original program (Huber 1964; Huber and Ronchetti, *Robust Statistics*, 2nd ed., Wiley,
2009, ch. 5); the bias-robustness theory of scale — where the `min(δ, 1−δ)` explosion/
implosion dichotomy is sharpened to maximum-bias optimality — is R. D. Martin and R. H.
Zamar, "Bias robust estimation of scale," *Ann. Statist.* **21** (1993), 991–1017.
-/

open MeasureTheory Filter Topology

namespace StatLean.RobustStatistics

/-- **The population scale M-root** (`MMY §2.5`, eq. (2.49), population form): `σ > 0`
solves `∫ ρ(x/σ) dP = δ`. The Bochner-junk caveat of `IsMLocationRoot` applies:
consumers carry integrability of `ρ(·/σ)` explicitly. -/
def IsMScaleRoot (ρ : ℝ → ℝ) (δ : ℝ) (P : Measure ℝ) (σ : ℝ) : Prop :=
  0 < σ ∧ ∫ x, ρ (x / σ) ∂P = δ

/-- The log-modulus data map `x ↦ log |x|` of the `MMY §3.2.2` reduction. Junk note:
`Real.log 0 = 0`, so the map sends the atom at `0` to `0`; all statements below carry
`P {0} = 0` and are unaffected. -/
noncomputable def logAbs (x : ℝ) : ℝ := Real.log |x|

/-- The transported score `ψ(t) = ρ(eᵗ) − δ` of the `MMY §3.2.2` reduction. -/
noncomputable def scaleScorePsi (ρ : ℝ → ℝ) (δ : ℝ) (t : ℝ) : ℝ := ρ (Real.exp t) - δ

/-- The log-modulus map is measurable — the transport map of the reduction. -/
private theorem measurable_logAbs : Measurable logAbs := by
  unfold logAbs; fun_prop

/-- **The log-scale reduction** (`MMY §3.2.2`, the display `ρ(x/σ) − δ = ψ(y − μ)`):
for an even loss, `σ` is a scale M-root of `P` iff `log σ` is a *location* M-root of the
transported score under the pushforward `P.map logAbs`. This is the engine that turns
Round-1 location theorems into scale theorems. -/
theorem isMScaleRoot_iff_logScale {ρ : ℝ → ℝ} {δ : ℝ} {P : Measure ℝ}
    [IsProbabilityMeasure P] {σ : ℝ} (hσ : 0 < σ)
    -- USER-INPUT: even loss; MMY §3.2.2 ("since ρ is even")
    (hρ_even : ∀ x, ρ (-x) = ρ x)
    -- LEAN-ONLY: measurability of ρ, to transport the integral; regularity
    (hρ_meas : Measurable ρ)
    -- USER-INPUT: no atom at 0 (so |x| > 0 a.e. and the log is honest); MMY §3.2.2
    -- (implicit in y = log|x|)
    (hP0 : P {0} = 0)
    -- USER-INPUT: the loss is integrable at scale σ; MMY (2.49) context
    (hint : Integrable (fun x => ρ (x / σ)) P) :
    IsMScaleRoot ρ δ P σ ↔
      IsMLocationRoot (scaleScorePsi ρ δ) (P.map logAbs) (Real.log σ) := by
  have hF : Measurable fun y => scaleScorePsi ρ δ (y - Real.log σ) :=
    (hρ_meas.comp (Real.measurable_exp.comp (measurable_id.sub_const _))).sub measurable_const
  -- transport the location integral back to `P`
  have hmap : ∫ y, scaleScorePsi ρ δ (y - Real.log σ) ∂(P.map logAbs)
      = ∫ x, scaleScorePsi ρ δ (logAbs x - Real.log σ) ∂P :=
    integral_map measurable_logAbs.aemeasurable hF.aestronglyMeasurable
  have h0 : ∀ᵐ x ∂P, x ≠ 0 := by
    rw [ae_iff]; simpa using hP0
  -- off the (null) atom at `0`: `exp(log|x| − log σ) = |x|/σ` and `ρ(|x|/σ) = ρ(x/σ)`
  have hae : (fun x => scaleScorePsi ρ δ (logAbs x - Real.log σ))
      =ᵐ[P] fun x => ρ (x / σ) - δ := by
    filter_upwards [h0] with x hx
    have hxa : (0:ℝ) < |x| := abs_pos.2 hx
    have hexp : Real.exp (logAbs x - Real.log σ) = |x| / σ := by
      rw [logAbs, Real.exp_sub, Real.exp_log hxa, Real.exp_log hσ]
    rw [scaleScorePsi, hexp]
    rcases abs_choice x with h | h
    · rw [h]
    · rw [h, show (-x) / σ = -(x / σ) by ring, hρ_even]
  have hsub : ∫ x, scaleScorePsi ρ δ (logAbs x - Real.log σ) ∂P
      = (∫ x, ρ (x / σ) ∂P) - δ := by
    rw [integral_congr_ae hae, integral_sub hint (integrable_const δ)]
    simp
  rw [IsMScaleRoot, IsMLocationRoot, hmap, hsub]
  constructor
  · rintro ⟨-, h⟩; rw [h, sub_self]
  · intro h; exact ⟨hσ, by linarith⟩

/-- The transported score of a bounded even *continuous* loss is monotone with limits
`−δ` at `−∞` and `1 − δ` at `+∞` (`MMY §3.2.2` with `ρ(0) = 0`, `ρ(∞) = 1`): the
location breakdown data `k₁ = δ`, `k₂ = 1 − δ` of `MMY (3.23)`.

Continuity is *not* cosmetic: `exp t > 0` for every `t`, so the `−∞` limit is the limit
of `ρ` at `0⁺`, which equals `ρ(0) = 0` only under continuity at `0` — for the (monotone,
`ρ(0)=0`) indicator loss `ρ = 1_{(0,∞)}` the transported score is *constantly* `1 − δ`
and the claimed `−δ` limit fails. This is why the MAD's indicator loss is excluded from
this file (see the module docstring). -/
theorem scaleScorePsi_monotone_limits {ρ : ℝ → ℝ} {δ : ℝ}
    -- USER-INPUT: the loss is a bounded continuous ρ-function: even, nondecreasing on
    -- [0,∞), ρ(0) = 0, ρ(∞) = 1; MMY §2.5 / Definition 2.1 + Thm 10.1 regularity
    (hρ_mono : MonotoneOn ρ (Set.Ici 0)) (hρ0 : ρ 0 = 0)
    (hρ_lim : Tendsto ρ atTop (𝓝 1)) (hρc : Continuous ρ) :
    Monotone (scaleScorePsi ρ δ) ∧
      Tendsto (scaleScorePsi ρ δ) atBot (𝓝 (-δ)) ∧
      Tendsto (scaleScorePsi ρ δ) atTop (𝓝 (1 - δ)) := by
  refine ⟨fun s t hst => ?_, ?_, ?_⟩
  · exact sub_le_sub_right (hρ_mono (Set.mem_Ici.2 (Real.exp_pos s).le)
      (Set.mem_Ici.2 (Real.exp_pos t).le) (Real.exp_le_exp.2 hst)) δ
  · -- `exp t → 0⁺` as `t → −∞`, and continuity at `0` turns `ρ(0⁺)` into `ρ(0) = 0`
    have h1 : Tendsto (fun t => ρ (Real.exp t)) atBot (𝓝 (ρ 0)) :=
      (hρc.tendsto 0).comp Real.tendsto_exp_atBot
    rw [hρ0] at h1
    simpa [scaleScorePsi] using! h1.sub_const δ
  · have h2 : Tendsto (fun t => ρ (Real.exp t)) atTop (𝓝 1) := hρ_lim.comp Real.tendsto_exp_atTop
    simpa [scaleScorePsi] using! h2.sub_const δ

/-! ### Shared envelopes for bounded even ρ-functions

A ρ-function of `MMY §2.5` takes values in `[0,1]`: on `[0,∞)` it increases from
`ρ(0) = 0` to `ρ(∞) = 1`, and evenness carries the bound to the whole line. This supplies
the domination envelope for every integral below. -/

/-- A bounded even ρ-function takes values in `[0,1]`. -/
private theorem rho_mem_Icc {ρ : ℝ → ℝ} (hρ_even : ∀ x, ρ (-x) = ρ x)
    (hρ_mono : MonotoneOn ρ (Set.Ici 0)) (hρ0 : ρ 0 = 0) (hρ_lim : Tendsto ρ atTop (𝓝 1))
    (u : ℝ) : 0 ≤ ρ u ∧ ρ u ≤ 1 := by
  have key : ∀ v : ℝ, 0 ≤ v → 0 ≤ ρ v ∧ ρ v ≤ 1 := by
    intro v hv
    refine ⟨?_, ?_⟩
    · rw [← hρ0]; exact hρ_mono Set.self_mem_Ici (Set.mem_Ici.2 hv) hv
    · refine ge_of_tendsto hρ_lim (eventually_atTop.2 ⟨v, fun w hw => ?_⟩)
      exact hρ_mono (Set.mem_Ici.2 hv) (Set.mem_Ici.2 (hv.trans hw)) hw
  rcases le_or_gt 0 u with h | h
  · exact key u h
  · rw [← hρ_even u]
    exact key (-u) (by linarith)

/-- The scale-equation integrand of a bounded ρ-function is integrable against any
probability measure (`MMY (2.49)`'s standing integrability, discharged). -/
private theorem integrable_rho_div {ρ : ℝ → ℝ} (hb : ∀ u, |ρ u| ≤ 1) (hmeas : Measurable ρ)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (σ : ℝ) :
    Integrable (fun x => ρ (x / σ)) μ := by
  refine Integrable.mono' (integrable_const 1)
    ((hmeas.comp (measurable_id.div_const σ)).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  simpa [Real.norm_eq_abs] using hb (x / σ)

/-- The translation `θ ↦ x − θ` drives `θ → −∞` to `+∞` (the companion in
`MLocationFunctional` is file-private, so it is re-derived here). -/
private theorem tendsto_const_sub_atBot_atTop' (x : ℝ) :
    Tendsto (fun θ : ℝ => x - θ) atBot atTop :=
  tendsto_atTop.2 fun b => eventually_atBot.2 ⟨x - b, fun _ hθ => by linarith⟩

/-- **Scale M-roots resist contamination below `min(δ, 1−δ)`** (`MMY (3.23)`, stability
direction): for a bounded even loss and `ε < min(δ, 1−δ)`, all scale M-roots of all
`ε`-contaminations of `P` lie in a fixed interval `[σ_lo, σ_hi] ⊂ (0, ∞)` — neither
explosion nor implosion. Proved through the log-scale reduction and Round-1's
`mLocationRoot_bounded_of_contamination` (`MMY (3.21)`) with `k₁ = δ`, `k₂ = 1 − δ`,
noting `min(δ, 1−δ)/(δ + (1−δ)) = min(δ, 1−δ)`. -/
theorem mScaleRoot_bounded_of_contamination {ρ : ℝ → ℝ} {δ ε : ℝ} {P : Measure ℝ}
    [IsProbabilityMeasure P]
    -- USER-INPUT: bounded even ρ-function; MMY §2.5 / Definition 2.1
    (hρ_even : ∀ x, ρ (-x) = ρ x) (hρ_mono : MonotoneOn ρ (Set.Ici 0))
    (hρ0 : ρ 0 = 0) (hρ_lim : Tendsto ρ atTop (𝓝 1))
    -- USER-INPUT: continuous loss (see scaleScorePsi_monotone_limits for why this is
    -- forced, not regularity-optional); MMY Thm 10.1-style
    (hρc : Continuous ρ)
    -- USER-INPUT: target level strictly inside (0,1); MMY §2.5 (0 < δ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    -- USER-INPUT: no atom at 0; MMY §3.2.2 (implicit in the log scale)
    (hP0 : P {0} = 0)
    -- USER-INPUT: contamination level below the scale breakdown point; MMY (3.23)
    (hε0 : 0 ≤ ε) (hε : ε < min δ (1 - δ)) :
    ∃ σlo σhi : ℝ, 0 < σlo ∧
      ∀ (Q : Measure ℝ), IsProbabilityMeasure Q → Q {0} = 0 → ∀ σ : ℝ,
        IsMScaleRoot ρ δ (contaminate P Q ε) σ → σ ∈ Set.Icc σlo σhi := by
  have hb := rho_mem_Icc hρ_even hρ_mono hρ0 hρ_lim
  have hbabs : ∀ u, |ρ u| ≤ 1 := fun u => abs_le.2 ⟨by linarith [(hb u).1], (hb u).2⟩
  obtain ⟨hmono, hbot, htop⟩ := scaleScorePsi_monotone_limits (δ := δ) hρ_mono hρ0 hρ_lim hρc
  have hεδ : ε < δ := lt_of_lt_of_le hε (min_le_left _ _)
  have hε1 : ε ≤ 1 := by linarith
  haveI : IsProbabilityMeasure (P.map logAbs) :=
    Measure.isProbabilityMeasure_map measurable_logAbs.aemeasurable
  -- the location breakdown data of `MMY (3.23)`: `k₁ = δ`, `k₂ = 1 − δ`, `k₁ + k₂ = 1`
  obtain ⟨B, hB⟩ := mLocationRoot_bounded_of_contamination (P := P.map logAbs)
    (ψ := scaleScorePsi ρ δ) (k₁ := δ) (k₂ := 1 - δ) hmono hbot htop hδ0 (by linarith) hε0
    (by rw [show δ + (1 - δ) = 1 by ring, div_one]; exact hε)
  refine ⟨Real.exp (-B), Real.exp B, Real.exp_pos _, fun Q hQ hQ0 σ hroot => ?_⟩
  haveI := hQ
  haveI : IsProbabilityMeasure (contaminate P Q ε) := isProbabilityMeasure_contaminate P Q hε0 hε1
  haveI : IsProbabilityMeasure (Q.map logAbs) :=
    Measure.isProbabilityMeasure_map measurable_logAbs.aemeasurable
  have hc0 : (contaminate P Q ε) {(0:ℝ)} = 0 := by rw [contaminate_apply, hP0, hQ0]; simp
  have hσ := hroot.1
  have hloc := (isMScaleRoot_iff_logScale hσ hρ_even hρc.measurable hc0
    (integrable_rho_div hbabs hρc.measurable σ)).1 hroot
  rw [map_contaminate measurable_logAbs] at hloc
  have habs := hB (Q.map logAbs) inferInstance (Real.log σ) hloc
  rw [abs_le] at habs
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · calc Real.exp (-B) ≤ Real.exp (Real.log σ) := Real.exp_le_exp.2 habs.1
      _ = σ := Real.exp_log hσ
  · calc σ = Real.exp (Real.log σ) := (Real.exp_log hσ).symm
      _ ≤ Real.exp B := Real.exp_le_exp.2 habs.2

/-- **Explosion beyond `δ`** (`MMY (3.23)` sharpness, explosion side; `MMY §3.2.2`:
"δ and 1 − δ are, respectively, the BPs for explosion and for implosion"): for
contamination level `ε > δ`, point-mass contamination arbitrarily far out produces
scale M-roots beyond any bound — through the log-scale reduction this is Round-1's
`mLocationRoot_contamination_unbounded` (`MMY (3.22)`) at `k₁ = δ`, `k₂ = 1 − δ`. -/
theorem mScaleRoot_explodes {ρ : ℝ → ℝ} {δ ε : ℝ} {P : Measure ℝ}
    [IsProbabilityMeasure P]
    -- USER-INPUT: bounded even continuous ρ-function; MMY §2.5 + Thm 10.1 regularity
    (hρ_even : ∀ x, ρ (-x) = ρ x) (hρ_mono : MonotoneOn ρ (Set.Ici 0))
    (hρ0 : ρ 0 = 0) (hρ_lim : Tendsto ρ atTop (𝓝 1)) (hρc : Continuous ρ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hP0 : P {0} = 0)
    -- USER-INPUT: contamination level beyond the explosion BP; MMY (3.23)
    (hε : δ < ε) (hε1 : ε < 1) :
    ∀ B : ℝ, ∃ (x₀ σ : ℝ), B < σ ∧
      IsMScaleRoot ρ δ (contaminate P (Measure.dirac x₀) ε) σ := by
  intro B
  have hb := rho_mem_Icc hρ_even hρ_mono hρ0 hρ_lim
  have hbabs : ∀ u, |ρ u| ≤ 1 := fun u => abs_le.2 ⟨by linarith [(hb u).1], (hb u).2⟩
  obtain ⟨hmono, hbot, htop⟩ := scaleScorePsi_monotone_limits (δ := δ) hρ_mono hρ0 hρ_lim hρc
  have hψc : Continuous (scaleScorePsi ρ δ) :=
    (hρc.comp Real.continuous_exp).sub continuous_const
  have hε0 : 0 ≤ ε := le_of_lt (hδ0.trans hε)
  haveI : IsProbabilityMeasure (P.map logAbs) :=
    Measure.isProbabilityMeasure_map measurable_logAbs.aemeasurable
  -- `k₁/(k₁+k₂) = δ < ε` is exactly the explosion side of `MMY (3.23)`
  obtain ⟨t₀, θ, hθgt, hloc⟩ := mLocationRoot_contamination_unbounded (P := P.map logAbs)
    (ψ := scaleScorePsi ρ δ) (k₁ := δ) (k₂ := 1 - δ) hψc hmono hbot htop hδ0 (by linarith)
    (by rw [show δ + (1 - δ) = 1 by ring, div_one]; exact hε) hε1 (Real.log (max B 1))
  have hmax : (0:ℝ) < max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hs : (0:ℝ) < Real.exp t₀ := Real.exp_pos _
  haveI : IsProbabilityMeasure (contaminate P (Measure.dirac (Real.exp t₀)) ε) :=
    isProbabilityMeasure_contaminate P _ hε0 hε1.le
  refine ⟨Real.exp t₀, Real.exp θ, ?_, ?_⟩
  · calc B ≤ max B 1 := le_max_left _ _
      _ = Real.exp (Real.log (max B 1)) := (Real.exp_log hmax).symm
      _ < Real.exp θ := Real.exp_lt_exp.2 hθgt
  · have hc0 : (contaminate P (Measure.dirac (Real.exp t₀)) ε) {(0:ℝ)} = 0 := by
      rw [contaminate_apply, hP0]
      simp [hs.ne']
    refine (isMScaleRoot_iff_logScale (Real.exp_pos θ) hρ_even hρc.measurable hc0
      (integrable_rho_div hbabs hρc.measurable _)).2 ?_
    rw [Real.log_exp, map_contaminate measurable_logAbs,
      Measure.map_dirac (f := logAbs) (Real.exp t₀),
      show logAbs (Real.exp t₀) = t₀ by rw [logAbs, abs_of_pos hs, Real.log_exp]]
    exact hloc

/-- **Implosion beyond `1 − δ`** (`MMY (3.23)` sharpness, implosion side): for
contamination level `ε > 1 − δ`, point-mass contamination by *inliers* at some small
`s > 0` produces scale M-roots below any positive bound.

Why `s > 0` and not `s = 0`: with the whole contaminating mass exactly at `0` the
contaminated equation reads `(1−ε) ∫ρ(x/σ) dP = δ`, whose left side is `< δ` for every
`σ > 0` when `ε > 1 − δ` — the root set is *empty*, which is breakdown by vacuity, not
by implosion. Placing the inliers at `s > 0` restores a root (IVT) and drives it below
`b` as `s → 0`. -/
theorem mScaleRoot_implodes {ρ : ℝ → ℝ} {δ ε : ℝ} {P : Measure ℝ}
    [IsProbabilityMeasure P]
    -- USER-INPUT: bounded even continuous ρ-function; MMY §2.5 + Thm 10.1 regularity
    (hρ_even : ∀ x, ρ (-x) = ρ x) (hρ_mono : MonotoneOn ρ (Set.Ici 0))
    (hρ0 : ρ 0 = 0) (hρ_lim : Tendsto ρ atTop (𝓝 1)) (hρc : Continuous ρ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hP0 : P {0} = 0)
    -- USER-INPUT: contamination level beyond the implosion BP; MMY (3.23)
    (hε : 1 - δ < ε) (hε1 : ε < 1) :
    ∀ b : ℝ, 0 < b → ∃ (s σ : ℝ), 0 < s ∧ 0 < σ ∧ σ < b ∧
      IsMScaleRoot ρ δ (contaminate P (Measure.dirac s) ε) σ := by
  intro b hb
  -- Everything happens in the log scale, where the implosion `σ → 0` is the *mirror* of
  -- the location explosion of `MMY (3.22)` — a direction Round-1 does not carry, so the
  -- IVT is run here, on the transported score.
  have hbnd := rho_mem_Icc hρ_even hρ_mono hρ0 hρ_lim
  have hbabs : ∀ u, |ρ u| ≤ 1 := fun u => abs_le.2 ⟨by linarith [(hbnd u).1], (hbnd u).2⟩
  obtain ⟨hmono, hbot, htop⟩ := scaleScorePsi_monotone_limits (δ := δ) hρ_mono hρ0 hρ_lim hρc
  have hψc : Continuous (scaleScorePsi ρ δ) :=
    (hρc.comp Real.continuous_exp).sub continuous_const
  have hψb : ∀ u, |scaleScorePsi ρ δ u| ≤ 1 := fun u => by
    have h1 := (hbnd (Real.exp u)).1
    have h2 := (hbnd (Real.exp u)).2
    rw [scaleScorePsi, abs_le]
    constructor <;> linarith
  have hε0 : 0 < ε := by linarith
  have hε1' : (0:ℝ) < 1 - ε := by linarith
  haveI : IsProbabilityMeasure (P.map logAbs) :=
    Measure.isProbabilityMeasure_map measurable_logAbs.aemeasurable
  have hint : ∀ θ : ℝ, Integrable (fun y => scaleScorePsi ρ δ (y - θ)) (P.map logAbs) :=
    fun θ => integrable_psi_sub hψc.measurable ⟨1, hψb⟩ θ
  have hcontLam : Continuous (mLocationScore (scaleScorePsi ρ δ) (P.map logAbs)) :=
    continuous_mLocationScore hψc ⟨1, hψb⟩
  have hLamBot : Tendsto (mLocationScore (scaleScorePsi ρ δ) (P.map logAbs)) atBot (𝓝 (1 - δ)) :=
    tendsto_mLocationScore_atBot hmono htop hint
  have hψle : ∀ u, scaleScorePsi ρ δ u ≤ 1 - δ := fun u =>
    ge_of_tendsto htop (eventually_atTop.2 ⟨u, fun v hv => hmono hv⟩)
  have hLamLe : ∀ θ : ℝ, mLocationScore (scaleScorePsi ρ δ) (P.map logAbs) θ ≤ 1 - δ := fun θ => by
    simpa using! integral_mono (hint θ) (integrable_const (1 - δ)) fun y => hψle (y - θ)
  -- (i) push the inlying point mass down until the contaminated score at `log b − 1` is
  -- negative; `ε > 1 − δ` is exactly `(1−ε)(1−δ) < εδ`
  set Bθ : ℝ := Real.log b - 1 with hBθ
  have hkey : (1 - ε) * (1 - δ) < ε * δ := by nlinarith
  obtain ⟨u₀, hu₀⟩ := eventually_atBot.1
    ((hbot.const_mul ε).eventually_lt_const (by linarith : ε * -δ < -((1 - ε) * (1 - δ))))
  set t₀ : ℝ := Bθ + u₀ with ht₀
  have hneg : (1 - ε) * mLocationScore (scaleScorePsi ρ δ) (P.map logAbs) Bθ
      + ε * scaleScorePsi ρ δ (t₀ - Bθ) < 0 := by
    have h1 : ε * scaleScorePsi ρ δ (t₀ - Bθ) < -((1 - ε) * (1 - δ)) := by
      rw [show t₀ - Bθ = u₀ by rw [ht₀]; ring]
      exact hu₀ u₀ le_rfl
    have h2 := mul_le_mul_of_nonneg_left (hLamLe Bθ) hε1'.le
    linarith
  -- (ii) as `θ → −∞` both parts of the contaminated score rise to `1 − δ > 0`
  have hcT : Tendsto (fun θ => (1 - ε) * mLocationScore (scaleScorePsi ρ δ) (P.map logAbs) θ
      + ε * scaleScorePsi ρ δ (t₀ - θ)) atBot (𝓝 ((1 - ε) * (1 - δ) + ε * (1 - δ))) :=
    (hLamBot.const_mul _).add ((htop.comp (tendsto_const_sub_atBot_atTop' t₀)).const_mul _)
  obtain ⟨θ', hθ'⟩ := eventually_atBot.1
    (hcT.eventually_const_lt (by nlinarith : (0:ℝ) < (1 - ε) * (1 - δ) + ε * (1 - δ)))
  -- (iii) the intermediate value theorem on `[min Bθ θ', Bθ]`
  have hcont : Continuous fun θ => (1 - ε) * mLocationScore (scaleScorePsi ρ δ) (P.map logAbs) θ
      + ε * scaleScorePsi ρ δ (t₀ - θ) :=
    (continuous_const.mul hcontLam).add
      (continuous_const.mul (hψc.comp (continuous_const.sub continuous_id)))
  have hle : min Bθ θ' ≤ Bθ := min_le_left _ _
  have hpos := hθ' _ (min_le_right Bθ θ')
  obtain ⟨θ, hθmem, hθ0⟩ :=
    intermediate_value_Icc' hle hcont.continuousOn (Set.mem_Icc.2 ⟨hneg.le, hpos.le⟩)
  have hs : (0:ℝ) < Real.exp t₀ := Real.exp_pos _
  haveI : IsProbabilityMeasure (contaminate P (Measure.dirac (Real.exp t₀)) ε) :=
    isProbabilityMeasure_contaminate P _ hε0.le hε1.le
  refine ⟨Real.exp t₀, Real.exp θ, hs, Real.exp_pos _, ?_, ?_⟩
  · calc Real.exp θ ≤ Real.exp Bθ := Real.exp_le_exp.2 hθmem.2
      _ < Real.exp (Real.log b) := Real.exp_lt_exp.2 (by rw [hBθ]; linarith)
      _ = b := Real.exp_log hb
  · have hc0 : (contaminate P (Measure.dirac (Real.exp t₀)) ε) {(0:ℝ)} = 0 := by
      rw [contaminate_apply, hP0]
      simp [hs.ne']
    refine (isMScaleRoot_iff_logScale (Real.exp_pos θ) hρ_even hρc.measurable hc0
      (integrable_rho_div hbabs hρc.measurable _)).2 ?_
    rw [Real.log_exp, map_contaminate measurable_logAbs,
      Measure.map_dirac (f := logAbs) (Real.exp t₀),
      show logAbs (Real.exp t₀) = t₀ by rw [logAbs, abs_of_pos hs, Real.log_exp]]
    show ∫ y, scaleScorePsi ρ δ (y - θ) ∂(contaminate (P.map logAbs) (Measure.dirac t₀) ε) = 0
    rw [integral_contaminate_dirac hε0.le hε1.le (hint θ)]
    exact hθ0

end StatLean.RobustStatistics
