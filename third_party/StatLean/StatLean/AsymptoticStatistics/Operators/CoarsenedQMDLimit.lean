module
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.Operators.InformationLoss
public import StatLean.AsymptoticStatistics.ForMathlib.SigmaFiniteTrimComap
public import StatLean.AsymptoticStatistics.ForMathlib.CondExpCauchySchwarz
public import StatLean.AsymptoticStatistics.ForMathlib.RnDerivSqrt
public import StatLean.AsymptoticStatistics.ForMathlib.CondExpL2
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Measure.WithDensityFinite

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# QMD limit for the coarsened path (vdV Lem 25.34-I, the `qmd_limit` field)

The score-preservation estimate is the `qmd_limit` property of
`QMDPath.coarsen` (vdV Lemma 25.34 half I, book p.375, whose proof van der Vaart
refers to [139, pp.188-193]).

Proof outline (denominator-safe conditional-projection domination):
writing `p̄ t := (dQ_t/dμ).toReal`, `ξ t := √(p̄ t)`, `q̃ t := μ[p̄ t | comap M]`,
`cross t := μ[ξt·ξ0 | comap M]`, `A t := cross t / √q̃0` (guarded), the pulled-back
field residual splits as
`RES = [A − √q̃0 − (t/2)(Π∘M)√q̃0] + [√q̃t − A]`, whose two brackets are each
`o(t)` in `L²(μ)` (the first by conditional Cauchy–Schwarz on the QMD remainder,
the second by a `ρ`-ratio DCT-along-subsequence argument).

The definitions `pbar`, `xi`, `qtilde`, `cross`, `Cdom`, `Acoef`, and `rho`
denote the quantities in this decomposition.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.dupNamespace false

namespace AsymptoticStatistics.Core.QMDPath

open AsymptoticStatistics.Operators.InformationLoss
open AsymptoticStatistics.ForMathlib.QMDAnalytic
open AsymptoticStatistics.ForMathlib.CondExpL2

section Coarsen

variable {Ω_full Ω_obs : Type*}
  [MeasurableSpace Ω_full] [MeasurableSpace Ω_obs]
  {M : Ω_full → Ω_obs}
  {P_full : Measure Ω_full} [IsProbabilityMeasure P_full]

/-! ## Finite equivalent dominating measure -/

/-- **Change of dominating measure.** Multiplication by the square root
of `dν/dν.toFinite` identifies the `L²(ν.toFinite)` seminorm with `L²(ν)`.

This is the minimal analytic layer needed to rebase a `QMDPath`; it is not part
of vdV Lemma 25.34-I's statistical content. -/
private lemma eLpNorm_sqrt_rnDeriv_toFinite_mul_eq
    (ν : Measure Ω_full) [SigmaFinite ν] {f : Ω_full → ℝ} (hf : Measurable f) :
    eLpNorm (fun ω => Real.sqrt (ν.rnDeriv ν.toFinite ω).toReal * f ω) 2 ν.toFinite
      = eLpNorm f 2 ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [htwo]
  congr 1
  have h_integrand :
      (fun ω => ‖Real.sqrt (ν.rnDeriv ν.toFinite ω).toReal * f ω‖ₑ ^ (2 : ℝ))
        =ᵐ[ν.toFinite] fun ω => ν.rnDeriv ν.toFinite ω * ‖f ω‖ₑ ^ (2 : ℝ) := by
    filter_upwards [Measure.rnDeriv_lt_top ν ν.toFinite] with ω hω
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [Real.enorm_of_nonneg (Real.sqrt_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two, Real.sq_sqrt ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hω.ne]
  rw [lintegral_congr_ae h_integrand]
  exact lintegral_rnDeriv_mul (absolutelyContinuous_toFinite ν)
    ((hf.enorm.pow_const (2 : ℝ)).aemeasurable)

/-- **QMD change-of-dominator identity.** Computing a path's QMD
residual against the equivalent finite dominator preserves its `L²` seminorm.
The RN chain rule factors the new residual by `sqrt (dμ/dμ.toFinite)`, which is
absorbed by `eLpNorm_sqrt_rnDeriv_toFinite_mul_eq`. -/
private lemma eLpNorm_qmdResidual_toFinite_eq (γ : QMDPath P_full) (t : ℝ) :
    eLpNorm (fun ω =>
        Real.sqrt ((γ.curve t).rnDeriv γ.dominating.toFinite ω).toReal
        - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating.toFinite ω).toReal
        - (t / 2) * (γ.score : Ω_full → ℝ) ω
            * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating.toFinite ω).toReal)
      2 γ.dominating.toFinite
      = eLpNorm (fun ω =>
        Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
        - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
        - (t / 2) * (γ.score : Ω_full → ℝ) ω
            * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal)
      2 γ.dominating := by
  haveI := γ.curve_isProbability t
  haveI := γ.curve_isProbability 0
  have hscore : Measurable (γ.score : Ω_full → ℝ) :=
    (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P_full)).measurable
  have hres : Measurable (fun ω =>
      Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
      - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
      - (t / 2) * (γ.score : Ω_full → ℝ) ω
          * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal) := by
    have ht := (Measure.measurable_rnDeriv (γ.curve t) γ.dominating).ennreal_toReal.sqrt
    have h0 := (Measure.measurable_rnDeriv (γ.curve 0) γ.dominating).ennreal_toReal.sqrt
    exact (ht.sub h0).sub ((measurable_const.mul hscore).mul h0)
  have hfactor : (fun ω =>
        Real.sqrt ((γ.curve t).rnDeriv γ.dominating.toFinite ω).toReal
        - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating.toFinite ω).toReal
        - (t / 2) * (γ.score : Ω_full → ℝ) ω
            * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating.toFinite ω).toReal)
      =ᵐ[γ.dominating.toFinite] fun ω =>
        Real.sqrt (γ.dominating.rnDeriv γ.dominating.toFinite ω).toReal *
          (Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
          - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
          - (t / 2) * (γ.score : Ω_full → ℝ) ω
              * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal) := by
    have ht := Measure.rnDeriv_mul_rnDeriv (κ := γ.dominating.toFinite)
      (γ.curve_absContinuous t)
    have h0 := Measure.rnDeriv_mul_rnDeriv (κ := γ.dominating.toFinite)
      (γ.curve_absContinuous 0)
    filter_upwards [ht, h0] with ω htω h0ω
    have hsqrt_t : Real.sqrt ((γ.curve t).rnDeriv γ.dominating.toFinite ω).toReal
        = Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
            * Real.sqrt (γ.dominating.rnDeriv γ.dominating.toFinite ω).toReal := by
      rw [← htω, Pi.mul_apply, ENNReal.toReal_mul,
        Real.sqrt_mul ENNReal.toReal_nonneg]
    have hsqrt_0 : Real.sqrt ((γ.curve 0).rnDeriv γ.dominating.toFinite ω).toReal
        = Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
            * Real.sqrt (γ.dominating.rnDeriv γ.dominating.toFinite ω).toReal := by
      rw [← h0ω, Pi.mul_apply, ENNReal.toReal_mul,
        Real.sqrt_mul ENNReal.toReal_nonneg]
    rw [hsqrt_t, hsqrt_0]
    ring
  rw [eLpNorm_congr_ae hfactor]
  exact eLpNorm_sqrt_rnDeriv_toFinite_mul_eq γ.dominating hres

/-- **Finite equivalent-dominator representation of a QMD path.**

For every dominated QMD path `γ`, this packages a representation of the same
measure-valued curve, at the same base probability measure and with the same score,
whose dominating measure is the equivalent finite measure
`γ.dominating.toFinite`. This finite measure can be pushed forward through any
measurable coarsening while retaining sigma-finiteness. `Measure.toFinite` has
the same null sets as the original sigma-finite dominating measure, and the QMD
residual has the same `L²` seminorm by
`eLpNorm_qmdResidual_toFinite_eq`. No additional statistical regularity
assumption is introduced. -/
noncomputable def finiteDominatorRepresentation (gamma : QMDPath P_full) :
    {gamma' : QMDPath P_full //
      gamma'.curve = gamma.curve ∧
      gamma'.dominating = gamma.dominating.toFinite ∧
      gamma'.score = gamma.score} := by
  let gamma' : QMDPath P_full :=
    { curve := gamma.curve
      curve_at_zero := gamma.curve_at_zero
      curve_isProbability := gamma.curve_isProbability
      dominating := gamma.dominating.toFinite
      curve_absContinuous := fun t =>
        (gamma.curve_absContinuous t).trans (absolutelyContinuous_toFinite gamma.dominating)
      dominating_sigmaFinite := inferInstance
      score := gamma.score
      qmd_limit := gamma.qmd_limit.congr fun t => by
        rw [eLpNorm_qmdResidual_toFinite_eq gamma t] }
  exact ⟨gamma', rfl, rfl, rfl⟩

/-! ## Notation-packaging definitions (vdV Lem 25.34-I) -/

/-- Constitutive (vdV Lem 25.34-I, book p.375): the real-valued density
`p̄ t ω = (dQ_t/dμ)(ω)` of the full-data curve against the dominating measure. -/
noncomputable def pbar (γ : QMDPath P_full) (t : ℝ) : Ω_full → ℝ :=
  fun ω => ((γ.curve t).rnDeriv γ.dominating ω).toReal

/-- Constitutive (vdV Lem 25.34-I, book p.375): the square-root density
`ξ t ω = √(p̄ t ω)`. -/
noncomputable def xi (γ : QMDPath P_full) (t : ℝ) : Ω_full → ℝ :=
  fun ω => Real.sqrt (pbar γ t ω)

/-- Constitutive (vdV Lem 25.34-I, book p.375): the coarsened density
`q̃ t = μ[p̄ t | comap M]`, the conditional expectation of the full-data density
under the observation σ-algebra. -/
noncomputable def qtilde (_hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) :
    Ω_full → ℝ :=
  γ.dominating[pbar γ t | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]

/-- Constitutive (vdV Lem 25.34-I, book p.375): the conditional cross term
`cross t = μ[ξt·ξ0 | comap M]`. -/
noncomputable def cross (_hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) :
    Ω_full → ℝ :=
  γ.dominating[(fun ω => xi γ t ω * xi γ 0 ω)
    | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]

/-- Constitutive (vdV Lem 25.34-I, book p.375): the `t`-independent DCT
dominator `Cdom = μ[(s·ξ0)² | comap M]`. -/
noncomputable def Cdom (_hM : Measurable M) (γ : QMDPath P_full) : Ω_full → ℝ :=
  γ.dominating[(fun ω => ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω) ^ 2)
    | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]

/-- Constitutive (vdV Lem 25.34-I, book p.375): the denominator-safe coefficient
`A t = cross t / √q̃0` on `{q̃0 > 0}`, and `0` elsewhere. -/
noncomputable def Acoef (hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) :
    Ω_full → ℝ :=
  fun ω =>
    if 0 < qtilde hM γ 0 ω then cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω) else 0

/-- Constitutive (vdV Lem 25.34-I, book p.375): the `ρ`-ratio
`ρ t = (√q̃t − A t) / (√q̃t + A t)` on `{√q̃t + A t > 0}`, and `0` elsewhere.
Takes values in `[0, 1]` and drives the DCT dominated convergence. -/
noncomputable def rho (hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) :
    Ω_full → ℝ :=
  fun ω =>
    if 0 < Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω
    then (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω)
          / (Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω)
    else 0

/-! ## Definitional unfold lemmas -/

lemma pbar_apply (γ : QMDPath P_full) (t : ℝ) (ω : Ω_full) :
    pbar γ t ω = ((γ.curve t).rnDeriv γ.dominating ω).toReal := rfl

lemma xi_apply (γ : QMDPath P_full) (t : ℝ) (ω : Ω_full) :
    xi γ t ω = Real.sqrt (((γ.curve t).rnDeriv γ.dominating ω).toReal) := rfl

lemma qtilde_apply (hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) :
    qtilde hM γ t
      = γ.dominating[pbar γ t | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›] :=
  rfl

lemma cross_apply (hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) :
    cross hM γ t
      = γ.dominating[(fun ω => xi γ t ω * xi γ 0 ω)
          | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›] := rfl

lemma Cdom_apply (hM : Measurable M) (γ : QMDPath P_full) :
    Cdom hM γ
      = γ.dominating[(fun ω => ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω) ^ 2)
          | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›] := rfl

lemma Acoef_apply (hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) (ω : Ω_full) :
    Acoef hM γ t ω
      = if 0 < qtilde hM γ 0 ω then cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω)
        else 0 := rfl

lemma Acoef_of_pos (hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) (ω : Ω_full)
    (h : 0 < qtilde hM γ 0 ω) :
    Acoef hM γ t ω = cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω) := by
  rw [Acoef_apply, if_pos h]

lemma Acoef_of_zero (hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) (ω : Ω_full)
    (h : ¬ 0 < qtilde hM γ 0 ω) :
    Acoef hM γ t ω = 0 := by
  rw [Acoef_apply, if_neg h]

lemma rho_apply (hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) (ω : Ω_full) :
    rho hM γ t ω
      = if 0 < Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω
        then (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω)
              / (Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω)
        else 0 := rfl

lemma rho_of_pos (hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) (ω : Ω_full)
    (h : 0 < Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω) :
    rho hM γ t ω = (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω)
      / (Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω) := by
  rw [rho_apply, if_pos h]

lemma rho_of_zero (hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) (ω : Ω_full)
    (h : ¬ 0 < Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω) :
    rho hM γ t ω = 0 := by
  rw [rho_apply, if_neg h]

/-! ## Auxiliary lemmas -/

/-- **Density transport.** Pulling back the coarsened square-root density
along `M` gives `√q̃ t`, a.e. under `μ = γ.dominating`. -/
theorem coarsen_density_transport (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    (fun ω => Real.sqrt
        (((γ.curve t).map M).rnDeriv (γ.dominating.map M) (M ω)).toReal)
      =ᵐ[γ.dominating] fun ω => Real.sqrt (qtilde hM γ t ω) := by
  haveI := γ.curve_isProbability t
  filter_upwards [toReal_rnDeriv_map (γ.curve_absContinuous t) hM] with ω hω
  exact congrArg Real.sqrt hω

/-- **B** — Bayes bridge (linchpin). The conditional expectation of `s·p̄0`
factors as `(Π∘M)·q̃0`, via the Doob sub-identity `Π∘M =ᵐ[P] P[s|comap M]`. -/
theorem coarsen_bayes_bridge (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] :
    γ.dominating[(fun ω => (γ.score : Ω_full → ℝ) ω * pbar γ 0 ω)
        | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]
      =ᵐ[γ.dominating]
        fun ω => (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
          * qtilde hM γ 0 ω := by
  classical
  -- σ-finite side conditions for the `μ`- and `P_full`-trims of `comap M`.
  have hm : MeasurableSpace.comap M ‹MeasurableSpace Ω_obs› ≤ ‹MeasurableSpace Ω_full› :=
    hM.comap_le
  haveI hσμ : SigmaFinite (γ.dominating.trim hm) :=
    AsymptoticStatistics.ForMathlib.SigmaFiniteTrimComap.sigmaFinite_trim_comap_of_sigmaFinite_map
      γ.dominating hM
  haveI hPmap : IsProbabilityMeasure (P_full.map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  haveI hσP : SigmaFinite (P_full.trim hm) :=
    AsymptoticStatistics.ForMathlib.SigmaFiniteTrimComap.sigmaFinite_trim_comap_of_sigmaFinite_map
      P_full hM
  -- `P_full ≪ μ` and the pointwise rnDeriv form of `pbar γ 0`.
  have h_ac : P_full ≪ γ.dominating := by
    have h := γ.curve_absContinuous 0; rwa [γ.curve_at_zero] at h
  have hp0 : ∀ ω, pbar γ 0 ω = (P_full.rnDeriv γ.dominating ω).toReal := by
    intro ω; rw [pbar_apply, γ.curve_at_zero]
  -- `s ∈ L¹(P_full)`.
  have hs_mem : MemLp (γ.score : Ω_full → ℝ) 2 P_full := Lp.memLp _
  have hs_int_P : Integrable (γ.score : Ω_full → ℝ) P_full := hs_mem.integrable one_le_two
  -- Doob sub-identity `Π∘M =ᵐ[P_full] P_full[s | comap M]`.
  have hDoob : (fun ω => (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω))
      =ᵐ[P_full]
        P_full[(γ.score : Ω_full → ℝ) | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›] := by
    have h1 := informationLossOperator_coe_eq hM P_full γ.score
    have h2 := doobL2Equiv_comp_apply hM
      (condExpL2 ℝ ℝ hM.comap_le (γ.score : Lp ℝ 2 P_full))
    have h3 := MemLp.condExpL2_ae_eq_condExp (𝕜 := ℝ) hM.comap_le hs_mem
    have htoLp : MemLp.toLp (γ.score : Ω_full → ℝ) hs_mem = (γ.score : Lp ℝ 2 P_full) :=
      Lp.toLp_coeFn (γ.score : Lp ℝ 2 P_full) hs_mem
    rw [htoLp] at h3
    have h_fun : (fun ω => (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω))
        = fun ω => (doobL2Equiv hM (condExpL2 ℝ ℝ hM.comap_le (γ.score : Lp ℝ 2 P_full))
            : Ω_obs → ℝ) (M ω) := by
      funext ω
      exact congrArg (fun φ : Lp ℝ 2 (P_full.map M) => (φ : Ω_obs → ℝ) (M ω)) h1
    rw [h_fun]
    exact h2.trans h3
  -- Integrability facts under `μ = γ.dominating`.
  have hp0_int : Integrable (pbar γ 0) γ.dominating := by
    have h : Integrable (fun ω => (P_full.rnDeriv γ.dominating ω).toReal) γ.dominating :=
      Measure.integrable_toReal_rnDeriv
    exact h.congr (Filter.Eventually.of_forall (fun ω => (hp0 ω).symm))
  have hsp0_int : Integrable
      (fun ω => (γ.score : Ω_full → ℝ) ω * pbar γ 0 ω) γ.dominating := by
    have heq : (fun ω => (γ.score : Ω_full → ℝ) ω * pbar γ 0 ω)
        = fun x => (P_full.rnDeriv γ.dominating x).toReal * (γ.score : Ω_full → ℝ) x := by
      funext ω; rw [hp0 ω]; ring
    rw [heq]
    exact (integrable_toReal_rnDeriv_mul_iff h_ac).mpr hs_int_P
  have hPiM_int_P : Integrable
      (fun ω => (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)) P_full :=
    integrable_condExp.congr hDoob.symm
  have hPiMp0_int : Integrable
      (fun ω => (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
        * pbar γ 0 ω) γ.dominating := by
    have heq : (fun ω => (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
          * pbar γ 0 ω)
        = fun x => (P_full.rnDeriv γ.dominating x).toReal
          * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M x) := by
      funext ω; rw [hp0 ω]; ring
    rw [heq]
    exact (integrable_toReal_rnDeriv_mul_iff h_ac).mpr hPiM_int_P
  -- `Π∘M` is `comap M`-strongly measurable (an `Lp` representative composed with `M`).
  have hPiM_sm : StronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]
      (fun ω => (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)) :=
    (Lp.stronglyMeasurable
        (↑(informationLossOperator hM P_full γ.score) : Lp ℝ 2 (P_full.map M))).comp_measurable
      (measurable_iff_comap_le.mpr le_rfl)
  have hq0_sm : StronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]
      (qtilde hM γ 0) := stronglyMeasurable_condExp
  -- Pull-out: `μ[(Π∘M)·p̄0 | 𝒢] =ᵐ (Π∘M)·q̃0`.
  have hpull : γ.dominating[(fun ω =>
        (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω) * pbar γ 0 ω)
        | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]
      =ᵐ[γ.dominating]
        fun ω => (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
          * qtilde hM γ 0 ω :=
    condExp_mul_of_stronglyMeasurable_left hPiM_sm hPiMp0_int hp0_int
  have hgm : AEStronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]
      (fun ω => (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
        * qtilde hM γ 0 ω) γ.dominating :=
    (hPiM_sm.mul hq0_sm).aestronglyMeasurable
  have hg_int : Integrable (fun ω =>
      (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
        * qtilde hM γ 0 ω) γ.dominating :=
    integrable_condExp.congr hpull
  -- Close via the abstract characterization of conditional expectation.
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hsp0_int
    (fun G' _ _ => hg_int.integrableOn) ?_ hgm).symm
  intro G hG _
  have hGbase : MeasurableSet G := hm G hG
  -- Transfer both set integrals to the `pbar`-weighted dominating measure.
  have adaptPiM : ∫ ω in G, (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω) ∂P_full
      = ∫ ω in G, ((informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
          * pbar γ 0 ω) ∂γ.dominating := by
    rw [AsymptoticStatistics.ForMathlib.RnDerivSqrt.setIntegral_eq_setIntegral_mul_rnDeriv_of_ac
          h_ac (fun ω => (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)) hGbase]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [hp0]
  have adaptS : ∫ ω in G, (γ.score : Ω_full → ℝ) ω ∂P_full
      = ∫ ω in G, ((γ.score : Ω_full → ℝ) ω * pbar γ 0 ω) ∂γ.dominating := by
    rw [AsymptoticStatistics.ForMathlib.RnDerivSqrt.setIntegral_eq_setIntegral_mul_rnDeriv_of_ac
          h_ac (γ.score : Ω_full → ℝ) hGbase]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [hp0]
  -- Chain: `∫_G (Π∘M)·q̃0 dμ = ∫_G s·p̄0 dμ`.
  have step1 := (setIntegral_congr_ae hGbase
      (Filter.Eventually.mono hpull.symm (fun x hx _ => hx))).trans
    (setIntegral_condExp hm hPiMp0_int hG)
  have step3 := setIntegral_congr_ae (μ := P_full) hGbase
      (Filter.Eventually.mono hDoob (fun x hx _ => hx))
  have step4 := setIntegral_condExp hm hs_int_P hG
  exact step1.trans (adaptPiM.symm.trans (step3.trans (step4.trans adaptS)))

/-! ## Shared pointwise / conditional-expectation helpers (P-cluster) -/

private lemma pbar_nonneg (γ : QMDPath P_full) (t : ℝ) (ω : Ω_full) :
    0 ≤ pbar γ t ω := by rw [pbar_apply]; exact ENNReal.toReal_nonneg

private lemma xi_sq (γ : QMDPath P_full) (t : ℝ) (ω : Ω_full) :
    xi γ t ω ^ 2 = pbar γ t ω := by
  rw [xi_apply, pbar_apply]; exact Real.sq_sqrt ENNReal.toReal_nonneg

/-- `μ[ξt² | comap M] = q̃t`, since `ξt² = p̄t` pointwise. -/
private lemma condExp_xi_sq_eq_qtilde (hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) :
    γ.dominating[(fun ω => xi γ t ω ^ 2)
        | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]
      = qtilde hM γ t := by
  have h : (fun ω => xi γ t ω ^ 2) = pbar γ t := funext (fun ω => xi_sq γ t ω)
  rw [h]
  exact (qtilde_apply hM γ t).symm

/-- `q̃t ≥ 0` a.e. (conditional expectation of `p̄t ≥ 0`). -/
private lemma qtilde_nonneg (hM : Measurable M) (γ : QMDPath P_full) (t : ℝ) :
    0 ≤ᵐ[γ.dominating] qtilde hM γ t := by
  rw [qtilde_apply hM]
  exact condExp_nonneg (Filter.Eventually.of_forall (fun ω => pbar_nonneg γ t ω))

/-- Cauchy–Schwarz core for the cross term, factored so `A_sq_le` (which precedes
`cross_sq_le` textually) can consume it. -/
private theorem cross_sq_le_helper (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    (fun ω => cross hM γ t ω ^ 2)
      ≤ᵐ[γ.dominating] fun ω => qtilde hM γ t ω * qtilde hM γ 0 ω := by
  haveI hσμ : SigmaFinite (γ.dominating.trim hM.comap_le) :=
    AsymptoticStatistics.ForMathlib.SigmaFiniteTrimComap.sigmaFinite_trim_comap_of_sigmaFinite_map
      γ.dominating hM
  haveI hpt : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  haveI hp0 : IsProbabilityMeasure (γ.curve 0) := γ.curve_isProbability 0
  have hξt : MemLp (xi γ t) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous t)
  have hξ0 : MemLp (xi γ 0) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous 0)
  have hCS := AsymptoticStatistics.ForMathlib.CondExpCauchySchwarz.condExp_sq_le_condExp_mul_condExp
    (μ := γ.dominating) (m := MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
    hM.comap_le hξt hξ0
  filter_upwards [hCS] with ω hω
  rw [cross_apply hM γ t, ← condExp_xi_sq_eq_qtilde hM γ t, ← condExp_xi_sq_eq_qtilde hM γ 0]
  exact hω

/-- The bound `A t² ≤ q̃t` holds almost everywhere by conditional
Cauchy--Schwarz. -/
theorem A_sq_le (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    (fun ω => Acoef hM γ t ω ^ 2) ≤ᵐ[γ.dominating] qtilde hM γ t := by
  filter_upwards [cross_sq_le_helper hM γ t, qtilde_nonneg hM γ t, qtilde_nonneg hM γ 0]
    with ω hCS hqt _hq0
  rcases le_or_gt (qtilde hM γ 0 ω) 0 with hnp | hpos
  · rw [Acoef_of_zero hM γ t ω (not_lt.mpr hnp)]; simpa using hqt
  · rw [Acoef_of_pos hM γ t ω hpos, div_pow, Real.sq_sqrt hpos.le, div_le_iff₀ hpos]
    exact hCS

/-- The bound `cross t² ≤ q̃t · q̃0` holds almost everywhere by conditional
Cauchy--Schwarz. -/
theorem cross_sq_le (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    (fun ω => cross hM γ t ω ^ 2)
      ≤ᵐ[γ.dominating] fun ω => qtilde hM γ t ω * qtilde hM γ 0 ω :=
  cross_sq_le_helper hM γ t

/-- The coefficient `A t` is nonnegative almost everywhere. -/
theorem A_nonneg (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    0 ≤ᵐ[γ.dominating] Acoef hM γ t := by
  have hcross_nn : 0 ≤ᵐ[γ.dominating] cross hM γ t := by
    rw [cross_apply hM γ t]
    exact condExp_nonneg (Filter.Eventually.of_forall (fun ω =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  filter_upwards [hcross_nn] with ω hcr
  rcases le_or_gt (qtilde hM γ 0 ω) 0 with hnp | hpos
  · simp [Acoef_of_zero hM γ t ω (not_lt.mpr hnp)]
  · rw [Acoef_of_pos hM γ t ω hpos]
    exact div_nonneg hcr (Real.sqrt_nonneg _)

/-- The cross term vanishes almost everywhere on `{q̃0 = 0}`. -/
theorem cross_eq_zero_of_qtilde_zero (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    ∀ᵐ ω ∂γ.dominating, qtilde hM γ 0 ω = 0 → cross hM γ t ω = 0 := by
  filter_upwards [cross_sq_le_helper hM γ t] with ω hCS hq0
  rw [hq0, mul_zero] at hCS
  have hsq : cross hM γ t ω ^ 2 = 0 := le_antisymm hCS (sq_nonneg _)
  exact sq_eq_zero_iff.mp hsq

/-- The conditional-projection bound
`q̃t − A t² ≤ μ[(ξt − ξ0)² | comap M]` holds almost everywhere. -/
theorem qtil_diff_le (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    (fun ω => qtilde hM γ t ω - Acoef hM γ t ω ^ 2)
      ≤ᵐ[γ.dominating]
        γ.dominating[(fun ω => (xi γ t ω - xi γ 0 ω) ^ 2)
          | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›] := by
  haveI hpt : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  haveI hp0 : IsProbabilityMeasure (γ.curve 0) := γ.curve_isProbability 0
  have hξt : MemLp (xi γ t) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous t)
  have hξ0 : MemLp (xi γ 0) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous 0)
  have hu : Integrable (fun ω => xi γ t ω ^ 2) γ.dominating := hξt.integrable_sq
  have hw : Integrable (fun ω => xi γ 0 ω ^ 2) γ.dominating := hξ0.integrable_sq
  have hv : Integrable (fun ω => xi γ t ω * xi γ 0 ω) γ.dominating := hξt.integrable_mul hξ0
  have hUW : Integrable ((fun ω => xi γ t ω ^ 2) + fun ω => xi γ 0 ω ^ 2) γ.dominating :=
    hu.add hw
  have h2V : Integrable ((2 : ℝ) • fun ω => xi γ t ω * xi γ 0 ω) γ.dominating :=
    Integrable.smul (2 : ℝ) hv
  have hfn : (fun ω => (xi γ t ω - xi γ 0 ω) ^ 2)
      = ((fun ω => xi γ t ω ^ 2) + fun ω => xi γ 0 ω ^ 2)
        - (2 : ℝ) • fun ω => xi γ t ω * xi γ 0 ω := by
    funext ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsub := condExp_sub hUW h2V (MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
  have hadd := condExp_add hu hw (MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
  have hsmul := condExp_smul (μ := γ.dominating) (2 : ℝ) (fun ω => xi γ t ω * xi γ 0 ω)
    (MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
  have hcU := condExp_xi_sq_eq_qtilde hM γ t
  have hcW := condExp_xi_sq_eq_qtilde hM γ 0
  have hcV := (cross_apply hM γ t).symm
  have hexp : γ.dominating[(fun ω => (xi γ t ω - xi γ 0 ω) ^ 2)
        | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]
      =ᵐ[γ.dominating]
        fun ω => qtilde hM γ t ω - 2 * cross hM γ t ω + qtilde hM γ 0 ω := by
    rw [hfn]
    filter_upwards [hsub, hadd, hsmul] with ω h1 h2 h3
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
    rw [h1, h2, h3, congrFun hcU ω, congrFun hcW ω, congrFun hcV ω]
    ring
  filter_upwards [hexp, cross_eq_zero_of_qtilde_zero hM γ t, qtilde_nonneg hM γ 0]
    with ω hexpω hP1d hq0nn
  rw [hexpω]
  rcases le_or_gt (qtilde hM γ 0 ω) 0 with hnp | hpos
  · have hq0 : qtilde hM γ 0 ω = 0 := le_antisymm hnp hq0nn
    have hcr : cross hM γ t ω = 0 := hP1d hq0
    have hA0 : Acoef hM γ t ω = 0 := Acoef_of_zero hM γ t ω (not_lt.mpr hnp)
    have h00 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [hA0, hcr, hq0]
    linarith
  · have hAsq : Acoef hM γ t ω ^ 2 = cross hM γ t ω ^ 2 / qtilde hM γ 0 ω := by
      rw [Acoef_of_pos hM γ t ω hpos, div_pow, Real.sq_sqrt hpos.le]
    have hkey : 2 * cross hM γ t ω - qtilde hM γ 0 ω ≤ Acoef hM γ t ω ^ 2 := by
      rw [hAsq, le_div_iff₀ hpos]
      nlinarith [sq_nonneg (cross hM γ t ω - qtilde hM γ 0 ω)]
    linarith

/-- The conditional square-root increment satisfies
`μ[(ξt − ξ0)² | comap M] ≤ (t²/2)·Cdom + 2·μ[rt² | comap M]` almost everywhere. -/
theorem condExp_sq_diff_le (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    γ.dominating[(fun ω => (xi γ t ω - xi γ 0 ω) ^ 2)
        | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]
      ≤ᵐ[γ.dominating]
        fun ω => t ^ 2 / 2 * Cdom hM γ ω
          + 2 * (γ.dominating[(fun ω' =>
              qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
              | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω := by
  -- Score coercion is measurable (StronglyMeasurable representative of `Lp`).
  have hscore_meas : Measurable (γ.score : Ω_full → ℝ) :=
    (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P_full)).measurable
  -- L²(μ) memberships of `√pₜ`, `√p₀` and `s·√p₀`.
  haveI hpt : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  haveI hp0 : IsProbabilityMeasure (γ.curve 0) := γ.curve_isProbability 0
  have hξt : MemLp (xi γ t) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
      (γ.curve_absContinuous t)
  have hξ0 : MemLp (xi γ 0) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
      (γ.curve_absContinuous 0)
  have hξdiff : MemLp (fun ω => xi γ t ω - xi γ 0 ω) 2 γ.dominating := hξt.sub hξ0
  have hsξ0 : MemLp (fun ω => (γ.score : Ω_full → ℝ) ω * xi γ 0 ω) 2 γ.dominating :=
    memLp_two_score_mul_sqrt_of_qmd (g := (γ.score : Ω_full → ℝ))
      γ.curve_isProbability γ.curve_absContinuous hscore_meas γ.qmd_limit
  -- The QMD remainder is in L²(μ) (all `t`, not just eventually).
  have hrt : MemLp (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t)
      2 γ.dominating := by
    have heq : qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t
        = fun ω => (xi γ t ω - xi γ 0 ω)
            - (t / 2) * ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω) := by
      funext ω; simp only [qmdRem, xi_apply, pbar_apply]; ring
    rw [heq]
    exact hξdiff.sub (hsξ0.const_mul (t / 2))
  -- Surface `Cdom` and name the three functions. (Do NOT bind the σ-algebra to a
  -- local `G : MeasurableSpace Ω_full`: it would pollute instance resolution for
  -- `Ω_full` in the `xi`/`qmdRem` elaborations below.)
  rw [Cdom_apply hM γ]
  set B := fun ω => ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω) ^ 2 with hB
  set A := fun ω' => qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2 with hA
  set LHSf := fun ω => (xi γ t ω - xi γ 0 ω) ^ 2 with hLHSf
  -- Integrability of the squares and their scalings.
  have hA_int : Integrable A γ.dominating := by rw [hA]; exact hrt.integrable_sq
  have hB_int : Integrable B γ.dominating := by rw [hB]; exact hsξ0.integrable_sq
  have hLHS_int : Integrable LHSf γ.dominating := by
    rw [hLHSf]; exact hξdiff.integrable_sq
  have hI2A : Integrable ((2 : ℝ) • A) γ.dominating := Integrable.smul (2 : ℝ) hA_int
  have hI2B : Integrable ((t ^ 2 / 2 : ℝ) • B) γ.dominating :=
    Integrable.smul (t ^ 2 / 2 : ℝ) hB_int
  have hRHS_int : Integrable ((2 : ℝ) • A + (t ^ 2 / 2 : ℝ) • B) γ.dominating :=
    hI2A.add hI2B
  -- Pointwise `(ξₜ − ξ₀)² ≤ 2 rₜ² + (t²/2)(s·ξ₀)²` from `2ab ≤ a² + b²`.
  have hbound' : LHSf ≤ᵐ[γ.dominating] (2 : ℝ) • A + (t ^ 2 / 2 : ℝ) • B := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simp only [hLHSf, hA, hB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hid : xi γ t ω - xi γ 0 ω
        = qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω
          + t / 2 * ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω) := by
      simp only [qmdRem, xi_apply]; ring
    rw [hid]
    nlinarith [sq_nonneg (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω
      - t / 2 * ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω))]
  -- Conditional-expectation monotonicity + linearity.
  have hmono := condExp_mono (m := MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
    hLHS_int hRHS_int hbound'
  have hadd := condExp_add hI2A hI2B (MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
  have hsA := condExp_smul (μ := γ.dominating) (2 : ℝ) A
    (MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
  have hsB := condExp_smul (μ := γ.dominating) (t ^ 2 / 2 : ℝ) B
    (MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
  filter_upwards [hmono, hadd, hsA, hsB] with ω hmono hadd hsA hsB
  rw [hadd] at hmono
  simp only [Pi.add_apply, hsA, hsB, Pi.smul_apply, smul_eq_mul] at hmono
  linarith

/-- The normalized second bracket satisfies
`(√q̃t − A t)²/t² ≤ (1/2)·Cdom·ρt + 2·μ[rt² | comap M]/t²` almost everywhere. -/
theorem sq_over_t_le (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    (fun ω => (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2)
      ≤ᵐ[γ.dominating]
        fun ω => 1 / 2 * Cdom hM γ ω * rho hM γ t ω
          + 2 * (γ.dominating[(fun ω' =>
              qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
              | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω / t ^ 2 := by
  have hCdom_nn : 0 ≤ᵐ[γ.dominating] Cdom hM γ := by
    rw [Cdom_apply hM]
    exact condExp_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
  have hrem_nn : 0 ≤ᵐ[γ.dominating]
      γ.dominating[(fun ω' => qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
        | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›] :=
    condExp_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
  have hρ_nn : 0 ≤ᵐ[γ.dominating] rho hM γ t := by
    filter_upwards [A_sq_le hM γ t, A_nonneg hM γ t, qtilde_nonneg hM γ t]
      with ω hP1a hP1c _hqt
    have hAle : Acoef hM γ t ω ≤ Real.sqrt (qtilde hM γ t ω) := by
      rw [← Real.sqrt_sq hP1c]; exact Real.sqrt_le_sqrt hP1a
    by_cases hsum : 0 < Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω
    · rw [rho_of_pos hM γ t ω hsum]
      exact div_nonneg (by linarith) (by linarith)
    · simp [rho_of_zero hM γ t ω hsum]
  have hρ_le1 : rho hM γ t ≤ᵐ[γ.dominating] fun _ => (1 : ℝ) := by
    filter_upwards [A_nonneg hM γ t] with ω hP1c
    have hP1c : (0 : ℝ) ≤ Acoef hM γ t ω := hP1c
    by_cases hsum : 0 < Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω
    · rw [rho_of_pos hM γ t ω hsum, div_le_one hsum]; linarith
    · rw [rho_of_zero hM γ t ω hsum]; norm_num
  by_cases ht : t = 0
  · subst ht
    filter_upwards [hCdom_nn, hρ_nn] with ω hcd hρ
    have hpos : (0 : ℝ) ≤ 1 / 2 * Cdom hM γ ω * rho hM γ 0 ω :=
      mul_nonneg (mul_nonneg (by norm_num) hcd) hρ
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, add_zero]
    exact hpos
  · have ht2 : (0 : ℝ) < t ^ 2 := by positivity
    filter_upwards [A_sq_le hM γ t, A_nonneg hM γ t, qtilde_nonneg hM γ t,
      qtil_diff_le hM γ t, condExp_sq_diff_le hM γ t, hCdom_nn, hrem_nn, hρ_nn, hρ_le1]
      with ω _hP1a hP1c hqt hP2 hP3 _hcd hrem hρnn hρle1
    have hP1c : (0 : ℝ) ≤ Acoef hM γ t ω := hP1c
    have hq : Real.sqrt (qtilde hM γ t ω) ^ 2 = qtilde hM γ t ω := Real.sq_sqrt hqt
    have hsnn : (0 : ℝ) ≤ Real.sqrt (qtilde hM γ t ω) := Real.sqrt_nonneg _
    have hfac : qtilde hM γ t ω - Acoef hM γ t ω ^ 2
        = (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω)
          * (Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω) := by
      linear_combination -hq
    have hρid : (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2
        = (qtilde hM γ t ω - Acoef hM γ t ω ^ 2) * rho hM γ t ω := by
      by_cases hsum : 0 < Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω
      · rw [rho_of_pos hM γ t ω hsum, hfac]
        have hne : Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω ≠ 0 := ne_of_gt hsum
        field_simp
      · rw [rho_of_zero hM γ t ω hsum, mul_zero]
        have hslt : Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω ≤ 0 := not_lt.mp hsum
        have hs0 : Real.sqrt (qtilde hM γ t ω) = 0 := le_antisymm (by linarith) hsnn
        have ha0 : Acoef hM γ t ω = 0 := le_antisymm (by linarith) hP1c
        rw [hs0, ha0]; ring
    have hchain : qtilde hM γ t ω - Acoef hM γ t ω ^ 2
        ≤ t ^ 2 / 2 * Cdom hM γ ω
          + 2 * (γ.dominating[(fun ω' =>
              qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
              | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω := le_trans hP2 hP3
    have hnum : (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2
        ≤ t ^ 2 / 2 * Cdom hM γ ω * rho hM γ t ω
          + 2 * (γ.dominating[(fun ω' =>
              qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
              | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω := by
      rw [hρid]
      have h1 := mul_le_mul_of_nonneg_right hchain hρnn
      have h2 : 0 ≤ (γ.dominating[(fun ω' =>
          qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
          | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω * (1 - rho hM γ t ω) :=
        mul_nonneg hrem (by linarith)
      nlinarith [h1, h2]
    have hfinal : (t ^ 2 / 2 * Cdom hM γ ω * rho hM γ t ω
          + 2 * (γ.dominating[(fun ω' =>
              qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
              | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω) / t ^ 2
        = 1 / 2 * Cdom hM γ ω * rho hM γ t ω
          + 2 * (γ.dominating[(fun ω' =>
              qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
              | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω / t ^ 2 := by
      field_simp
    calc (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2
        ≤ (t ^ 2 / 2 * Cdom hM γ ω * rho hM γ t ω
            + 2 * (γ.dominating[(fun ω' =>
                qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
                | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω) / t ^ 2 :=
          (div_le_div_iff_of_pos_right ht2).mpr hnum
      _ = _ := hfinal

set_option maxHeartbeats 1000000 in
-- Single heavy declaration: many condExp-def-unfolding unifications plus integral rewrites.
/-- Integral form of the second-bracket bound. -/
theorem integral_second_bracket_bound (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) (ht : t ≠ 0) :
    ∫ ω, (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2 ∂γ.dominating
      ≤ 1 / 2 * ∫ ω, Cdom hM γ ω * rho hM γ t ω ∂γ.dominating
        + 2 * (eLpNorm (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t)
            2 γ.dominating).toReal ^ 2 / t ^ 2 := by
  -- Apply the pointwise second-bracket bound; the required measurability and
  -- integrability facts are established inline below.
  have hP4 := sq_over_t_le hM γ t
  have hm : MeasurableSpace.comap M ‹MeasurableSpace Ω_obs› ≤ ‹MeasurableSpace Ω_full› :=
    hM.comap_le
  haveI hσμ : SigmaFinite (γ.dominating.trim hm) :=
    AsymptoticStatistics.ForMathlib.SigmaFiniteTrimComap.sigmaFinite_trim_comap_of_sigmaFinite_map
      γ.dominating hM
  -- `Cdom ≥ 0`, integrable.
  have hCd_nn : 0 ≤ᵐ[γ.dominating] Cdom hM γ := by
    rw [Cdom_apply hM]
    exact condExp_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
  have hCd_int : Integrable (Cdom hM γ) γ.dominating := by
    rw [Cdom_apply hM]; exact integrable_condExp
  -- `0 ≤ ρ ≤ 1` a.e.
  have hrho_nn : 0 ≤ᵐ[γ.dominating] rho hM γ t := by
    filter_upwards [A_sq_le hM γ t, A_nonneg hM γ t, qtilde_nonneg hM γ t]
      with ω hP1a hP1c _hqt
    have hAle : Acoef hM γ t ω ≤ Real.sqrt (qtilde hM γ t ω) := by
      rw [← Real.sqrt_sq hP1c]; exact Real.sqrt_le_sqrt hP1a
    by_cases hsum : 0 < Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω
    · rw [rho_of_pos hM γ t ω hsum]
      exact div_nonneg (by linarith) (by linarith)
    · simp [rho_of_zero hM γ t ω hsum]
  have hrho_le1 : rho hM γ t ≤ᵐ[γ.dominating] fun _ => (1 : ℝ) := by
    filter_upwards [A_nonneg hM γ t] with ω hP1c
    have hP1c : (0 : ℝ) ≤ Acoef hM γ t ω := hP1c
    by_cases hsum : 0 < Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω
    · rw [rho_of_pos hM γ t ω hsum, div_le_one hsum]; linarith
    · rw [rho_of_zero hM γ t ω hsum]; norm_num
  -- `ρ` a.e.-strongly-measurable.
  have hrho_aesm : AEStronglyMeasurable (rho hM γ t) γ.dominating := by
    have hqtA : AEMeasurable (qtilde hM γ t) γ.dominating :=
      integrable_condExp.aestronglyMeasurable.aemeasurable
    have hq0A : AEMeasurable (qtilde hM γ 0) γ.dominating :=
      integrable_condExp.aestronglyMeasurable.aemeasurable
    have hcrA : AEMeasurable (cross hM γ t) γ.dominating :=
      integrable_condExp.aestronglyMeasurable.aemeasurable
    have hsqt : AEMeasurable (fun ω => Real.sqrt (qtilde hM γ t ω)) γ.dominating :=
      Real.continuous_sqrt.measurable.comp_aemeasurable hqtA
    have hsq0 : AEMeasurable (fun ω => Real.sqrt (qtilde hM γ 0 ω)) γ.dominating :=
      Real.continuous_sqrt.measurable.comp_aemeasurable hq0A
    have hquot : AEMeasurable
        (fun ω => cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω)) γ.dominating := hcrA.div hsq0
    have hform : rho hM γ t =ᵐ[γ.dominating]
        fun ω => (Real.sqrt (qtilde hM γ t ω) - cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω))
          / (Real.sqrt (qtilde hM γ t ω) + cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω)) := by
      filter_upwards [A_nonneg hM γ t, qtilde_nonneg hM γ 0] with ω hA hq0nn
      have hA' : (0 : ℝ) ≤ Acoef hM γ t ω := hA
      have hAeq : Acoef hM γ t ω = cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω) := by
        by_cases hpos : 0 < qtilde hM γ 0 ω
        · rw [Acoef_of_pos hM γ t ω hpos]
        · have hz : qtilde hM γ 0 ω = 0 := le_antisymm (not_lt.mp hpos) hq0nn
          rw [Acoef_of_zero hM γ t ω hpos, hz, Real.sqrt_zero, div_zero]
      have hsnn : (0 : ℝ) ≤ Real.sqrt (qtilde hM γ t ω) := Real.sqrt_nonneg _
      by_cases hsum : 0 < Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω
      · rw [rho_of_pos hM γ t ω hsum, hAeq]
      · rw [rho_of_zero hM γ t ω hsum]
        have hsle : Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω ≤ 0 := not_lt.mp hsum
        have hs0 : Real.sqrt (qtilde hM γ t ω) = 0 := le_antisymm (by linarith) hsnn
        have ha0 : Acoef hM γ t ω = 0 := le_antisymm (by linarith) hA'
        rw [← hAeq, hs0, ha0]; simp
    exact ((hsqt.sub hquot).div (hsqt.add hquot)).aestronglyMeasurable.congr hform.symm
  -- `Cdom·ρ` integrable (dominated by `Cdom`).
  have hg_aesm : AEStronglyMeasurable (fun ω => Cdom hM γ ω * rho hM γ t ω) γ.dominating :=
    integrable_condExp.aestronglyMeasurable.mul hrho_aesm
  have hg_bound : ∀ᵐ ω ∂γ.dominating, ‖Cdom hM γ ω * rho hM γ t ω‖ ≤ Cdom hM γ ω := by
    filter_upwards [hCd_nn, hrho_nn, hrho_le1] with ω hcd hrn hrl
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcd, abs_of_nonneg hrn]
    calc Cdom hM γ ω * rho hM γ t ω ≤ Cdom hM γ ω * 1 := mul_le_mul_of_nonneg_left hrl hcd
      _ = Cdom hM γ ω := mul_one _
  have hg_int : Integrable (fun ω => Cdom hM γ ω * rho hM γ t ω) γ.dominating :=
    hCd_int.mono' hg_aesm hg_bound
  -- `r_t ∈ L²(μ)`.
  have hrt_mem : MemLp (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t) 2 γ.dominating := by
    haveI hpt : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
    haveI hp0 : IsProbabilityMeasure (γ.curve 0) := γ.curve_isProbability 0
    have hscore_meas : Measurable (γ.score : Ω_full → ℝ) :=
      (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P_full)).measurable
    have hξt : MemLp (xi γ t) 2 γ.dominating :=
      AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous t)
    have hξ0 : MemLp (xi γ 0) 2 γ.dominating :=
      AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous 0)
    have hξdiff : MemLp (fun ω => xi γ t ω - xi γ 0 ω) 2 γ.dominating := hξt.sub hξ0
    have hsξ0 : MemLp (fun ω => (γ.score : Ω_full → ℝ) ω * xi γ 0 ω) 2 γ.dominating :=
      memLp_two_score_mul_sqrt_of_qmd (g := (γ.score : Ω_full → ℝ))
        γ.curve_isProbability γ.curve_absContinuous hscore_meas γ.qmd_limit
    have heq : qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t
        = fun ω => (xi γ t ω - xi γ 0 ω) - (t / 2) * ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω) := by
      funext ω; simp only [qmdRem, xi_apply, pbar_apply]; ring
    rw [heq]
    exact hξdiff.sub (hsξ0.const_mul (t / 2))
  -- `∫ r_t² = ‖r_t‖²`.
  have hsq : ∫ ω, qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω ^ 2 ∂γ.dominating
      = (eLpNorm (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t) 2 γ.dominating).toReal
          ^ 2 := by
    rw [← sqrt_integral_sq_eq_eLpNorm_toReal hrt_mem,
        Real.sq_sqrt (integral_nonneg (fun ω => sq_nonneg _))]
  -- `∫ μ[r_t²|𝒢] = ‖r_t‖²`.
  have hCE : (∫ ω, (γ.dominating[(fun ω' =>
        qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
        | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω ∂γ.dominating)
      = (eLpNorm (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t) 2
          γ.dominating).toReal ^ 2 := by
    rw [integral_condExp hm]; exact hsq
  -- The two RHS summands are integrable.
  have hf1_int : Integrable (fun ω => 1 / 2 * Cdom hM γ ω * rho hM γ t ω) γ.dominating :=
    (hg_int.const_mul (1 / 2)).congr (Filter.Eventually.of_forall (fun ω => by ring))
  have hf2_int : Integrable (fun ω => 2 * (γ.dominating[(fun ω' =>
        qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
        | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω / t ^ 2) γ.dominating :=
    (integrable_condExp.const_mul 2).div_const (t ^ 2)
  have hRHS_int : Integrable (fun ω => 1 / 2 * Cdom hM γ ω * rho hM γ t ω
      + 2 * (γ.dominating[(fun ω' => qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
          | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω / t ^ 2) γ.dominating := by
    exact hf1_int.add hf2_int
  -- The left-hand side is integrable by domination by the right-hand side.
  have hLHS_aesm : AEStronglyMeasurable
      (fun ω => (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2) γ.dominating := by
    have hqtA : AEMeasurable (qtilde hM γ t) γ.dominating :=
      integrable_condExp.aestronglyMeasurable.aemeasurable
    have hq0A : AEMeasurable (qtilde hM γ 0) γ.dominating :=
      integrable_condExp.aestronglyMeasurable.aemeasurable
    have hcrA : AEMeasurable (cross hM γ t) γ.dominating :=
      integrable_condExp.aestronglyMeasurable.aemeasurable
    have hsqt : AEMeasurable (fun ω => Real.sqrt (qtilde hM γ t ω)) γ.dominating :=
      Real.continuous_sqrt.measurable.comp_aemeasurable hqtA
    have hsq0 : AEMeasurable (fun ω => Real.sqrt (qtilde hM γ 0 ω)) γ.dominating :=
      Real.continuous_sqrt.measurable.comp_aemeasurable hq0A
    have hAae : Acoef hM γ t =ᵐ[γ.dominating]
        fun ω => cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω) := by
      filter_upwards [qtilde_nonneg hM γ 0] with ω hq0nn
      by_cases hpos : 0 < qtilde hM γ 0 ω
      · rw [Acoef_of_pos hM γ t ω hpos]
      · have hz : qtilde hM γ 0 ω = 0 := le_antisymm (not_lt.mp hpos) hq0nn
        rw [Acoef_of_zero hM γ t ω hpos, hz, Real.sqrt_zero, div_zero]
    have hAA : AEMeasurable (Acoef hM γ t) γ.dominating := (hcrA.div hsq0).congr hAae.symm
    exact (((hsqt.sub hAA).pow_const 2).div_const (t ^ 2)).aestronglyMeasurable
  have hLHS_int : Integrable
      (fun ω => (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2) γ.dominating := by
    refine hRHS_int.mono' hLHS_aesm ?_
    filter_upwards [hP4] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hω
  -- Integral algebra on the RHS.
  have hI1 : ∫ ω, 1 / 2 * Cdom hM γ ω * rho hM γ t ω ∂γ.dominating
      = 1 / 2 * ∫ ω, Cdom hM γ ω * rho hM γ t ω ∂γ.dominating := by
    simp_rw [mul_assoc]
    exact integral_const_mul (1 / 2 : ℝ) _
  have hI2 : ∫ ω, 2 * (γ.dominating[(fun ω' =>
        qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
        | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω / t ^ 2 ∂γ.dominating
      = 2 * (∫ ω, (γ.dominating[(fun ω' =>
          qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
          | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω ∂γ.dominating) / t ^ 2 := by
    simp_rw [mul_div_assoc]
    rw [integral_const_mul, integral_div]
  have hRHS_eq : (∫ ω, (1 / 2 * Cdom hM γ ω * rho hM γ t ω
        + 2 * (γ.dominating[(fun ω' => qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
            | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω / t ^ 2) ∂γ.dominating)
      = 1 / 2 * ∫ ω, Cdom hM γ ω * rho hM γ t ω ∂γ.dominating
        + 2 * (eLpNorm (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t) 2
            γ.dominating).toReal ^ 2 / t ^ 2 := by
    rw [integral_add hf1_int hf2_int, hI1, hI2, hCE]
  calc ∫ ω, (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2 ∂γ.dominating
      ≤ ∫ ω, (1 / 2 * Cdom hM γ ω * rho hM γ t ω
          + 2 * (γ.dominating[(fun ω' =>
                qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω' ^ 2)
              | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω / t ^ 2) ∂γ.dominating :=
        integral_mono_ae hLHS_int hRHS_int hP4
    _ = 1 / 2 * ∫ ω, Cdom hM γ ω * rho hM γ t ω ∂γ.dominating
        + 2 * (eLpNorm (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t) 2
            γ.dominating).toReal ^ 2 / t ^ 2 := hRHS_eq

/-- The second term `2·‖rt‖²/t²` tends to zero by
`γ.qmd_limit_toReal_sq`. -/
theorem second_term_tendsto (γ : QMDPath P_full) :
    Tendsto (fun t => 2 * (eLpNorm
        (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t) 2 γ.dominating).toReal ^ 2
        / t ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  have h := (γ.qmd_limit_toReal_sq).const_mul (2 : ℝ)
  simp only [mul_zero] at h
  simp only [mul_div_assoc]
  exact h

/-! ### Dominated-convergence lemmas -/

/-- The QMD remainder `r_t` is in `L²(μ)` for every `t` (all `t`, not just
eventually). -/
private lemma memLp_qmdRem (γ : QMDPath P_full) (t : ℝ) :
    MemLp (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t) 2 γ.dominating := by
  haveI hpt : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  haveI hp0 : IsProbabilityMeasure (γ.curve 0) := γ.curve_isProbability 0
  have hscore_meas : Measurable (γ.score : Ω_full → ℝ) :=
    (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P_full)).measurable
  have hξt : MemLp (xi γ t) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous t)
  have hξ0 : MemLp (xi γ 0) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous 0)
  have hξdiff : MemLp (fun ω => xi γ t ω - xi γ 0 ω) 2 γ.dominating := hξt.sub hξ0
  have hsξ0 : MemLp (fun ω => (γ.score : Ω_full → ℝ) ω * xi γ 0 ω) 2 γ.dominating :=
    memLp_two_score_mul_sqrt_of_qmd (g := (γ.score : Ω_full → ℝ))
      γ.curve_isProbability γ.curve_absContinuous hscore_meas γ.qmd_limit
  have heq : qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t
      = fun ω => (xi γ t ω - xi γ 0 ω) - (t / 2) * ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω) := by
    funext ω; simp only [qmdRem, xi_apply, pbar_apply]; ring
  rw [heq]
  exact hξdiff.sub (hsξ0.const_mul (t / 2))

/-- The unit `L²(μ)`-norm of the square-root density: `‖ξ_t‖_{L²(μ)} = 1`. -/
private lemma eLpNorm_xi_eq_one (γ : QMDPath P_full) (t : ℝ) :
    eLpNorm (xi γ t) 2 γ.dominating = 1 := by
  haveI hpt : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  have hmem : MemLp (xi γ t) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous t)
  have hint : ∫ ω, xi γ t ω ^ 2 ∂γ.dominating = 1 := by
    have h := AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_sqrt_rnDeriv_sq
      (ν := γ.curve t) (μ := γ.dominating) (γ.curve_absContinuous t)
    rw [measure_univ, ENNReal.toReal_one] at h
    exact h
  have htoReal : (eLpNorm (xi γ t) 2 γ.dominating).toReal = 1 := by
    rw [← sqrt_integral_sq_eq_eLpNorm_toReal hmem, hint, Real.sqrt_one]
  have hne : eLpNorm (xi γ t) 2 γ.dominating ≠ ⊤ := hmem.eLpNorm_lt_top.ne
  calc eLpNorm (xi γ t) 2 γ.dominating
      = ENNReal.ofReal (eLpNorm (xi γ t) 2 γ.dominating).toReal :=
        (ENNReal.ofReal_toReal hne).symm
    _ = ENNReal.ofReal 1 := by rw [htoReal]
    _ = 1 := by simp

/-- `‖r_t‖_{L²(μ)} → 0` along `𝓝[≠] 0` (from the `ℝ≥0∞`-form QMD limit). -/
private lemma eLpNorm_qmdRem_tendsto (γ : QMDPath P_full) :
    Tendsto (fun t => eLpNorm (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t)
        2 γ.dominating) (𝓝[≠] 0) (𝓝 0) := by
  have hq : AsymptoticStatistics.ForMathlib.QMDAnalytic.IsQMDLimit γ.curve γ.dominating
      (γ.score : Ω_full → ℝ) := γ.qmd_limit
  have hofr : Tendsto (fun t : ℝ => ENNReal.ofReal |t|) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => |t|) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
      have hc : Tendsto (fun t : ℝ => |t|) (𝓝 (0:ℝ)) (𝓝 |(0:ℝ)|) := continuous_abs.tendsto (0:ℝ)
      simp only [abs_zero] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    have := (ENNReal.continuous_ofReal.tendsto (0:ℝ)).comp h1
    simpa using! this
  have hprod := ENNReal.Tendsto.mul hq (Or.inr (by simp : (0:ℝ≥0∞) ≠ ⊤)) hofr
    (Or.inr (by simp : (0:ℝ≥0∞) ≠ ⊤))
  rw [mul_zero] at hprod
  refine Tendsto.congr' ?_ hprod
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : ENNReal.ofReal |t| ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact abs_pos.mpr ht
  rw [ENNReal.div_mul_cancel hne ENNReal.ofReal_ne_top]

/-- `‖ξ_t − ξ_0‖_{L²(μ)} → 0` along `𝓝[≠] 0` (triangle inequality:
`ξ_t − ξ_0 = r_t + (t/2)·s·ξ_0`). -/
private lemma xi_diff_L2_tendsto (γ : QMDPath P_full) :
    Tendsto (fun t => eLpNorm (fun ω => xi γ t ω - xi γ 0 ω) 2 γ.dominating)
      (𝓝[≠] 0) (𝓝 0) := by
  haveI hp0 : IsProbabilityMeasure (γ.curve 0) := γ.curve_isProbability 0
  have hscore_meas : Measurable (γ.score : Ω_full → ℝ) :=
    (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P_full)).measurable
  have hsξ0 : MemLp (fun ω => (γ.score : Ω_full → ℝ) ω * xi γ 0 ω) 2 γ.dominating :=
    memLp_two_score_mul_sqrt_of_qmd (g := (γ.score : Ω_full → ℝ))
      γ.curve_isProbability γ.curve_absContinuous hscore_meas γ.qmd_limit
  set C₀ : ℝ≥0∞ := eLpNorm (fun ω => (γ.score : Ω_full → ℝ) ω * xi γ 0 ω) 2 γ.dominating with hC₀
  have hC₀_ne : C₀ ≠ ⊤ := hsξ0.eLpNorm_lt_top.ne
  have hterm2 : Tendsto (fun t : ℝ => ‖(t / 2 : ℝ)‖ₑ * C₀) (𝓝[≠] 0) (𝓝 0) := by
    have henorm : Tendsto (fun t : ℝ => ‖(t / 2 : ℝ)‖ₑ) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
      have hc : Tendsto (fun t : ℝ => ‖(t / 2 : ℝ)‖ₑ) (𝓝 (0:ℝ)) (𝓝 ‖((0:ℝ) / 2 : ℝ)‖ₑ) :=
        (continuous_enorm.comp (continuous_id.div_const 2)).tendsto (0:ℝ)
      simp only [zero_div, enorm_zero] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    have := ENNReal.Tendsto.mul_const henorm (Or.inr hC₀_ne)
    simpa using this
  have hupperlim : Tendsto (fun t => eLpNorm (qmdRem γ.curve γ.dominating
        (γ.score : Ω_full → ℝ) t) 2 γ.dominating + ‖(t / 2 : ℝ)‖ₑ * C₀)
      (𝓝[≠] 0) (𝓝 0) := by
    have := (eLpNorm_qmdRem_tendsto γ).add hterm2
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupperlim
    (Eventually.of_forall (fun t => zero_le)) ?_
  filter_upwards with t
  have hAESMr := (memLp_qmdRem γ t).aestronglyMeasurable
  have hAESMg : AEStronglyMeasurable
      ((t / 2) • fun ω => (γ.score : Ω_full → ℝ) ω * xi γ 0 ω) γ.dominating :=
    hsξ0.aestronglyMeasurable.const_smul (t / 2)
  have hfun : (fun ω => xi γ t ω - xi γ 0 ω)
      = qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t
        + (t / 2) • fun ω => (γ.score : Ω_full → ℝ) ω * xi γ 0 ω := by
    funext ω
    simp only [qmdRem, xi_apply, pbar_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  calc eLpNorm (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t
          + (t / 2) • fun ω => (γ.score : Ω_full → ℝ) ω * xi γ 0 ω) 2 γ.dominating
      ≤ eLpNorm (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t) 2 γ.dominating
        + eLpNorm ((t / 2) • fun ω => (γ.score : Ω_full → ℝ) ω * xi γ 0 ω) 2 γ.dominating :=
        eLpNorm_add_le hAESMr hAESMg one_le_two
    _ = eLpNorm (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t) 2 γ.dominating
        + ‖(t / 2 : ℝ)‖ₑ * C₀ := by rw [eLpNorm_const_smul]

/-- `‖q̃_t − q̃_0‖_{L¹(μ)} → 0` (condExp contraction + Hölder + `‖ξ‖₂ = 1`). -/
private lemma qtilde_L1_tendsto (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] :
    Tendsto (fun t => eLpNorm (fun ω => qtilde hM γ t ω - qtilde hM γ 0 ω) 1 γ.dominating)
      (𝓝[≠] 0) (𝓝 0) := by
  have hupperlim : Tendsto
      (fun t => 2 * eLpNorm (fun ω => xi γ t ω - xi γ 0 ω) 2 γ.dominating)
      (𝓝[≠] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (xi_diff_L2_tendsto γ) (Or.inr (by simp : (2:ℝ≥0∞) ≠ ⊤))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupperlim
    (Eventually.of_forall (fun t => zero_le)) ?_
  filter_upwards with t
  haveI hpt : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  haveI hp0 : IsProbabilityMeasure (γ.curve 0) := γ.curve_isProbability 0
  have hξt : MemLp (xi γ t) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous t)
  have hξ0 : MemLp (xi γ 0) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous 0)
  have hξt2_int : Integrable (fun ω => xi γ t ω ^ 2) γ.dominating := hξt.integrable_sq
  have hξ02_int : Integrable (fun ω => xi γ 0 ω ^ 2) γ.dominating := hξ0.integrable_sq
  have hae : (fun ω => qtilde hM γ t ω - qtilde hM γ 0 ω)
      =ᵐ[γ.dominating]
      γ.dominating[((fun ω => xi γ t ω ^ 2) - fun ω => xi γ 0 ω ^ 2)
        | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›] := by
    have hsub := condExp_sub hξt2_int hξ02_int (MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
    filter_upwards [hsub] with ω hω
    rw [hω, Pi.sub_apply, congrFun (condExp_xi_sq_eq_qtilde hM γ t) ω,
      congrFun (condExp_xi_sq_eq_qtilde hM γ 0) ω]
  rw [eLpNorm_congr_ae hae]
  have hb2 : eLpNorm (fun ω => xi γ t ω + xi γ 0 ω) 2 γ.dominating ≤ 2 := by
    refine le_trans (eLpNorm_add_le hξt.aestronglyMeasurable hξ0.aestronglyMeasurable one_le_two) ?_
    rw [eLpNorm_xi_eq_one, eLpNorm_xi_eq_one]; norm_num
  have hDG : ((fun ω => xi γ t ω ^ 2) - fun ω => xi γ 0 ω ^ 2)
      = (fun ω => xi γ t ω - xi γ 0 ω) • fun ω => xi γ t ω + xi γ 0 ω := by
    funext ω
    change xi γ t ω ^ 2 - xi γ 0 ω ^ 2 = (xi γ t ω - xi γ 0 ω) * (xi γ t ω + xi γ 0 ω)
    ring
  refine le_trans (eLpNorm_one_condExp_le_eLpNorm _) ?_
  rw [hDG]
  refine le_trans (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2)
    (hξt.add hξ0).aestronglyMeasurable (hξt.sub hξ0).aestronglyMeasurable) ?_
  exact le_of_le_of_eq (mul_le_mul_right hb2 _) (mul_comm _ _)

/-- `‖cross_t − q̃_0‖_{L¹(μ)} → 0` (condExp contraction + Hölder + `‖ξ₀‖₂ = 1`). -/
private lemma cross_L1_tendsto (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] :
    Tendsto (fun t => eLpNorm (fun ω => cross hM γ t ω - qtilde hM γ 0 ω) 1 γ.dominating)
      (𝓝[≠] 0) (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (xi_diff_L2_tendsto γ)
    (Eventually.of_forall (fun t => zero_le)) ?_
  filter_upwards with t
  haveI hpt : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  haveI hp0 : IsProbabilityMeasure (γ.curve 0) := γ.curve_isProbability 0
  have hξt : MemLp (xi γ t) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous t)
  have hξ0 : MemLp (xi γ 0) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous 0)
  have hcross_int : Integrable (fun ω => xi γ t ω * xi γ 0 ω) γ.dominating := hξt.integrable_mul hξ0
  have hξ02_int : Integrable (fun ω => xi γ 0 ω ^ 2) γ.dominating := hξ0.integrable_sq
  have hae : (fun ω => cross hM γ t ω - qtilde hM γ 0 ω)
      =ᵐ[γ.dominating]
      γ.dominating[((fun ω => xi γ t ω * xi γ 0 ω) - fun ω => xi γ 0 ω ^ 2)
        | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›] := by
    have hsub := condExp_sub hcross_int hξ02_int (MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
    filter_upwards [hsub] with ω hω
    rw [hω, Pi.sub_apply, ← cross_apply hM γ t, congrFun (condExp_xi_sq_eq_qtilde hM γ 0) ω]
  rw [eLpNorm_congr_ae hae]
  have hDG : ((fun ω => xi γ t ω * xi γ 0 ω) - fun ω => xi γ 0 ω ^ 2)
      = (fun ω => xi γ t ω - xi γ 0 ω) • xi γ 0 := by
    funext ω
    change xi γ t ω * xi γ 0 ω - xi γ 0 ω ^ 2 = (xi γ t ω - xi γ 0 ω) * xi γ 0 ω
    ring
  refine le_trans (eLpNorm_one_condExp_le_eLpNorm _) ?_
  rw [hDG]
  refine le_trans (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2)
    hξ0.aestronglyMeasurable (hξt.sub hξ0).aestronglyMeasurable) ?_
  rw [eLpNorm_xi_eq_one, mul_one]

/-- `0 ≤ ρ_t` a.e. (from `A_sq_le` + `A_nonneg`). -/
private lemma rho_nonneg (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    0 ≤ᵐ[γ.dominating] rho hM γ t := by
  filter_upwards [A_sq_le hM γ t, A_nonneg hM γ t, qtilde_nonneg hM γ t]
    with ω hP1a hP1c _hqt
  have hAle : Acoef hM γ t ω ≤ Real.sqrt (qtilde hM γ t ω) := by
    rw [← Real.sqrt_sq hP1c]; exact Real.sqrt_le_sqrt hP1a
  by_cases hsum : 0 < Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω
  · rw [rho_of_pos hM γ t ω hsum]
    exact div_nonneg (by linarith) (by linarith)
  · simp [rho_of_zero hM γ t ω hsum]

/-- `ρ_t ≤ 1` a.e. (from `A_nonneg`). -/
private lemma rho_le_one (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    rho hM γ t ≤ᵐ[γ.dominating] fun _ => (1 : ℝ) := by
  filter_upwards [A_nonneg hM γ t] with ω hP1c
  have hP1c : (0 : ℝ) ≤ Acoef hM γ t ω := hP1c
  by_cases hsum : 0 < Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω
  · rw [rho_of_pos hM γ t ω hsum, div_le_one hsum]; linarith
  · rw [rho_of_zero hM γ t ω hsum]; norm_num

/-- `ρ_t` is a.e.-strongly-measurable (an a.e. ratio of condExp-based terms). -/
private lemma aestronglyMeasurable_rho (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    AEStronglyMeasurable (rho hM γ t) γ.dominating := by
  have hqt : AEStronglyMeasurable (qtilde hM γ t) γ.dominating :=
    integrable_condExp.aestronglyMeasurable
  have hq0 : AEStronglyMeasurable (qtilde hM γ 0) γ.dominating :=
    integrable_condExp.aestronglyMeasurable
  have hcr : AEStronglyMeasurable (cross hM γ t) γ.dominating :=
    integrable_condExp.aestronglyMeasurable
  have hform : rho hM γ t =ᵐ[γ.dominating]
      fun ω => (Real.sqrt (qtilde hM γ t ω) - cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω))
        / (Real.sqrt (qtilde hM γ t ω) + cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω)) := by
    filter_upwards [A_nonneg hM γ t, qtilde_nonneg hM γ 0] with ω hA hq0nn
    have hA' : (0 : ℝ) ≤ Acoef hM γ t ω := hA
    have hAeq : Acoef hM γ t ω = cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω) := by
      by_cases hpos : 0 < qtilde hM γ 0 ω
      · rw [Acoef_of_pos hM γ t ω hpos]
      · have hz : qtilde hM γ 0 ω = 0 := le_antisymm (not_lt.mp hpos) hq0nn
        rw [Acoef_of_zero hM γ t ω hpos, hz, Real.sqrt_zero, div_zero]
    have hsnn : (0 : ℝ) ≤ Real.sqrt (qtilde hM γ t ω) := Real.sqrt_nonneg _
    by_cases hsum : 0 < Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω
    · rw [rho_of_pos hM γ t ω hsum, hAeq]
    · rw [rho_of_zero hM γ t ω hsum]
      have hsle : Real.sqrt (qtilde hM γ t ω) + Acoef hM γ t ω ≤ 0 := not_lt.mp hsum
      have hs0 : Real.sqrt (qtilde hM γ t ω) = 0 := le_antisymm (by linarith) hsnn
      have ha0 : Acoef hM γ t ω = 0 := le_antisymm (by linarith) hA'
      rw [← hAeq, hs0, ha0]; simp
  refine AEStronglyMeasurable.congr ?_ hform.symm
  have hqtA : AEMeasurable (qtilde hM γ t) γ.dominating := hqt.aemeasurable
  have hq0A : AEMeasurable (qtilde hM γ 0) γ.dominating := hq0.aemeasurable
  have hcrA : AEMeasurable (cross hM γ t) γ.dominating := hcr.aemeasurable
  have hsqt : AEMeasurable (fun ω => Real.sqrt (qtilde hM γ t ω)) γ.dominating :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hqtA
  have hsq0 : AEMeasurable (fun ω => Real.sqrt (qtilde hM γ 0 ω)) γ.dominating :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hq0A
  have hquot : AEMeasurable
      (fun ω => cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω)) γ.dominating := hcrA.div hsq0
  exact ((hsqt.sub hquot).div (hsqt.add hquot)).aestronglyMeasurable

/-- `Cdom = 0` a.e. on `{q̃_0 = 0}`: conditional support implies `ξ₀ = 0` there
⟹ `(s·ξ₀)² = 0` ⟹ its condExp vanishes on the `𝒢`-set). -/
private lemma Cdom_eq_zero_of_qtilde_zero (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] :
    ∀ᵐ ω ∂γ.dominating, qtilde hM γ 0 ω = 0 → Cdom hM γ ω = 0 := by
  classical
  have hm : MeasurableSpace.comap M ‹MeasurableSpace Ω_obs› ≤ ‹MeasurableSpace Ω_full› :=
    hM.comap_le
  haveI hσμ : SigmaFinite (γ.dominating.trim hm) :=
    AsymptoticStatistics.ForMathlib.SigmaFiniteTrimComap.sigmaFinite_trim_comap_of_sigmaFinite_map
      γ.dominating hM
  haveI hp0 : IsProbabilityMeasure (γ.curve 0) := γ.curve_isProbability 0
  have hscore_meas : Measurable (γ.score : Ω_full → ℝ) :=
    (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P_full)).measurable
  have hξ0 : MemLp (xi γ 0) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous 0)
  have hsξ0 : MemLp (fun ω => (γ.score : Ω_full → ℝ) ω * xi γ 0 ω) 2 γ.dominating :=
    memLp_two_score_mul_sqrt_of_qmd (g := (γ.score : Ω_full → ℝ))
      γ.curve_isProbability γ.curve_absContinuous hscore_meas γ.qmd_limit
  -- `G := {q̃₀ = 0}` is `𝒢`-measurable.
  have hqtSM : StronglyMeasurable[MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]
      (qtilde hM γ 0) := stronglyMeasurable_condExp
  have hG_meas : MeasurableSet[MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]
      {ω | qtilde hM γ 0 ω = 0} := hqtSM.measurableSet_eq_fun stronglyMeasurable_const
  have hG_meas0 : MeasurableSet {ω | qtilde hM γ 0 ω = 0} := hm _ hG_meas
  -- `pbar 0 = 0` almost everywhere on `G`, by conditional support.
  have hpbar0_int : Integrable (pbar γ 0) γ.dominating := Measure.integrable_toReal_rnDeriv
  have hpbar0_nn : 0 ≤ᵐ[γ.dominating] pbar γ 0 :=
    Eventually.of_forall (fun ω => pbar_nonneg γ 0 ω)
  have hcondG : ∀ᵐ ω ∂γ.dominating.restrict {ω | qtilde hM γ 0 ω = 0},
      (γ.dominating[pbar γ 0 | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω = 0 := by
    filter_upwards [ae_restrict_mem hG_meas0] with ω hω
    exact hω
  have hpbar0_zero : ∀ᵐ ω ∂γ.dominating.restrict {ω | qtilde hM γ 0 ω = 0}, pbar γ 0 ω = 0 :=
    AsymptoticStatistics.ForMathlib.CondExpCauchySchwarz.ae_eq_zero_on_of_condExp_eq_zero
      hm hpbar0_int hpbar0_nn hG_meas hcondG
  -- `(s·ξ₀)² = 0` a.e. on `G`.
  have hsq_zero : ∀ᵐ ω ∂γ.dominating.restrict {ω | qtilde hM γ 0 ω = 0},
      ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω) ^ 2 = 0 := by
    filter_upwards [hpbar0_zero] with ω hω
    have h2 : xi γ 0 ω ^ 2 = 0 := by rw [xi_sq]; exact hω
    have hxi0 : xi γ 0 ω = 0 := (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp h2
    rw [hxi0]; ring
  -- `∫_G (s·ξ₀)² = 0`, `Cdom ≥ 0`, `Cdom = μ[(s·ξ₀)²|𝒢]` ⟹ `Cdom = 0` a.e. on `G`.
  have hCd_nn : 0 ≤ᵐ[γ.dominating] Cdom hM γ := by
    rw [Cdom_apply hM]
    exact condExp_nonneg (Eventually.of_forall (fun ω => sq_nonneg _))
  have hCd_int : Integrable (Cdom hM γ) γ.dominating := by
    rw [Cdom_apply hM]; exact integrable_condExp
  have hsq_int : Integrable (fun ω => ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω) ^ 2) γ.dominating :=
    hsξ0.integrable_sq
  have hintG : ∫ ω in {ω | qtilde hM γ 0 ω = 0}, Cdom hM γ ω ∂γ.dominating = 0 := by
    rw [Cdom_apply hM, setIntegral_condExp hm hsq_int hG_meas]
    exact integral_eq_zero_of_ae hsq_zero
  have hCd_zero : ∀ᵐ ω ∂γ.dominating.restrict {ω | qtilde hM γ 0 ω = 0}, Cdom hM γ ω = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae hCd_nn) hCd_int.restrict).mp hintG
  rw [ae_restrict_iff' hG_meas0] at hCd_zero
  exact hCd_zero

/-- The first term `(1/2)∫ Cdom·ρt dμ` tends to zero by dominated convergence
along subsequences. -/
theorem first_term_tendsto (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] :
    Tendsto (fun t => 1 / 2 * ∫ ω, Cdom hM γ ω * rho hM γ t ω ∂γ.dominating)
      (𝓝[≠] 0) (𝓝 0) := by
  have hCd_nn : 0 ≤ᵐ[γ.dominating] Cdom hM γ := by
    rw [Cdom_apply hM]
    exact condExp_nonneg (Eventually.of_forall (fun ω => sq_nonneg _))
  have hCd_int : Integrable (Cdom hM γ) γ.dominating := by
    rw [Cdom_apply hM]; exact integrable_condExp
  have hCd_zero := Cdom_eq_zero_of_qtilde_zero hM γ
  -- Core: `∫ Cdom·ρt dμ → 0` via the subsequence principle.
  have hmain : Tendsto (fun t => ∫ ω, Cdom hM γ ω * rho hM γ t ω ∂γ.dominating)
      (𝓝[≠] 0) (𝓝 0) := by
    refine Filter.tendsto_of_subseq_tendsto ?_
    intro u hu
    -- In-measure convergences of `q̃_{uₙ}` and `cross_{uₙ}` (from L¹ convergence).
    have hq_meas : TendstoInMeasure γ.dominating (fun n => qtilde hM γ (u n)) atTop
        (qtilde hM γ 0) := by
      apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
        (fun n => integrable_condExp.aestronglyMeasurable)
        integrable_condExp.aestronglyMeasurable
      exact (qtilde_L1_tendsto hM γ).comp hu
    have hc_meas : TendstoInMeasure γ.dominating (fun n => cross hM γ (u n)) atTop
        (qtilde hM γ 0) := by
      apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
        (fun n => integrable_condExp.aestronglyMeasurable)
        integrable_condExp.aestronglyMeasurable
      exact (cross_L1_tendsto hM γ).comp hu
    -- Extract a common a.e.-convergent subsequence `ns₁ ∘ ns₂`.
    obtain ⟨ns₁, hns₁_mono, hns₁_ae⟩ := hq_meas.exists_seq_tendsto_ae
    have hc_meas' : TendstoInMeasure γ.dominating (fun i => cross hM γ (u (ns₁ i))) atTop
        (qtilde hM γ 0) := by
      intro ε hε
      exact (hc_meas ε hε).comp hns₁_mono.tendsto_atTop
    obtain ⟨ns₂, hns₂_mono, hns₂_ae⟩ := hc_meas'.exists_seq_tendsto_ae
    refine ⟨fun j => ns₁ (ns₂ j), ?_⟩
    -- Pointwise `Cdom·ρ_{u(ns₁(ns₂ j))} → 0` a.e.
    have hlim : ∀ᵐ ω ∂γ.dominating,
        Tendsto (fun j => Cdom hM γ ω * rho hM γ (u (ns₁ (ns₂ j))) ω) atTop (𝓝 0) := by
      filter_upwards [hns₁_ae, hns₂_ae, hCd_zero, qtilde_nonneg hM γ 0]
        with ω hqx hcx hCdz hq0nn
      have hqxφ : Tendsto (fun j => qtilde hM γ (u (ns₁ (ns₂ j))) ω) atTop
          (𝓝 (qtilde hM γ 0 ω)) := hqx.comp hns₂_mono.tendsto_atTop
      by_cases hpos : 0 < qtilde hM γ 0 ω
      · have hsqtq : Tendsto (fun j => Real.sqrt (qtilde hM γ (u (ns₁ (ns₂ j))) ω)) atTop
            (𝓝 (Real.sqrt (qtilde hM γ 0 ω))) :=
          (Real.continuous_sqrt.tendsto _).comp hqxφ
        have hA : Tendsto (fun j => Acoef hM γ (u (ns₁ (ns₂ j))) ω) atTop
            (𝓝 (Real.sqrt (qtilde hM γ 0 ω))) := by
          have hd := hcx.div_const (Real.sqrt (qtilde hM γ 0 ω))
          rw [Real.div_sqrt] at hd
          exact hd.congr (fun j => (Acoef_of_pos hM γ _ ω hpos).symm)
        have hnum : Tendsto (fun j => Real.sqrt (qtilde hM γ (u (ns₁ (ns₂ j))) ω)
            - Acoef hM γ (u (ns₁ (ns₂ j))) ω) atTop (𝓝 0) := by
          have := hsqtq.sub hA; simpa using this
        have hden : Tendsto (fun j => Real.sqrt (qtilde hM γ (u (ns₁ (ns₂ j))) ω)
            + Acoef hM γ (u (ns₁ (ns₂ j))) ω) atTop (𝓝 (2 * Real.sqrt (qtilde hM γ 0 ω))) := by
          have := hsqtq.add hA; rwa [← two_mul] at this
        have hden_pos : 0 < 2 * Real.sqrt (qtilde hM γ 0 ω) := by
          have : 0 < Real.sqrt (qtilde hM γ 0 ω) := Real.sqrt_pos.mpr hpos
          linarith
        have hrho : Tendsto (fun j => rho hM γ (u (ns₁ (ns₂ j))) ω) atTop (𝓝 0) := by
          have hev : ∀ᶠ j in atTop, 0 < Real.sqrt (qtilde hM γ (u (ns₁ (ns₂ j))) ω)
              + Acoef hM γ (u (ns₁ (ns₂ j))) ω := hden.eventually (eventually_gt_nhds hden_pos)
          have hratio : Tendsto (fun j =>
              (Real.sqrt (qtilde hM γ (u (ns₁ (ns₂ j))) ω) - Acoef hM γ (u (ns₁ (ns₂ j))) ω)
              / (Real.sqrt (qtilde hM γ (u (ns₁ (ns₂ j))) ω) + Acoef hM γ (u (ns₁ (ns₂ j))) ω))
              atTop (𝓝 0) := by
            have := hnum.div hden (ne_of_gt hden_pos); simpa using! this
          refine hratio.congr' ?_
          filter_upwards [hev] with j hj
          exact (rho_of_pos hM γ _ ω hj).symm
        have := hrho.const_mul (Cdom hM γ ω); simpa using this
      · have hqz : qtilde hM γ 0 ω = 0 := le_antisymm (not_lt.mp hpos) hq0nn
        have hcz : Cdom hM γ ω = 0 := hCdz hqz
        simp only [hcz, zero_mul]
        exact tendsto_const_nhds
    -- Dominated convergence: `∫ Cdom·ρ_{u(ns₁(ns₂ j))} → 0`.
    have hbound : ∀ j, ∀ᵐ ω ∂γ.dominating,
        ‖Cdom hM γ ω * rho hM γ (u (ns₁ (ns₂ j))) ω‖ ≤ Cdom hM γ ω := by
      intro j
      filter_upwards [hCd_nn, rho_nonneg hM γ (u (ns₁ (ns₂ j))),
        rho_le_one hM γ (u (ns₁ (ns₂ j)))] with ω hcd hrn hrl
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcd, abs_of_nonneg hrn]
      calc Cdom hM γ ω * rho hM γ (u (ns₁ (ns₂ j))) ω
          ≤ Cdom hM γ ω * 1 := mul_le_mul_of_nonneg_left hrl hcd
        _ = Cdom hM γ ω := mul_one _
    have hFmeas : ∀ j, AEStronglyMeasurable
        (fun ω => Cdom hM γ ω * rho hM γ (u (ns₁ (ns₂ j))) ω) γ.dominating :=
      fun j => integrable_condExp.aestronglyMeasurable.mul (aestronglyMeasurable_rho hM γ _)
    have hDCT := tendsto_integral_of_dominated_convergence (Cdom hM γ) hFmeas hCd_int hbound hlim
    simpa using hDCT
  have := hmain.const_mul (1 / 2 : ℝ)
  simpa using this

/-- **Lfirst** — first bracket `∫ (A t − √q̃0 − (t/2)(Π∘M)√q̃0)²/t² dμ → 0`. -/
theorem first_bracket_tendsto (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] :
    Tendsto (fun t => ∫ ω, (Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
        - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
            * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 / t ^ 2 ∂γ.dominating)
      (𝓝[≠] 0) (𝓝 0) := by
  haveI hσμ : SigmaFinite (γ.dominating.trim hM.comap_le) :=
    AsymptoticStatistics.ForMathlib.SigmaFiniteTrimComap.sigmaFinite_trim_comap_of_sigmaFinite_map
      γ.dominating hM
  -- Upper envelope: `‖r_t‖₂²/t² → 0` (defeq to `qmd_limit_toReal_sq`).
  have hupper : Tendsto (fun t => (eLpNorm
      (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t) 2 γ.dominating).toReal ^ 2
        / t ^ 2) (𝓝[≠] 0) (𝓝 0) := γ.qmd_limit_toReal_sq
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall (fun t =>
      integral_nonneg (fun ω => div_nonneg (sq_nonneg _) (sq_nonneg _)))) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htne : t ≠ 0 := ht
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  haveI hpt : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  haveI hp0 : IsProbabilityMeasure (γ.curve 0) := γ.curve_isProbability 0
  have hscore_meas : Measurable (γ.score : Ω_full → ℝ) :=
    (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P_full)).measurable
  have hξt : MemLp (xi γ t) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous t)
  have hξ0 : MemLp (xi γ 0) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous 0)
  have hrt : MemLp (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t) 2 γ.dominating :=
    memLp_qmdRem γ t
  have hsξ0 : MemLp (fun ω => (γ.score : Ω_full → ℝ) ω * xi γ 0 ω) 2 γ.dominating :=
    memLp_two_score_mul_sqrt_of_qmd (g := (γ.score : Ω_full → ℝ))
      γ.curve_isProbability γ.curve_absContinuous hscore_meas γ.qmd_limit
  -- Integrabilities for the conditional-expectation linearity of `r_t·ξ₀`.
  have hu_int : Integrable (fun ω => xi γ t ω * xi γ 0 ω) γ.dominating := hξt.integrable_mul hξ0
  have hw_int : Integrable (fun ω => xi γ 0 ω ^ 2) γ.dominating := hξ0.integrable_sq
  have hv_int : Integrable (fun ω => (γ.score : Ω_full → ℝ) ω * pbar γ 0 ω) γ.dominating := by
    refine (hsξ0.integrable_mul hξ0).congr (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [Pi.mul_apply]
    rw [← xi_sq γ 0 ω]; ring
  have hI2V : Integrable ((t / 2 : ℝ) • fun ω => (γ.score : Ω_full → ℝ) ω * pbar γ 0 ω)
      γ.dominating := Integrable.smul (t / 2 : ℝ) hv_int
  -- `r_t·ξ₀ = (ξ_t·ξ₀ − ξ₀²) − (t/2)·(s·p̄₀)` (using `ξ₀² = p̄₀`).
  have hfn : (fun ω => qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω * xi γ 0 ω)
      = ((fun ω => xi γ t ω * xi γ 0 ω) - fun ω => xi γ 0 ω ^ 2)
        - (t / 2 : ℝ) • fun ω => (γ.score : Ω_full → ℝ) ω * pbar γ 0 ω := by
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hrtω : qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω
        = xi γ t ω - xi γ 0 ω - t / 2 * ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω) := by
      simp only [qmdRem, xi_apply]; ring
    rw [hrtω, ← xi_sq γ 0 ω]; ring
  -- Conditional-expectation linearity pieces.
  have hsub := condExp_sub (hu_int.sub hw_int) hI2V
    (MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
  have hsub2 := condExp_sub hu_int hw_int (MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
  have hsmul := condExp_smul (μ := γ.dominating) (t / 2 : ℝ)
    (fun ω => (γ.score : Ω_full → ℝ) ω * pbar γ 0 ω)
    (MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
  have hB := coarsen_bayes_bridge hM γ
  -- **hEr** — `μ[r_t·ξ₀ | 𝒢] =ᵐ cross − q̃₀ − (t/2)(Π∘M)q̃₀` (via B + linearity).
  have hEr : γ.dominating[(fun ω => qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω
        * xi γ 0 ω) | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]
      =ᵐ[γ.dominating]
        fun ω => cross hM γ t ω - qtilde hM γ 0 ω
          - t / 2 * ((informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
              * qtilde hM γ 0 ω) := by
    rw [hfn]
    filter_upwards [hsub, hsub2, hsmul, hB] with ω ho hi hs hbω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ho hi hs
    rw [ho, hi, hs, hbω, congrFun (cross_apply hM γ t).symm ω,
      congrFun (condExp_xi_sq_eq_qtilde hM γ 0) ω]
  -- Conditional Cauchy--Schwarz with `f := r_t`, `g := ξ₀`.
  have hCS := AsymptoticStatistics.ForMathlib.CondExpCauchySchwarz.condExp_sq_le_condExp_mul_condExp
    (μ := γ.dominating) (m := MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
    hM.comap_le hrt hξ0
  have hrem_nn : 0 ≤ᵐ[γ.dominating]
      γ.dominating[(fun ω => qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω ^ 2)
        | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›] :=
    condExp_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
  -- **Step 2** — `bracket² ≤ μ[r_t² | 𝒢]` a.e.
  have hbracket_sq_le : (fun ω => (Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
        - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
            * Real.sqrt (qtilde hM γ 0 ω)) ^ 2)
      ≤ᵐ[γ.dominating]
        γ.dominating[(fun ω => qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω ^ 2)
          | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›] := by
    filter_upwards [hEr, hCS, hrem_nn, qtilde_nonneg hM γ 0] with ω hEr hCS hrem hq0nn
    rw [congrFun (condExp_xi_sq_eq_qtilde hM γ 0) ω] at hCS
    rcases eq_or_lt_of_le hq0nn with hQ0 | hQpos
    · -- On `{q̃₀ = 0}`: `A = 0`, `√q̃₀ = 0`, so the bracket vanishes.
      have hQz : qtilde hM γ 0 ω = 0 := hQ0.symm
      have hnpos : ¬ 0 < qtilde hM γ 0 ω := not_lt.mpr (le_of_eq hQz)
      have hbr : Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
          - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
            * Real.sqrt (qtilde hM γ 0 ω) = 0 := by
        rw [Acoef_of_zero hM γ t ω hnpos, hQz, Real.sqrt_zero]; ring
      rw [hbr]; simpa using hrem
    · -- On `{q̃₀ > 0}`: `bracket = μ[r_t·ξ₀|𝒢]/√q̃₀`, then conditional Cauchy–Schwarz.
      rw [Acoef_of_pos hM γ t ω hQpos]
      have hd : 0 < Real.sqrt (qtilde hM γ 0 ω) := Real.sqrt_pos.mpr hQpos
      have hCd : cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω) * Real.sqrt (qtilde hM γ 0 ω)
          = cross hM γ t ω := div_mul_cancel₀ (cross hM γ t ω) hd.ne'
      have hdd : Real.sqrt (qtilde hM γ 0 ω) * Real.sqrt (qtilde hM γ 0 ω) = qtilde hM γ 0 ω :=
        Real.mul_self_sqrt hq0nn
      have key : (cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω) - Real.sqrt (qtilde hM γ 0 ω)
            - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
              * Real.sqrt (qtilde hM γ 0 ω)) * Real.sqrt (qtilde hM γ 0 ω)
          = (γ.dominating[(fun ω => qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω
              * xi γ 0 ω) | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω := by
        rw [hEr]
        calc (cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω) - Real.sqrt (qtilde hM γ 0 ω)
              - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
                * Real.sqrt (qtilde hM γ 0 ω)) * Real.sqrt (qtilde hM γ 0 ω)
            = cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω) * Real.sqrt (qtilde hM γ 0 ω)
                - Real.sqrt (qtilde hM γ 0 ω) * Real.sqrt (qtilde hM γ 0 ω)
                - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
                  * (Real.sqrt (qtilde hM γ 0 ω) * Real.sqrt (qtilde hM γ 0 ω)) := by ring
          _ = cross hM γ t ω - qtilde hM γ 0 ω
                - t / 2 * ((informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
                  * qtilde hM γ 0 ω) := by rw [hCd, hdd]; ring
      refine le_of_mul_le_mul_right ?_ hQpos
      have hbe : (cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω) - Real.sqrt (qtilde hM γ 0 ω)
            - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
              * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 * qtilde hM γ 0 ω
          = (γ.dominating[(fun ω => qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω
              * xi γ 0 ω) | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]) ω ^ 2 := by
        rw [← key, mul_pow, Real.sq_sqrt hq0nn]
      rw [hbe]
      exact hCS
  -- **Step 3** — integrate: `∫ bracket²/t² ≤ ‖r_t‖₂²/t²`.
  have hInt_rt : ∫ ω, qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω ^ 2 ∂γ.dominating
      = ((eLpNorm (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t) 2
          γ.dominating).toReal) ^ 2 := by
    rw [← sqrt_integral_sq_eq_eLpNorm_toReal (memLp_qmdRem γ t),
      Real.sq_sqrt (integral_nonneg (fun ω => sq_nonneg _))]
  have h_num_le : ∫ ω, (Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
        - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
            * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 ∂γ.dominating
      ≤ ∫ ω, qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t ω ^ 2 ∂γ.dominating := by
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
      integrable_condExp hbracket_sq_le).trans_eq ?_
    exact integral_condExp hM.comap_le
  rw [integral_div, ← hInt_rt]
  exact (div_le_div_iff_of_pos_right ht2).mpr h_num_le

/-! ## Square-integrability of the residual -/

/-- `√q̃t ∈ L²(μ)`: `∫ (√q̃t)² = ∫ q̃t = ∫ p̄t = 1`. -/
private lemma memLp_sqrt_qtilde (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    MemLp (fun ω => Real.sqrt (qtilde hM γ t ω)) 2 γ.dominating := by
  have hqtA : AEMeasurable (qtilde hM γ t) γ.dominating :=
    integrable_condExp.aestronglyMeasurable.aemeasurable
  have haesm : AEStronglyMeasurable (fun ω => Real.sqrt (qtilde hM γ t ω)) γ.dominating :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable hqtA).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq haesm]
  have hqt_int : Integrable (qtilde hM γ t) γ.dominating := by
    rw [qtilde_apply hM]; exact integrable_condExp
  have hsq_eq : qtilde hM γ t =ᵐ[γ.dominating] fun ω => Real.sqrt (qtilde hM γ t ω) ^ 2 := by
    filter_upwards [qtilde_nonneg hM γ t] with ω hω
    exact (Real.sq_sqrt hω).symm
  exact hqt_int.congr hsq_eq

/-- `A t ∈ L²(μ)`: `A t² ≤ q̃t` almost everywhere and `q̃t` is integrable. -/
private lemma memLp_Acoef (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    MemLp (Acoef hM γ t) 2 γ.dominating := by
  have hq0A : AEMeasurable (qtilde hM γ 0) γ.dominating :=
    integrable_condExp.aestronglyMeasurable.aemeasurable
  have hcrA : AEMeasurable (cross hM γ t) γ.dominating :=
    integrable_condExp.aestronglyMeasurable.aemeasurable
  have hsq0 : AEMeasurable (fun ω => Real.sqrt (qtilde hM γ 0 ω)) γ.dominating :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hq0A
  have hAae : Acoef hM γ t =ᵐ[γ.dominating]
      fun ω => cross hM γ t ω / Real.sqrt (qtilde hM γ 0 ω) := by
    filter_upwards [qtilde_nonneg hM γ 0] with ω hq0nn
    by_cases hpos : 0 < qtilde hM γ 0 ω
    · rw [Acoef_of_pos hM γ t ω hpos]
    · have hz : qtilde hM γ 0 ω = 0 := le_antisymm (not_lt.mp hpos) hq0nn
      rw [Acoef_of_zero hM γ t ω hpos, hz, Real.sqrt_zero, div_zero]
  have hAA : AEMeasurable (Acoef hM γ t) γ.dominating := (hcrA.div hsq0).congr hAae.symm
  have haesm : AEStronglyMeasurable (Acoef hM γ t) γ.dominating := hAA.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq haesm]
  have hqt_int : Integrable (qtilde hM γ t) γ.dominating := by
    rw [qtilde_apply hM]; exact integrable_condExp
  refine hqt_int.mono' ((hAA.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [A_sq_le hM γ t] with ω hle
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hle

/-- `(Π∘M)·√q̃0 ∈ L²(μ)`: `((Π∘M)√q̃0)² ≤ Cdom` a.e. (Bayes bridge + conditional
Cauchy–Schwarz), and `Cdom` is integrable. -/
private lemma memLp_PiM_sqrt_qtilde0 (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] :
    MemLp (fun ω => (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
        * Real.sqrt (qtilde hM γ 0 ω)) 2 γ.dominating := by
  haveI hp0 : IsProbabilityMeasure (γ.curve 0) := γ.curve_isProbability 0
  haveI hσμ : SigmaFinite (γ.dominating.trim hM.comap_le) :=
    AsymptoticStatistics.ForMathlib.SigmaFiniteTrimComap.sigmaFinite_trim_comap_of_sigmaFinite_map
      γ.dominating hM
  have hscore_meas : Measurable (γ.score : Ω_full → ℝ) :=
    (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P_full)).measurable
  have hξ0 : MemLp (xi γ 0) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (γ.curve_absContinuous 0)
  have hsξ0 : MemLp (fun ω => (γ.score : Ω_full → ℝ) ω * xi γ 0 ω) 2 γ.dominating :=
    memLp_two_score_mul_sqrt_of_qmd (g := (γ.score : Ω_full → ℝ))
      γ.curve_isProbability γ.curve_absContinuous hscore_meas γ.qmd_limit
  have hPiM_sm : StronglyMeasurable
      (fun ω => (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)) :=
    (Lp.stronglyMeasurable
        (↑(informationLossOperator hM P_full γ.score) : Lp ℝ 2 (P_full.map M))).comp_measurable hM
  have hq0A : AEMeasurable (qtilde hM γ 0) γ.dominating :=
    integrable_condExp.aestronglyMeasurable.aemeasurable
  have hsq0 : AEStronglyMeasurable (fun ω => Real.sqrt (qtilde hM γ 0 ω)) γ.dominating :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable hq0A).aestronglyMeasurable
  have haesm : AEStronglyMeasurable (fun ω =>
      (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
        * Real.sqrt (qtilde hM γ 0 ω)) γ.dominating :=
    hPiM_sm.aestronglyMeasurable.mul hsq0
  rw [memLp_two_iff_integrable_sq haesm]
  have hCd_int : Integrable (Cdom hM γ) γ.dominating := by
    rw [Cdom_apply hM]; exact integrable_condExp
  have hCd_nn : 0 ≤ᵐ[γ.dominating] Cdom hM γ := by
    rw [Cdom_apply hM]
    exact condExp_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
  -- Conditional Cauchy–Schwarz with `f := s·ξ0`, `g := ξ0`.
  have hCS := AsymptoticStatistics.ForMathlib.CondExpCauchySchwarz.condExp_sq_le_condExp_mul_condExp
    (μ := γ.dominating) (m := MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›)
    hM.comap_le hsξ0 hξ0
  have hfg_eq : (fun ω => ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω) * xi γ 0 ω)
      = (fun ω => (γ.score : Ω_full → ℝ) ω * pbar γ 0 ω) := by
    funext ω; rw [← xi_sq γ 0 ω]; ring
  have hEq : γ.dominating[(fun ω => ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω) * xi γ 0 ω)
        | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]
      =ᵐ[γ.dominating] fun ω =>
        (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω) * qtilde hM γ 0 ω := by
    have h1 : γ.dominating[(fun ω => ((γ.score : Ω_full → ℝ) ω * xi γ 0 ω) * xi γ 0 ω)
          | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›]
        = γ.dominating[(fun ω => (γ.score : Ω_full → ℝ) ω * pbar γ 0 ω)
          | MeasurableSpace.comap M ‹MeasurableSpace Ω_obs›] := by rw [hfg_eq]
    rw [h1]; exact coarsen_bayes_bridge hM γ
  -- `((Π∘M)√q̃0)² ≤ Cdom` a.e.
  have hsq_le : ∀ᵐ ω ∂γ.dominating,
      ((informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
        * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 ≤ Cdom hM γ ω := by
    filter_upwards [hCS, hEq, hCd_nn, qtilde_nonneg hM γ 0] with ω hCSω hEqω hcd hq0nn
    rw [hEqω, ← congrFun (Cdom_apply hM γ) ω,
      congrFun (condExp_xi_sq_eq_qtilde hM γ 0) ω] at hCSω
    by_cases hpos : 0 < qtilde hM γ 0 ω
    · have hsq : Real.sqrt (qtilde hM γ 0 ω) ^ 2 = qtilde hM γ 0 ω := Real.sq_sqrt hq0nn
      rw [mul_pow, hsq]
      refine le_of_mul_le_mul_right ?_ hpos
      calc (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω) ^ 2
            * qtilde hM γ 0 ω * qtilde hM γ 0 ω
          = ((informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
              * qtilde hM γ 0 ω) ^ 2 := by ring
        _ ≤ Cdom hM γ ω * qtilde hM γ 0 ω := hCSω
    · have hz : qtilde hM γ 0 ω = 0 := le_antisymm (not_lt.mp hpos) hq0nn
      rw [hz, Real.sqrt_zero, mul_zero]
      simpa using hcd
  have hInt : Integrable (fun ω =>
      ((informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
        * Real.sqrt (qtilde hM γ 0 ω)) ^ 2) γ.dominating := by
    refine hCd_int.mono' ((haesm.aemeasurable.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [hsq_le] with ω hle
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hle
  exact hInt

/-- The pulled-back residual `√q̃t − √q̃0 − (t/2)(Π∘M)√q̃0` belongs to
`L²(μ)`. -/
private lemma memLp_residual (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] (t : ℝ) :
    MemLp (fun ω => Real.sqrt (qtilde hM γ t ω) - Real.sqrt (qtilde hM γ 0 ω)
        - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
            * Real.sqrt (qtilde hM γ 0 ω)) 2 γ.dominating := by
  have hfun : (fun ω => Real.sqrt (qtilde hM γ t ω) - Real.sqrt (qtilde hM γ 0 ω)
        - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
            * Real.sqrt (qtilde hM γ 0 ω))
      = (fun ω => Real.sqrt (qtilde hM γ t ω)) - (fun ω => Real.sqrt (qtilde hM γ 0 ω))
        - (fun ω => t / 2 * ((informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
            * Real.sqrt (qtilde hM γ 0 ω))) := by
    funext ω; simp only [Pi.sub_apply]; ring
  rw [hfun]
  exact ((memLp_sqrt_qtilde hM γ t).sub (memLp_sqrt_qtilde hM γ 0)).sub
    ((memLp_PiM_sqrt_qtilde0 hM γ).const_mul (t / 2))

/-- The pulled-back residual satisfies `∫ RES²/t² dμ → 0`, where
`RES t = √q̃t − √q̃0 − (t/2)(Π∘M)√q̃0`. -/
theorem residual_sq_over_t_tendsto (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] :
    Tendsto (fun t => ∫ ω, (Real.sqrt (qtilde hM γ t ω) - Real.sqrt (qtilde hM γ 0 ω)
        - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
            * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 / t ^ 2 ∂γ.dominating)
      (𝓝[≠] 0) (𝓝 0) := by
  -- The second bracket `∫ (√q̃t − A)²/t²` tends to zero by the integral
  -- bound and the two preceding limit estimates.
  have hsecond : Tendsto (fun t => ∫ ω,
      (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2 ∂γ.dominating)
      (𝓝[≠] 0) (𝓝 0) := by
    have hup : Tendsto (fun t => 1 / 2 * ∫ ω, Cdom hM γ ω * rho hM γ t ω ∂γ.dominating
        + 2 * (eLpNorm (qmdRem γ.curve γ.dominating (γ.score : Ω_full → ℝ) t) 2
            γ.dominating).toReal ^ 2 / t ^ 2) (𝓝[≠] 0) (𝓝 0) := by
      have h := (first_term_tendsto hM γ).add (second_term_tendsto γ)
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Filter.Eventually.of_forall (fun t =>
        integral_nonneg (fun ω => div_nonneg (sq_nonneg _) (sq_nonneg _)))) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact integral_second_bracket_bound hM γ t ht
  have hfirst := first_bracket_tendsto hM γ
  -- Upper envelope `2∫first²/t² + 2∫second²/t² → 0`.
  have hup : Tendsto (fun t =>
      2 * (∫ ω, (Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
          - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
              * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 / t ^ 2 ∂γ.dominating)
      + 2 * (∫ ω, (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2 ∂γ.dominating))
      (𝓝[≠] 0) (𝓝 0) := by
    have h := (hfirst.const_mul 2).add (hsecond.const_mul 2)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Filter.Eventually.of_forall (fun t =>
      integral_nonneg (fun ω => div_nonneg (sq_nonneg _) (sq_nonneg _)))) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htne : t ≠ 0 := ht
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  -- L² memberships of the two brackets and the residual.
  have hfirst_mem : MemLp (fun ω => Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
      - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
          * Real.sqrt (qtilde hM γ 0 ω)) 2 γ.dominating := by
    have hfun : (fun ω => Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
          - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
              * Real.sqrt (qtilde hM γ 0 ω))
        = (Acoef hM γ t) - (fun ω => Real.sqrt (qtilde hM γ 0 ω))
          - (fun ω => t / 2 * ((informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
              * Real.sqrt (qtilde hM γ 0 ω))) := by
      funext ω; simp only [Pi.sub_apply]; ring
    rw [hfun]
    exact ((memLp_Acoef hM γ t).sub (memLp_sqrt_qtilde hM γ 0)).sub
      ((memLp_PiM_sqrt_qtilde0 hM γ).const_mul (t / 2))
  have hsecond_mem : MemLp (fun ω => Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) 2 γ.dominating :=
    (memLp_sqrt_qtilde hM γ t).sub (memLp_Acoef hM γ t)
  have hR_int : Integrable (fun ω => (Real.sqrt (qtilde hM γ t ω) - Real.sqrt (qtilde hM γ 0 ω)
      - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
          * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 / t ^ 2) γ.dominating :=
    (memLp_residual hM γ t).integrable_sq.div_const _
  have hf_int : Integrable (fun ω => (Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
      - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
          * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 / t ^ 2) γ.dominating :=
    hfirst_mem.integrable_sq.div_const _
  have hs_int : Integrable (fun ω => (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2)
      γ.dominating := hsecond_mem.integrable_sq.div_const _
  have hsum_int : Integrable (fun ω =>
      2 * ((Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
          - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
              * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 / t ^ 2)
      + 2 * ((Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2)) γ.dominating :=
    (hf_int.const_mul 2).add (hs_int.const_mul 2)
  -- Pointwise `RES²/t² ≤ 2·first²/t² + 2·second²/t²` (`(a+b)² ≤ 2a²+2b²`).
  have hpt : (fun ω => (Real.sqrt (qtilde hM γ t ω) - Real.sqrt (qtilde hM γ 0 ω)
        - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
            * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 / t ^ 2)
      ≤ᵐ[γ.dominating] fun ω =>
        2 * ((Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
            - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
                * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 / t ^ 2)
        + 2 * ((Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2) := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    beta_reduce
    rw [show 2 * ((Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
          - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
              * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 / t ^ 2)
        + 2 * ((Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2)
        = (2 * (Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
            - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
                * Real.sqrt (qtilde hM γ 0 ω)) ^ 2
          + 2 * (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2) / t ^ 2 from by ring]
    refine (div_le_div_iff_of_pos_right ht2).mpr ?_
    nlinarith [sq_nonneg ((Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
      - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
          * Real.sqrt (qtilde hM γ 0 ω)) - (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω))]
  calc ∫ ω, (Real.sqrt (qtilde hM γ t ω) - Real.sqrt (qtilde hM γ 0 ω)
          - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
              * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 / t ^ 2 ∂γ.dominating
      ≤ ∫ ω, (2 * ((Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
            - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
                * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 / t ^ 2)
          + 2 * ((Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2)) ∂γ.dominating :=
        integral_mono_ae hR_int hsum_int hpt
    _ = 2 * (∫ ω, (Acoef hM γ t ω - Real.sqrt (qtilde hM γ 0 ω)
          - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
              * Real.sqrt (qtilde hM γ 0 ω)) ^ 2 / t ^ 2 ∂γ.dominating)
        + 2 * (∫ ω, (Real.sqrt (qtilde hM γ t ω) - Acoef hM γ t ω) ^ 2 / t ^ 2 ∂γ.dominating) := by
      rw [integral_add (hf_int.const_mul 2) (hs_int.const_mul 2), integral_const_mul,
        integral_const_mul]

/-- The coarsened `qmd_limit` property under an explicit mapped
sigma-finiteness assumption. -/
theorem coarsen_qmd_limit_withMappedSigmaFinite (hM : Measurable M) (γ : QMDPath P_full)
    [SigmaFinite (γ.dominating.map M)] :
    Tendsto
      (fun t : ℝ =>
        eLpNorm (fun y : Ω_obs =>
          Real.sqrt (((γ.curve t).map M).rnDeriv (γ.dominating.map M) y).toReal
            - Real.sqrt (((γ.curve 0).map M).rnDeriv (γ.dominating.map M) y).toReal
            - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) y
                * Real.sqrt (((γ.curve 0).map M).rnDeriv (γ.dominating.map M) y).toReal)
          2 (γ.dominating.map M) / ENNReal.ofReal |t|)
      (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞)) := by
  -- Repackage each `eLpNorm` over `μ.map M` as an `eLpNorm` over `μ` of the residual.
  have hkey : ∀ t : ℝ, eLpNorm (fun y : Ω_obs =>
        Real.sqrt (((γ.curve t).map M).rnDeriv (γ.dominating.map M) y).toReal
          - Real.sqrt (((γ.curve 0).map M).rnDeriv (γ.dominating.map M) y).toReal
          - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) y
              * Real.sqrt (((γ.curve 0).map M).rnDeriv (γ.dominating.map M) y).toReal)
        2 (γ.dominating.map M)
      = eLpNorm (fun ω => Real.sqrt (qtilde hM γ t ω) - Real.sqrt (qtilde hM γ 0 ω)
          - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
              * Real.sqrt (qtilde hM γ 0 ω)) 2 γ.dominating := by
    intro t
    have hFsm : StronglyMeasurable (fun y : Ω_obs =>
        Real.sqrt (((γ.curve t).map M).rnDeriv (γ.dominating.map M) y).toReal
          - Real.sqrt (((γ.curve 0).map M).rnDeriv (γ.dominating.map M) y).toReal
          - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) y
              * Real.sqrt (((γ.curve 0).map M).rnDeriv (γ.dominating.map M) y).toReal) := by
      have hrt : Measurable (fun y : Ω_obs =>
          Real.sqrt (((γ.curve t).map M).rnDeriv (γ.dominating.map M) y).toReal) :=
        Real.continuous_sqrt.measurable.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal
      have hr0 : Measurable (fun y : Ω_obs =>
          Real.sqrt (((γ.curve 0).map M).rnDeriv (γ.dominating.map M) y).toReal) :=
        Real.continuous_sqrt.measurable.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal
      have hPi : StronglyMeasurable (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) :=
        Lp.stronglyMeasurable _
      exact (hrt.stronglyMeasurable.sub hr0.stronglyMeasurable).sub
        ((stronglyMeasurable_const.mul hPi).mul hr0.stronglyMeasurable)
    rw [eLpNorm_map_measure hFsm.aestronglyMeasurable hM.aemeasurable]
    refine eLpNorm_congr_ae ?_
    filter_upwards [coarsen_density_transport hM γ t, coarsen_density_transport hM γ 0]
      with ω h1 h0
    simp only [Function.comp_apply]
    rw [h1, h0]
  -- The required `.toReal²/t² → 0` limit follows from the squared-residual
  -- estimate via `√(∫RES²) = ‖RES‖₂`.
  have hsq' : Tendsto (fun t => (eLpNorm (fun ω => Real.sqrt (qtilde hM γ t ω)
        - Real.sqrt (qtilde hM γ 0 ω)
        - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) (M ω)
            * Real.sqrt (qtilde hM γ 0 ω)) 2 γ.dominating).toReal ^ 2 / t ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
    refine (residual_sq_over_t_tendsto hM γ).congr (fun t => ?_)
    rw [integral_div]
    congr 1
    rw [← sqrt_integral_sq_eq_eLpNorm_toReal (memLp_residual hM γ t),
      Real.sq_sqrt (integral_nonneg (fun ω => sq_nonneg _))]
  have hT0 := AsymptoticStatistics.L2Utils.tendsto_eLpNorm_div_ofReal_of_toReal_sq
    (Filter.Eventually.of_forall (fun t => memLp_residual hM γ t)) hsq'
  exact hT0.congr (fun t => by rw [hkey t])

/-- **Score preservation for vdV Lemma 25.34-I.**

The coarsened curve has score `informationLossOperator hM P_full γ.score`, with
the QMD residual computed against the pushforward of the equivalent finite
dominating measure. Finiteness, and hence sigma-finiteness after mapping,
follows from `finiteDominatorRepresentation`; no
`[SigmaFinite (γ.dominating.map M)]` assumption is required. -/
theorem coarsen_qmd_limit (hM : Measurable M) (γ : QMDPath P_full) :
    Tendsto
      (fun t : ℝ =>
        eLpNorm (fun y : Ω_obs =>
          Real.sqrt (((γ.curve t).map M).rnDeriv (γ.dominating.toFinite.map M) y).toReal
            - Real.sqrt
                (((γ.curve 0).map M).rnDeriv (γ.dominating.toFinite.map M) y).toReal
            - t / 2 * (informationLossOperator hM P_full γ.score : Ω_obs → ℝ) y
                * Real.sqrt
                  (((γ.curve 0).map M).rnDeriv (γ.dominating.toFinite.map M) y).toReal)
          2 (γ.dominating.toFinite.map M) / ENNReal.ofReal |t|)
      (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞)) := by
  let γ' := (finiteDominatorRepresentation γ).1
  have hcurve : γ'.curve = γ.curve := (finiteDominatorRepresentation γ).2.1
  have hdom : γ'.dominating = γ.dominating.toFinite :=
    (finiteDominatorRepresentation γ).2.2.1
  have hscore : γ'.score = γ.score := (finiteDominatorRepresentation γ).2.2.2
  haveI : SigmaFinite (γ'.dominating.map M) := by
    rw [hdom]
    infer_instance
  simpa only [hcurve, hdom, hscore] using coarsen_qmd_limit_withMappedSigmaFinite hM γ'

end Coarsen

end AsymptoticStatistics.Core.QMDPath
